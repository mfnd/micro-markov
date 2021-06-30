import re
import sys
from formula import *
from dtmc import DTMC
from ctmc import CTMC


rules = [
    ("SKIP", "\s+"),
    ("NUM", "\d+(.\d+)?"),
    ("MOD_TYPE", "dtmc|ctmc"),
    ("BEGIN", "begin"),
    ("END", "end"),
    ("SPEC", "spec"),
    ("TRUE", "true"),
    ("LPAR", "\("),
    ("RPAR", "\)"),
    ("PROB", "P"),
    ("STEADY", "S"),
    ("NEXT", "X"),
    ("EQUALS", "="),
    ("QUESTION", "\?"),
    ("TB_UNTIL", "U'"),
    ("UNTIL", "U"),
    ("AND", "&"),
    ("NOT", "~"),
    ("CMP", ">|<"),
    ("TRANS", "->"),
    ("COMMA", ","),
    ("SEMICOLON", ";"),
    ("COLON", ":"),
    ("LBRACK", "\["),
    ("RBRACK", "\]"),
    ("LCURLY", "{"),
    ("RCURLY", "}"),
    ("IDENT", "[a-z]\w*"),
]

T_SKIP, T_NUM, T_MOD_TYPE, T_BEGIN, T_END, T_SPEC, T_TRUE, T_LPAR, T_RPAR, T_PROB, T_STEADY, T_NEXT, T_EQUALS, T_QUESTION, \
  T_TB_UNTIL, T_UNTIL, T_AND, T_NOT, T_CMP, T_TRANS, T_COMMA, T_SEMICOLON, T_COLON, T_LBRACK, T_RBRACK, \
  T_LCURLY, T_RCURLY, T_IDENT, = range(len(rules))

rule_ids = { rule_name : i for i, (rule_name, rule_regex) in enumerate(rules)}

regex_string = "|".join([ "(?P<%s>%s)" % (token_type, token_regex) for token_type, token_regex in rules])
lexer_re = re.compile(regex_string)

def lex(formula):
    token_list = []
    pos = 0
    while pos < len(formula):
        m = lexer_re.match(formula, pos)
        if m is not None:
            if m.lastgroup == "SKIP":
                pos = m.end()
                continue
            rule_id = rule_ids[m.lastgroup]
            pos = m.end()
            token_list.append((rule_id, m.group(m.lastgroup)))
        else:
            raise Exception("None matched")
    return token_list


class Parser(object):

    def __init__(self, formula):
        self.tokens = lex(formula)
        self.pos = 0

    def parse(self):
        node = self.parse_module()
        #node.dump()
        return node

    def parse_module(self):
        save = self.pos

        module_type = self.parse_token(T_MOD_TYPE)
        if not module_type:
            return None

        print("MODULE TYPE: %s" % module_type)


        states = self.parse_state_set()
        if not states:
            return None

        print("STATES: %s" % states)

        if not self.check_token(T_BEGIN):
            return None

        transitions = self.parse_transition_set()
        if not transitions:
            return None

        print("TRANSITIONS: %s" % transitions)

        specs = self.parse_spec_set()
        if not specs:
            return None

        #print("Specs %s" % specs)

        if not self.check_token(T_END):
            return None

        if module_type == "dtmc":
            return DTMC.create(states, transitions, specs)
        elif module_type == "ctmc":
            return CTMC.create(states, transitions ,specs)
        else:
            print("Invalid Module Type: %s" % module_type)
            sys.exit(1)

    def parse_state_set(self):
        save = self.pos
        state = self.parse_state_def()
        if not state:
            return None
        save = self.pos
        if self.check_token(T_COMMA):
            state_set = self.parse_state_set()
            if state_set:
                state_set[state[0]] = state[1]
                return state_set
            else:
                return None
        self.pos = save
        return {state[0] : state[1]}

    def parse_state_def(self):
        state_name = self.parse_token(T_IDENT)
        if not state_name:
            return None
        save = self.pos
        if self.check_token(T_COLON) and self.check_token(T_LCURLY):
            atomic_props = self.parse_atomic_props()
            if atomic_props is not None and self.check_token(T_RCURLY):
                return (state_name, atomic_props)
            else:
                return None
        self.pos = save
        return (state_name, set())

    def parse_atomic_props(self):
        save = self.pos
        atomic_prop = self.parse_token(T_IDENT)
        if not atomic_prop:
            return None
        save = self.pos
        if self.parse_token(T_COMMA):
            atomic_props = self.parse_atomic_props()
            if not atomic_props:
                return None
            else:
                atomic_props.add(atomic_prop)
                return atomic_props
        else:
            self.pos = save
            return set([atomic_prop])



    def parse_transition_set(self):
        transition = self.parse_transition()
        if not transition or not self.check_token(T_SEMICOLON):
            return None
        save = self.pos
        transition_set = self.parse_transition_set()
        if transition_set:
            transition_set[transition[0]] = transition[1]
            return transition_set
        else:
            self.pos = save
            return { transition[0] : transition[1] }

    def parse_transition(self):
        save = self.pos
        state_name = self.parse_token(T_IDENT)
        if not state_name or not self.check_token(T_TRANS):
            return None

        trans_probs = self.parse_transition_probs()
        if not trans_probs:
            return None

        return (state_name, trans_probs)

    def parse_transition_probs(self):
        save = self.pos
        next_state = self.parse_token(T_IDENT)
        if next_state:
            return [(next_state, 1.0)]
        self.pos = save
        if not self.check_token(T_LCURLY):
            return None
        trans_prob_list = self.parse_transition_prob_list()
        if not trans_prob_list or not self.check_token(T_RCURLY):
            return None
        return trans_prob_list

    def parse_transition_prob_list(self):
        save = self.pos
        state_name = self.parse_token(T_IDENT)
        if not self.check_token(T_COLON):
            return None
        probability = self.parse_token(T_NUM)
        if not probability:
            return None
        probability = float(probability)
        #if probability > 1 or probability < 0:
        #    raise Exception("Probability should be in [0, 1]")
        save = self.pos
        if self.check_token(T_COMMA):
            trans_prob_list = self.parse_transition_prob_list()
            if trans_prob_list:
                trans_prob_list.append((state_name, probability))
                return trans_prob_list
            else:
                return None
        self.pos = save
        return [(state_name, probability)]


    def parse_spec_set(self):
        save = self.pos
        spec = self.parse_spec()
        if not spec:
            return None
        save = self.pos
        spec_set = self.parse_spec_set()
        if spec_set:
            spec_set[spec[0]] = spec[1]
            return spec_set
        else:
            self.pos = save
            return { spec[0] : spec[1] }

    def parse_spec(self):
        save = self.pos
        if not self.check_token(T_SPEC):
            return None

        spec_name = self.parse_token(T_IDENT)
        if not spec_name:
            return None

        if not self.check_token(T_COLON):
            return None
        save = self.pos
        prob_formula = self.parse_prob_formula()
        if prob_formula and self.parse_token(T_SEMICOLON):
            return spec_name, prob_formula

        self.pos = save
        formula = self.parse_state_formula_conj()
        if not formula:
            return None

        if not self.parse_token(T_SEMICOLON):
            return None

        return spec_name, formula

    def parse_state_formula_conj(self):
        save = self.pos
        state_formula = self.parse_state_formula()
        if state_formula:
            save = self.pos
            if self.check_token(T_AND):
                state_formula_conj = self.parse_state_formula_conj()
                if state_formula_conj:
                    state_formula_conj.prepend_formula(state_formula)
                    return state_formula_conj
                else:
                    raise Exception("Invalid &")
            else:
                self.pos = save
                return ConjunctionNode(state_formula)
        else:
            return None

    def parse_state_formula(self):
        save = self.pos
        if self.check_token(T_TRUE):
            return APNode("T")
        self.pos = save
        ap_name = self.parse_token(T_IDENT)
        if ap_name:
            return APNode(ap_name)
        self.pos = save
        if self.check_token(T_NOT):
            state_formula = self.parse_state_formula()
            if state_formula:
                return NegationNode(state_formula)
        self.pos = save
        if self.check_token(T_LPAR):
            state_formula_conj = self.parse_state_formula_conj()
            if state_formula_conj and self.check_token(T_RPAR):
                return state_formula_conj
        self.pos = save
        if self.check_token(T_PROB) and self.check_token(T_LPAR):
            path_node = self.parse_path_formula()
            if path_node and self.check_token(T_RPAR):
                cmp_op = self.parse_token(T_CMP)
                probability = self.parse_token(T_NUM)
                if cmp_op and probability:
                    return ProbabilityNode(path_node, cmp_op, probability)
        self.pos = save
        if self.check_token(T_STEADY) and self.check_token(T_LPAR):
            state_node = self.parse_state_formula()
            if state_node and self.check_token(T_RPAR):
                cmp_op = self.parse_token(T_CMP)
                probability = self.parse_token(T_NUM)
                if cmp_op and probability:
                    return SteadyStateNode(state_node, cmp_op, probability)

        return None


    def parse_path_formula(self):
        save = self.pos
        if self.check_token(T_NEXT):
            state_formula = self.parse_state_formula()
            if state_formula:
                return CTLNextNode(state_formula)
        left_conj = self.parse_state_formula_conj()
        if not left_conj:
            return None
        save = self.pos
        if self.parse_token(T_UNTIL):
            step_count = self.parse_step_count()
            right_conj = self.parse_state_formula_conj()
            if right_conj:
                return CTLUntilNode(left_conj, right_conj, step_count)
        self.pos = save
        if self.parse_token(T_TB_UNTIL):
            #interval = self.parse_interval()
            duration = self.parse_step_count()
            right_conj = self.parse_state_formula_conj()
            if right_conj:
                return CSLUntilNode(left_conj, right_conj, duration)

        return None

    def parse_prob_formula(self):
        save = self.pos
        if self.check_token(T_PROB) and self.check_token(T_LPAR):
            path_node = self.parse_path_formula()
            if path_node and self.check_token(T_RPAR):
                if self.check_token(T_EQUALS) and self.check_token(T_QUESTION):
                    return ProbabilityNode(path_node, "=", 0)
        self.pos = save
        if self.check_token(T_STEADY) and self.check_token(T_LPAR):
            state_node = self.parse_state_formula()
            if state_node and self.check_token(T_RPAR):
                if self.check_token(T_EQUALS) and self.check_token(T_QUESTION):
                    return SteadyStateNode(state_node, "=", 0)

        return None

    def parse_step_count(self):
        save = self.pos
        if self.check_token(T_LBRACK):
            step_count = self.parse_token(T_NUM)
            if step_count and self.check_token(T_RBRACK):
                return step_count
        self.pos = save
        return None

    def parse_interval(self):
        save = self.pos
        if self.check_token(T_LBRACK):
            start = self.parse_token(T_NUM)
            comma = self.check_token(T_COMMA)
            end = self.parse_token(T_NUM)
            if start and comma and end and self.check_token(T_RBRACK):
                return (float(start), float(end))
        self.pos = save
        return None

    def parse_token(self, token_id):
        if self.pos >= len(self.tokens):
            return None
        token = self.tokens[self.pos]
        if token[0] == token_id:
            self.pos += 1
            return token[1]
        return None

    def check_token(self, token_id):
        if self.pos >= len(self.tokens):
            return None
        token = self.tokens[self.pos]
        if token[0] == token_id:
            self.pos += 1
            return True
        return None

