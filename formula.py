import numpy as np
import numpy.linalg as linalg

# Decorators which checks whether the subformula is already checked or not
def satisfied_check(method_ref):
    def satisfied_checked_method(self, dtmc):
        if self in dtmc.sat_sets:
            return dtmc.sat_sets[self]
        return method_ref(self, dtmc)
    return satisfied_checked_method

def sat_computed_check(method_ref):
    def sat_computed_checked_method(self, dtmc):
        if self in dtmc.sat_vectors:
            return dtmc.sat_vectors[self]
        return method_ref(self, dtmc)
    return sat_computed_checked_method


class StateFormulaNode(object):

    @sat_computed_check
    def sat_vector(self, dtmc):
        sat_vector = np.zeros(dtmc.size)
        for sat_state in self.satisfy(dtmc):
            sat_vector[sat_state] = 1
        dtmc.sat_vectors[self] = sat_vector
        return sat_vector


class NegationNode(StateFormulaNode):

    def __init__(self, state_formula):
        self.state_formula = state_formula

    @satisfied_check
    def satisfy(self, dtmc):
        formula_sat_set = self.state_formula.satisfy(dtmc)
        negation_set = dtmc.all_states - formula_sat_set
        dtmc.sat_sets[self] = negation_set
        return negation_set

    def dump(self, indent=0):
        print(indent * " " + "Negation")
        print(indent * " " + "|")
        self.state_formula.dump(indent+1)

    def __str__(self):
        return "~" + str(self.state_formula)

class APNode(StateFormulaNode):

    def __init__(self, name):
        self.name = name

    @satisfied_check
    def satisfy(self, dtmc):
        if self.name == "T":
            return    dtmc.all_states
        sat_set = set()
        for state, atomic_props in enumerate(dtmc.propositions):
            if self.name in atomic_props:
                sat_set.add(state)
        dtmc.sat_sets[self] = sat_set
        return sat_set

    def dump(self, indent=0):
        print(indent * " " + "APNode(%s)" % self.name)

    def __str__(self):
        return self.name

class ProbabilityNode(StateFormulaNode):

    def __init__(self, path_formula, operator, probability):
        self.path_formula = path_formula
        self.operator = operator
        self.probability = float(probability)

    @satisfied_check
    def satisfy(self, dtmc):
        sat_probs = self.path_formula.probability(dtmc)
        if self.operator != "=":
            if self.operator == ">":
                sat_states = sat_probs > self.probability
            elif self.operator == "<":
                sat_states = sat_probs < self.probability
            sat_set = set([state for state, in_set in enumerate(sat_states) if in_set])
            dtmc.sat_sets[self] = sat_set
            return sat_set
        else:
            sat_dict = {state: prob for state, prob in enumerate(sat_probs)}
            return sat_dict


    def dump(self, indent=0):
        print(indent * " " + "Pr %s %f" % (self.operator, self.probability))
        print(indent * " " + "|")
        self.path_formula.dump(indent+1)

    def __str__(self):
        return "Pr{ %s } %s %s" % (str(self.path_formula), self.operator, str(self.probability))

class SteadyStateNode(StateFormulaNode):
    def __init__(self, state_formula, operator, probability):
        self.state_formula = state_formula
        self.operator = operator
        self.probability = float(probability)

    def satisfy(self, ctmc):
        sat = self.state_formula.satisfy(ctmc)
        sat_probs = ctmc.steady_probs[:, list(sat)]
        sat_probs = np.sum(sat_probs, axis=1)
        if self.operator != "=":
            if self.operator == ">":
                sat_states = sat_probs > self.probability
            elif self.operator == "<":
                sat_states = sat_probs < self.probability
            sat_set = set([state for state, in_set in enumerate(sat_states) if in_set])
            return sat_set
        sat_dict = { state: prob for state, prob in enumerate(sat_probs) }
        return sat_dict

    def dump(self, indent=0):
        print(indent * " " + "Steady %s %f" % (self.operator, self.probability))
        print(indent * " " + "|")
        self.state_formula.dump(indent+1)

    def __str__(self):
        return "S{ %s } %s %s" % (str(self.state_formula), self.operator, str(self.probability))


class ConjunctionNode(StateFormulaNode):

    def __init__(self, first_term):
        self.conjunction = [ first_term ]

    def prepend_formula(self, state_formula):
        self.conjunction.insert(0,state_formula)

    def satisfy(self,dtmc):
        term_iter = iter(self.conjunction)
        sat_set = next(term_iter).satisfy(dtmc)
        for term in term_iter:
            sat_set &= term.satisfy(dtmc)
        dtmc.sat_sets[self] = sat_set
        return sat_set

    def dump(self, indent=0):
        print(indent * " " + "Conjunction")
        print(indent * " " + "|")
        for term in self.conjunction:
            term.dump(indent+1)

    def __str__(self):
        if len(self.conjunction) == 0:
            return "EMPTY"
        text = str(self.conjunction[0])
        for i in range(1, len(self.conjunction)):
            text += " & %s" % str(self.conjunction[i])

class CTLNextNode(object):

    def __init__(self, state_formula):
        self.state_formula = state_formula

    #@calculated_check
    def probability(self, dtmc):
        sat_vector = self.state_formula.sat_vector(dtmc)
        return dtmc.transitions @ sat_vector

    def dump(self, indent=0):
        print(indent * " " + "Next")
        print(indent * " " + "|")
        self.state_formula.dump(indent+1)

    def __str__(self):
        return "X %s" % str(self.state_formula)

class CTLUntilNode(object):

    def __init__(self, left_conj, right_conj, step_count):
        self.left_conj = left_conj
        self.right_conj = right_conj
        if step_count is not None:
            self.step_count = int(step_count)
        else:
            self.step_count = -1

    def probability(self, dtmc):
        if self.step_count > 0:
            left_sat = self.left_conj.satisfy(dtmc)
            right_sat = self.right_conj.satisfy(dtmc)
            mod_trans_mat = dtmc.transitions.copy()
            unsat = (dtmc.all_states - left_sat) - right_sat
            for unsat_state in unsat:
                mod_trans_mat[unsat_state] = 0
                mod_trans_mat[unsat_state][unsat_state] = 1
            for sat_state in right_sat:
                mod_trans_mat[sat_state] = 0
                mod_trans_mat[sat_state][sat_state] = 1
            right_sat_vec = self.right_conj.sat_vector(dtmc)
            mat_power = linalg.matrix_power(mod_trans_mat, self.step_count)
            probabilities = mat_power @ right_sat_vec
            return probabilities
        else:
            left_sat = self.left_conj.satisfy(dtmc)
            right_sat = self.right_conj.satisfy(dtmc)
            mod_trans_mat = dtmc.transitions.copy()

            W = left_sat
            X = dtmc.all_states
            Y = right_sat
            while X != Y:
                X = Y.copy()
                Y = Y | (W & dtmc.pre_exists(Y))

            prob0 = dtmc.all_states - Y
            s_prime = prob0 | right_sat
            for state in s_prime:
                mod_trans_mat[state] = 0

            linear_equations = np.identity(mod_trans_mat.shape[0]) - mod_trans_mat
            indicator_vec = self.right_conj.sat_vector(dtmc)
            probabilities = linalg.solve(linear_equations, indicator_vec)
            return probabilities

    def dump(self, indent=0):
        print(indent * " " + "Until (%s)" % (str(self.step_count) if self.step_count > 0 else "inf"))
        print(indent * " " + "|")
        self.left_conj.dump(indent+1)
        print(indent * " " + "|")
        self.right_conj.dump(indent+1)

    def __str__(self):
        until_text = "U"
        if self.step_count > 0:
            until_text += "[%d]" % self.step_count
        return "%s %s %s" % (str(self.left_conj), until_text, str(self.right_conj))


class CSLUntilNode(object):

    def __init__(self, left_conj, right_conj, duration):
        self.left_conj = left_conj
        self.right_conj = right_conj
        self.duration = float(duration)

    def probability(self, ctmc):
        left_sat = self.left_conj.satisfy(ctmc)
        right_sat = self.right_conj.satisfy(ctmc)
        unsat = (ctmc.all_states - left_sat) - right_sat
        reduced_ctmc = ctmc.reduce(right_sat, unsat)
        indicator_vec = self.right_conj.sat_vector(ctmc)

        return reduced_ctmc.transient_prob(self.duration) @ indicator_vec

    def dump(self, indent=0):
        print(indent * " " + "Time Bounded Until (%s)" % (str(self.duration)))
        print(indent * " " + "|")
        self.left_conj.dump(indent+1)
        print(indent * " " + "|")
        self.right_conj.dump(indent+1)

    def __str__(self):
        until_text = "U"
        if self.step_count > 0:
            until_text += "[%d]" % self.step_count
        return "%s %s %s" % (str(self.left_conj), until_text, str(self.right_conj))