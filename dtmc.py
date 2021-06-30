#from Parser import Parser
import numpy as np


class State(object):

    def __init__(self, name):
        self.name = name
        self.propositions = set()
        self.transitions = {}

class DTMC(object):

    def __init__(self, state_names, propositions, transition_mat, specs=None):
        self.transitions = transition_mat
        self.propositions = propositions
        self.state_names = state_names
        self.sat_sets = {}
        self.sat_vectors = {}
        self.specs = specs
        if specs is None:
            self.specs = {}
        self.size = transition_mat.shape[0]
        self.all_states = set([i for i in range(self.size)])
        self.pre_sets = {}
        for i in range(self.size):
            pre_set = set()
            for j in range(self.size):
                if transition_mat[j,i] > 0:
                    pre_set.add(j)
            self.pre_sets[i] = pre_set

    def print_state_names(self, states):
        name_dict = {i : self.state_names[i] for i in states}
        print(name_dict)

    def pre_exists(self, state_set):
        pre_set = set()
        for s in state_set:
            pre_set |= self.pre_sets[s]
        return pre_set

    def satisfy(self, spec):
        #state_prop = Parser(formula).parse()
        return spec.satisfy(self)

    def check_all_specs(self):
        print("\n--- CHECKING SPECS ---\n")
        for spec_name, spec in self.specs.items():
            #print("Formula : %s" % str(spec))
            #spec.dump()
            spec_type = spec.__class__.__name__
            #print("Spec type ", spec_type)
            if spec_type == "ProbabilityNode":
                if spec.operator == "=":
                    satisfy_dict = self.satisfy(spec)
                    print("%s : %s" % (spec_name, {self.state_names[i] : prob for i, prob in satisfy_dict.items()}))
            else:
                satisfy_set = self.satisfy(spec)
                satisfy_names = set([self.state_names[i] for i in satisfy_set])
                print("%s : %s" % (spec_name, satisfy_names))

    def dump(self):
        print("DTMC")
        print("States : %s" % self.state_names)
        print("Propositions : %s" % self.propositions)
        print("Trans. Matrix :")
        print(self.transitions)

    @staticmethod
    def create(states, transitions, specs):
        state_names = []
        propositions = []
        state_ids = {}
        for state_name, state_propositions in states.items():
            state_ids[state_name] = len(state_names)
            state_names.append(state_name)
            propositions.append(state_propositions)

        size = len(state_names)
        transition_matrix = np.zeros((size, size))
        for state_name, trans_list in transitions.items():
            state_id = state_ids[state_name]
            for (next_name, prob) in trans_list:
                next_id = state_ids[next_name]
                transition_matrix[state_id, next_id] = prob

        for i in range(size):
            total_prob = np.sum(transition_matrix[i])
            if total_prob > 1:
                print(transition_matrix[i])
                raise Exception("Maximum outgoing probability is greater than 1")
            elif total_prob < 1:
                transition_matrix[i, i] = 1 - total_prob

        dtmc = DTMC(state_names, propositions, transition_matrix, specs)
        return dtmc
