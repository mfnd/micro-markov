import numpy as np
import numpy.linalg as linalg
import math


class StrongConnect:
    def __init__(self, trans_matrix):
        self.trans_matrix = trans_matrix
        self.size = trans_matrix.shape[0]
        self.S = []
        self.indices = [-1 for i in range(self.size)]
        self.lowlinks = [-1 for i in range(self.size)]
        self.on_stack = [False for i in range(self.size)]
        self.index = 0
        self.sccs = []

    def strong_connect(self):
        for v in range(self.size):
            if self.indices[v] == -1:
              self.strong_connect_sub(v)

    def strong_connect_sub(self, v):
        self.indices[v] = self.index
        self.lowlinks[v] = self.index
        self.index += 1
        self.S.append(v)
        self.on_stack[v] = True

        for w in range(self.size):
            if self.trans_matrix[v,w] > 0:
                if self.indices[w] == -1:
                    self.strong_connect_sub(w)
                    self.lowlinks[v] = min(self.lowlinks[v], self.lowlinks[w])
                elif self.on_stack[w]:
                    self.lowlinks[v] = min(self.lowlinks[v], self.indices[w])
        if self.lowlinks[v] == self.indices[v]:
            scc = []
            while True:
                w = self.S.pop()
                self.on_stack[w] = False
                scc.append(w)
                if w == v:
                    break
            self.sccs.append(np.sort(np.array(scc)))

class CTMC(object):

    def __init__(self, state_names, propositions, transitions_mat, specs=None, epsilon=0.000001):
        self.transitions = transitions_mat
        self.propositions = propositions
        self.state_names = state_names
        self.sat_sets = {}
        self.sat_vectors = {}
        self.specs = specs
        self.epsilon = epsilon
        if specs is None:
            self.specs = {}
        self.size = transitions_mat.shape[0]
        self.all_states = set([i for i in range(self.size)])
        self.pre_sets = {}
        for i in range(self.size):
            pre_set = set()
            for j in range(self.size):
                if transitions_mat[j,i] > 0:
                    pre_set.add(j)
            self.pre_sets[i] = pre_set

        self.q_mat = transitions_mat.copy()
        for i in range(self.size):
            self.q_mat[i,i] = -np.sum(self.q_mat[i])

        self.embedded = transitions_mat.copy()
        for i in range(self.size):
            row_sum = np.sum(self.embedded[i])
            if row_sum > 0:
                self.embedded[i] /= np.sum(self.embedded[i])
            else:
                self.embedded[i, i] = 1
        self.max_q = np.max(np.abs(self.q_mat))
        self.uniform = np.identity(self.size) + self.q_mat / self.max_q

        sc_algo = StrongConnect(self.transitions)
        sc_algo.strong_connect()
        self.sccs = sc_algo.sccs
        self.state_sccs = np.full((self.size), -1)

        for scc_id, scc in enumerate(self.sccs):
            self.state_sccs[scc] = scc_id

        self.bscc_ids = set([i for i in range(len(self.sccs))])
        for state_id in range(self.size):
            state_scc_id = self.state_sccs[state_id]
            if state_scc_id in self.bscc_ids \
                    and len(np.where(self.state_sccs[np.where(self.transitions[state_id] > 0)] != state_scc_id)[0]) > 0:
                self.bscc_ids.remove(state_scc_id)

        self.bscc_steady = []

        steady_probs = np.zeros((self.size, self.size))

        self.bscc_steady = []

        for i in self.bscc_ids:
            bscc = self.sccs[i]
            prob_reach = self.prob_reach(i)
            steady = None
            if len(bscc) == 1:
                steady = np.array([[1]])
            else:
                bscc_q = self.transitions[bscc][:, bscc].copy()
                for i in range(bscc_q.shape[0]):
                    bscc_q[i, i] = -np.sum(bscc_q[i])

                equation_mat = np.transpose(bscc_q)
                right_hand_side = np.zeros(len(bscc))
                (q, r) = linalg.qr(equation_mat)
                #print("QR Decomp R:", r)
                dependent_rows =  np.where(~r.any(axis=1))[0]
                steady = None
                if len(dependent_rows) > 1:
                    raise Exception("Singular matrix")
                elif len(dependent_rows) == 1:
                    equation_mat[dependent_rows[0]] = 1
                    right_hand_side[dependent_rows[0]] = 1
                    steady = linalg.solve(equation_mat, right_hand_side)
                else:
                    equation_mat[len(bscc)-1] = 1
                    right_hand_side[len(bscc)-1] = 1
                    steady = linalg.solve(equation_mat, right_hand_side)
                    steady /= np.sum(steady)
                steady = np.array([steady])
            steady_probs[:, bscc] = np.matmul(np.transpose(prob_reach), steady)

        self.steady_probs = steady_probs

    def reduce(self, sat, unsat):
        modified_trans = self.transitions.copy()
        for i in sat:
            modified_trans[i] = 0
        for i in unsat:
            modified_trans[i] = 0
        reduced_ctmc = CTMC(self.state_names, self.propositions, modified_trans)
        return reduced_ctmc

    def prob_reach(self, target_bscc_id):
        embed_dtmc = self.embedded.copy()
        for bscc_id in self.bscc_ids:
            bscc = self.sccs[bscc_id]
            embed_dtmc[bscc] = 0
        indicator = np.zeros(self.size)
        target_bscc = self.sccs[target_bscc_id]
        indicator[target_bscc] = 1
        equations = np.identity(self.size) - embed_dtmc
        solution = linalg.solve(equations, indicator)
        return np.array([solution])

    def transient_prob(self, t):
        rate = self.max_q * t
        transient_prob = self.poisson_prob(rate, 0) * np.identity(self.size)
        i = 1
        prev_poisson =  self.poisson_prob(rate, 0)
        while True:
            poisson_prob = self.poisson_prob(rate, i)
            matrix_pow = linalg.matrix_power(self.uniform, i)
            iter_prob = poisson_prob * matrix_pow
            transient_prob += iter_prob
            i += 1
            if poisson_prob < prev_poisson and poisson_prob < self.epsilon:
                break
            prev_poisson = poisson_prob
        return transient_prob

    def poisson_prob(self, rate, count):
        return math.exp(-rate) * math.pow(rate, count) / math.factorial(count)

    def steady_prob(self,t):
        pass

    def print_state_names(self, states):
        name_dict = {i : self.state_names[i] for i in states}
        print(name_dict)

    def pre_exists(self, state_set):
        pre_set = set()
        for s in state_set:
            pre_set |= self.pre_sets[s]
        return pre_set

    def satisfy(self, spec):
        return spec.satisfy(self)

    def check_all_specs(self):
        print("\n--- CHECKING SPECS ---\n")
        for spec_name, spec in self.specs.items():
            spec_type = spec.__class__.__name__
            if spec_type == "ProbabilityNode" or spec_type == "SteadyStateNode":
                if spec.operator == "=":
                    satisfy_dict = self.satisfy(spec)
                    print("%s : %s" % (spec_name, {self.state_names[i] : prob for i, prob in satisfy_dict.items()}))
            else:
                satisfy_set = self.satisfy(spec)
                satisfy_names = set([self.state_names[i] for i in satisfy_set])
                print("%s : %s" % (spec_name, satisfy_names))

    def dump(self):
        print("CTMC")
        print("States : %s" % self.state_names)
        print("Propositions : %s" % self.propositions)
        print("Trans. Matrix :")
        print(self.transitions)
        print("Generator Matrix :")
        print(self.q_mat)
        print("Embedded DTMC :")
        print(self.embedded)
        print("Uniformized DTMC :")
        print(self.uniform)

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
            for (next_name, rate) in trans_list:
                next_id = state_ids[next_name]
                transition_matrix[state_id, next_id] = rate

        ctmc = CTMC(state_names, propositions, transition_matrix, specs)
        return ctmc