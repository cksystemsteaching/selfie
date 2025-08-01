#!/usr/bin/env python3

# Copyright (c) the Selfie Project authors. All rights reserved.
# Please see the AUTHORS file for details. Use of this source code is
# governed by a BSD license that can be found in the LICENSE file.

# Selfie is a project of the Computational Systems Group at the
# Department of Computer Sciences of the University of Salzburg
# in Austria. For further information and code please refer to:

# selfie.cs.uni-salzburg.at

# Context-free language ordered bitvector decision diagrams (CFLOBVDDs)

# ------------------------------------------------------------

from bvdd import utilization

from math import log2
from math import ceil

class BV_Grouping:
    # generalizing CFLOBDDs to bitvector input variables with up to 8 bits
    pair_product_cache = {}
    pair_product_cache_hits = 0

    triple_product_cache = {}
    triple_product_cache_hits = 0

    reduction_cache = {}
    reduction_cache_hits = 0

    def __init__(self, level, number_of_input_bits, number_of_exits,
            number_of_paths_per_exit = {}, number_of_inputs_per_exit = {}):
        assert level >= 0
        self.level = level
        assert 0 < number_of_input_bits <= 8
        self.number_of_input_bits = number_of_input_bits
        self.number_of_exits = number_of_exits
        assert not number_of_paths_per_exit or len(number_of_paths_per_exit) == number_of_exits
        self.number_of_paths_per_exit = number_of_paths_per_exit
        assert not number_of_inputs_per_exit or len(number_of_inputs_per_exit) == number_of_exits
        self.number_of_inputs_per_exit = number_of_inputs_per_exit

    def __repr__(self):
        return f"{self.level} w/ {self.number_of_input_bits} input bits & {self.number_of_exits} exits"

    def number_of_paths(self):
        return sum(self.number_of_paths_per_exit.values())

    def number_of_inputs(self):
        return sum(self.number_of_inputs_per_exit.values())

    def is_consistent(self):
        assert self.number_of_exits > 0
        return True

    def is_pair_product_cached(self, g2):
        if (self, g2) in BV_Grouping.pair_product_cache:
            BV_Grouping.pair_product_cache_hits += 1
            return True
        else:
            return False

    def get_cached_pair_product(self, g2):
        assert self.is_pair_product_cached(g2)
        return BV_Grouping.pair_product_cache[(self, g2)]

    def cache_pair_product(self, g2, pair_product, pt_ans):
        if (self, g2) not in BV_Grouping.pair_product_cache:
            BV_Grouping.pair_product_cache[(self, g2)] = (pair_product, pt_ans)
        return BV_Grouping.pair_product_cache[(self, g2)]

    def is_triple_product_cached(self, g2, g3):
        if (self, g2, g3) in BV_Grouping.triple_product_cache:
            BV_Grouping.triple_product_cache_hits += 1
            return True
        else:
            return False

    def get_cached_triple_product(self, g2, g3):
        assert self.is_triple_product_cached(g2, g3)
        return BV_Grouping.triple_product_cache[(self, g2, g3)]

    def cache_triple_product(self, g2, g3, triple_product, pt_ans):
        if (self, g2, g3) not in BV_Grouping.triple_product_cache:
            BV_Grouping.triple_product_cache[(self, g2, g3)] = (triple_product, pt_ans)
        return BV_Grouping.triple_product_cache[(self, g2, g3)]

    def reduction_hash(reduction_tuple):
        return hash(tuple(reduction_tuple.values()))

    def is_reduction_cached(self, reduction_tuple):
        if (self, BV_Grouping.reduction_hash(reduction_tuple)) in BV_Grouping.reduction_cache:
            BV_Grouping.reduction_cache_hits += 1
            return True
        else:
            return False

    def get_cached_reduction(self, reduction_tuple):
        assert self.is_reduction_cached(reduction_tuple)
        return BV_Grouping.reduction_cache[(self, BV_Grouping.reduction_hash(reduction_tuple))]

    def cache_reduction(self, reduction_tuple, reduction):
        reduction_hash = BV_Grouping.reduction_hash(reduction_tuple)
        if (self, reduction_hash) not in BV_Grouping.reduction_cache:
            BV_Grouping.reduction_cache[(self, reduction_hash)] = reduction
        return BV_Grouping.reduction_cache[(self, reduction_hash)]

    def is_no_distinction_proto(self):
        return isinstance(self, BV_Dont_Care_Grouping) or isinstance(self, BV_No_Distinction_Proto)

    def reduce(self, reduction_tuple):
        assert len(reduction_tuple) == self.number_of_exits
        if reduction_tuple == dict(enumerate(range(1, len(reduction_tuple) + 1), 1)):
            return 1, self
        else:
            reduction_length = len(set(reduction_tuple.values()))
            if reduction_length == 1:
                return 1, BV_No_Distinction_Proto.representative(self.level,
                    self.number_of_input_bits)
            else:
                return reduction_length, self

class BV_Dont_Care_Grouping(BV_Grouping):
    representatives = {}

    def __init__(self, number_of_input_bits):
        super().__init__(0, number_of_input_bits, 1, {1:2**number_of_input_bits}, {1:1})

    def __repr__(self):
        return "dontcare @ " + super().__repr__()

    def get_paths(self, exit_i, index_i = 0):
        assert exit_i == 1
        return [(index_i, 0)]

    def is_consistent(self):
        assert super().is_consistent()
        return True

    def representative(number_of_input_bits):
        if number_of_input_bits not in BV_Dont_Care_Grouping.representatives:
            BV_Dont_Care_Grouping.representatives[number_of_input_bits] = BV_Dont_Care_Grouping(number_of_input_bits)
            assert BV_Dont_Care_Grouping.representatives[number_of_input_bits].is_consistent()
        return BV_Dont_Care_Grouping.representatives[number_of_input_bits]

    def pair_product(self, g2, inorder = True):
        assert isinstance(g2, BV_Grouping)

        if inorder:
            g1 = self
        else:
            g1 = g2
            g2 = self

        if g1.is_pair_product_cached(g2):
            return g1.get_cached_pair_product(g2)

        assert g1.number_of_input_bits == g2.number_of_input_bits

        if inorder:
            return g1.cache_pair_product(g2,
                g2, dict([(k, (1, k)) for k in range(1, g2.number_of_exits + 1)]))
        else:
            return g1.cache_pair_product(g2,
                g1, dict([(k, (k, 1)) for k in range(1, g1.number_of_exits + 1)]))

    def triple_product(self, g2, g3, order = 1):
        assert isinstance(g2, BV_Grouping) or isinstance(g3, BV_Grouping)

        if order == 1:
            g1 = self
        elif order == 2:
            g1 = g2
            g2 = self
        else:
            assert order == 3
            g1 = g2
            g2 = g3
            g3 = self

        if g1.is_triple_product_cached(g2, g3):
            return g1.get_cached_triple_product(g2, g3)

        assert g1.number_of_input_bits == g2.number_of_input_bits == g3.number_of_input_bits

        if g1.is_no_distinction_proto() and g2.is_no_distinction_proto():
            return g1.cache_triple_product(g2, g3,
                g3, dict([(k, (1, 1, k)) for k in range(1, g3.number_of_exits + 1)]))
        elif g1.is_no_distinction_proto() and g3.is_no_distinction_proto():
            return g1.cache_triple_product(g2, g3,
                g2, dict([(k, (1, k, 1)) for k in range(1, g2.number_of_exits + 1)]))
        elif g2.is_no_distinction_proto() and g3.is_no_distinction_proto():
            return g1.cache_triple_product(g2, g3,
                g1, dict([(k, (k, 1, 1)) for k in range(1, g1.number_of_exits + 1)]))
        elif g1.is_no_distinction_proto():
            g, pt = g2.pair_product(g3)
            return g1.cache_triple_product(g2, g3,
                g, dict([(jk, (1, pt[jk][0], pt[jk][1])) for jk in pt]))
        elif g2.is_no_distinction_proto():
            g, pt = g1.pair_product(g3)
            return g1.cache_triple_product(g2, g3,
                g, dict([(jk, (pt[jk][0], 1, pt[jk][1])) for jk in pt]))
        else:
            assert g3.is_no_distinction_proto()
            g, pt = g1.pair_product(g2)
            return g1.cache_triple_product(g2, g3,
                g, dict([(jk, (pt[jk][0], pt[jk][1], 1)) for jk in pt]))

    def reduce(self, reduction_tuple):
        assert reduction_tuple == {1:1}
        return self

class BV_Fork_Grouping(BV_Grouping):
    representatives = {}
    representatives_hits = 0

    def __init__(self, inputs, number_of_input_bits):
        assert 1 < len(inputs) <= 2**number_of_input_bits
        number_of_paths_per_exit = dict([(i, inputs[i].bit_count()) for i in inputs])
        super().__init__(0, number_of_input_bits, len(inputs),
            number_of_paths_per_exit, number_of_paths_per_exit)
        self.inputs = inputs

    def __repr__(self):
        indentation = " " * (CFLOBVDD.max_level - self.level + 1)
        return (indentation + "\n" +
            indentation + "fork @ " + super().__repr__() + ":\n" +
            indentation + f"{self.inputs}")

    def __hash__(self):
        return hash((self.number_of_exits,
            self.number_of_input_bits,
            tuple(self.inputs.values())))

    def __eq__(self, g2):
        return (isinstance(g2, BV_Fork_Grouping) and
            self.number_of_exits == g2.number_of_exits and
            self.number_of_input_bits == g2.number_of_input_bits and
            self.inputs == g2.inputs)

    def get_input_values(inputs, input_value = 0):
        assert inputs >= 0
        if inputs == 0:
            return []
        elif inputs == 1:
            return [input_value]
        else:
            number_of_input_bits = ceil(log2(inputs.bit_length()))
            assert 0 < number_of_input_bits <= 8, f"number_of_input_bits {number_of_input_bits} out of range with {inputs}"

            mid_input = 2**(number_of_input_bits - 1)

            low_inputs = inputs % 2**mid_input
            low_values = BV_Fork_Grouping.get_input_values(low_inputs, input_value)

            high_inputs = inputs >> mid_input

            if low_inputs == high_inputs:
                return [low_value + mid_input for low_value in low_values] + low_values
            else:
                return BV_Fork_Grouping.get_input_values(high_inputs, input_value + mid_input) + low_values

    def get_paths(self, exit_i, index_i = 0):
        assert 1 <= exit_i <= self.number_of_exits
        return [(index_i, self.inputs[exit_i])]

    def lowest_input(inputs):
        assert inputs > 0
        return inputs & ~(inputs - 1)

    def highest_input(inputs):
        assert inputs > 0
        return 2**int(log2(inputs))

    def is_consistent(self):
        assert super().is_consistent()
        assert len(self.inputs) == self.number_of_exits
        previous_exit = 0
        previous_inputs = 0
        union = 0
        for exit in self.inputs:
            assert exit == previous_exit + 1
            previous_exit = exit
            current_inputs = self.inputs[exit]
            assert 0 < current_inputs < 2**2**self.number_of_input_bits - 1
            assert (exit == 1 or
                BV_Fork_Grouping.lowest_input(current_inputs) >
                    BV_Fork_Grouping.lowest_input(previous_inputs)), f"{exit} == 1 or {BV_Fork_Grouping.lowest_input(current_inputs)} > {BV_Fork_Grouping.lowest_input(previous_inputs)}"
            previous_inputs = current_inputs
            assert current_inputs & union == 0
            union |= current_inputs
        assert union == 2**2**self.number_of_input_bits - 1, f"{union} == {2**2**self.number_of_input_bits - 1}"
        return True

    def representative(self):
        if self in BV_Fork_Grouping.representatives:
            BV_Fork_Grouping.representatives_hits += 1
        else:
            assert self.is_consistent()
            BV_Fork_Grouping.representatives[self] = self
        return BV_Fork_Grouping.representatives[self]

    def projection_proto(number_of_input_bits):
        return BV_Fork_Grouping(dict([(i + 1, 2**i) for i in range(2**number_of_input_bits)]),
            number_of_input_bits).representative()

    def pair_product(self, g2):
        assert isinstance(g2, BV_Grouping)

        g1 = self

        assert g1.number_of_input_bits == g2.number_of_input_bits

        if isinstance(g2, BV_Dont_Care_Grouping):
            return g2.pair_product(g1, False)
        else:
            if g1.is_pair_product_cached(g2):
                return g1.get_cached_pair_product(g2)

            assert isinstance(g2, BV_Fork_Grouping)

            g_exit = 0
            g_inputs = {}
            g_pair_tuples = {}

            g2_exit = 1
            g2_inputs = {}
            g2_inputs[g2_exit] = g2.inputs[g2_exit]

            for g1_exit in g1.inputs:
                g1_inputs = g1.inputs[g1_exit]

                # exploit lexicographic ordering of g1 and g2 inputs by lowest input

                while (BV_Fork_Grouping.highest_input(g2_inputs[g2_exit]) <
                    BV_Fork_Grouping.lowest_input(g1_inputs)):
                    # move on to next g2 inputs
                    if g2_exit < g2.number_of_exits:
                        g2_exit += 1
                        if g2_exit not in g2_inputs:
                            g2_inputs[g2_exit] = g2.inputs[g2_exit]
                    else:
                        return g1.cache_pair_product(g2,
                            BV_Fork_Grouping(g_inputs, g1.number_of_input_bits).representative(),
                            g_pair_tuples)

                next_g2_exit = g2_exit

                while (g1_inputs > 0 and
                    BV_Fork_Grouping.lowest_input(g2_inputs[next_g2_exit]) <=
                        BV_Fork_Grouping.highest_input(g1_inputs)):
                    # intersect with all overlapping next g2 inputs
                    intersection = g1_inputs & g2_inputs[next_g2_exit]

                    if intersection != 0:
                        g_exit += 1

                        # insert intersection sorted by lowest input
                        # to establish lexicographical ordering of g inputs
                        exit_i = g_exit
                        while (exit_i > 1 and
                            BV_Fork_Grouping.lowest_input(intersection) <
                                BV_Fork_Grouping.lowest_input(g_inputs[exit_i - 1])):
                            g_inputs[exit_i] = g_inputs[exit_i - 1]
                            g_pair_tuples[exit_i] = g_pair_tuples[exit_i - 1]
                            exit_i -= 1
                        g_inputs[exit_i] = intersection
                        g_pair_tuples[exit_i] = (g1_exit, next_g2_exit)

                        g1_inputs &= ~intersection
                        # do not remove intersection from next g2 inputs
                        # to maintain lexicographical ordering of g2 inputs

                    next_g2_exit += 1

                    if next_g2_exit <= len(g2.inputs):
                        if next_g2_exit not in g2_inputs:
                            g2_inputs[next_g2_exit] = g2.inputs[next_g2_exit]
                    else:
                        break

            return g1.cache_pair_product(g2,
                BV_Fork_Grouping(g_inputs, g1.number_of_input_bits).representative(),
                g_pair_tuples)

    def triple_product(self, g2, g3):
        assert isinstance(g2, BV_Grouping) and isinstance(g3, BV_Grouping)

        g1 = self

        assert g1.number_of_input_bits == g2.number_of_input_bits == g3.number_of_input_bits

        if g2.is_no_distinction_proto():
            return g2.triple_product(g1, g3, 2)
        elif g3.is_no_distinction_proto():
            return g3.triple_product(g1, g2, 3)
        else:
            if g1.is_triple_product_cached(g2, g3):
                return g1.get_cached_triple_product(g2, g3)

            assert isinstance(g2, BV_Fork_Grouping) and isinstance(g3, BV_Fork_Grouping)

            g, pt23 = g2.pair_product(g3)
            g, pt123 = g1.pair_product(g)

            tt = dict([(k, (pt123[k][0], pt23[pt123[k][1]][0], pt23[pt123[k][1]][1]))
                for k in pt123])

            return g1.cache_triple_product(g2, g3, g, tt)

    def reduce(self, reduction_tuple):
        reduction_length, reduction = super().reduce(reduction_tuple)

        if reduction_length == 1:
            return reduction
        else:
            if self.is_reduction_cached(reduction_tuple):
                return self.get_cached_reduction(reduction_tuple)

            g_exits = {}
            g_inputs = {}

            for exit in self.inputs:
                reduced_to_exit = reduction_tuple[exit]

                assert reduced_to_exit <= exit

                if reduced_to_exit not in g_exits:
                    new_exit = len(g_inputs) + 1
                    g_exits[reduced_to_exit] = new_exit
                    g_inputs[new_exit] = self.inputs[exit]
                else:
                    new_exit = g_exits[reduced_to_exit]
                    assert g_inputs[new_exit] & self.inputs[exit] == 0
                    g_inputs[new_exit] |= self.inputs[exit]

            assert len(g_inputs) > 0

            if len(g_inputs) > 1:
                g = BV_Fork_Grouping(g_inputs, self.number_of_input_bits).representative()
            else:
                g = BV_Dont_Care_Grouping.representative(self.number_of_input_bits)

            return self.cache_reduction(reduction_tuple, g)

class BV_Internal_Grouping(BV_Grouping):
    representatives = {}
    representatives_hits = 0

    def __init__(self, level, number_of_input_bits, number_of_exits = 0):
        assert level > 0
        super().__init__(level, number_of_input_bits, number_of_exits)
        self.a_connection = None
        self.a_return_tuple = {}
        self.number_of_b_connections = 0
        self.b_connections = {}
        self.b_return_tuples = {}

    def __repr__(self):
        indentation = " " * (CFLOBVDD.max_level - self.level + 1)
        return (indentation + "\n" +
            indentation + f"{type(self).__name__} @ " + super().__repr__() + ":\n" +
            indentation + f"a_c: {self.a_connection}\n" +
            indentation + f"a_rt: {self.a_return_tuple}\n" +
            indentation + f"n_of_b: {self.number_of_b_connections}\n" +
            indentation + f"b_c: {self.b_connections}\n" +
            indentation + f"b_rt: {self.b_return_tuples}")

    def __hash__(self):
        return hash((self.level,
            self.number_of_input_bits,
            self.number_of_exits,
            self.a_connection,
            tuple(self.a_return_tuple.values()),
            self.number_of_b_connections,
            tuple(self.b_connections.values()),
            tuple([(tuple(rt), tuple(rt.values())) for rt in self.b_return_tuples.values()])))

    def __eq__(self, g2):
        return (isinstance(g2, BV_Internal_Grouping) and
            self.level == g2.level and
            self.number_of_input_bits == g2.number_of_input_bits and
            self.number_of_exits == g2.number_of_exits and
            self.a_connection == g2.a_connection and
            self.a_return_tuple == g2.a_return_tuple and
            self.number_of_b_connections == g2.number_of_b_connections and
            self.b_connections == g2.b_connections and
            self.b_return_tuples == g2.b_return_tuples)

    def get_paths(self, exit_i, index_i = 0):
        inputs = []
        for b_i in self.b_return_tuples:
            b_rt = self.b_return_tuples[b_i]
            for b_e_i in b_rt:
                if exit_i == b_rt[b_e_i]:
                    inputs += [(self.a_connection.get_paths(b_i, index_i),
                        self.b_connections[b_i].get_paths(b_e_i,
                            index_i + 2**(self.level - 1)))]
                    break
        return inputs

    def is_consistent(self):
        assert super().is_consistent()
        g_a = self.a_connection
        assert isinstance(g_a, BV_Grouping)
        assert not self.a_return_tuple or len(self.a_return_tuple) == g_a.number_of_exits
        assert len(self.a_return_tuple) == len(set(self.a_return_tuple.values()))
        assert self.number_of_b_connections == g_a.number_of_exits
        assert len(self.b_connections) == self.number_of_b_connections
        assert len(self.b_return_tuples) == len(self.b_connections)
        for g_a_e_i in self.a_return_tuple:
            assert 1 <= g_a_e_i <= g_a.number_of_exits
            a_e_i = self.a_return_tuple[g_a_e_i]
            assert g_a_e_i == a_e_i
            assert 1 <= a_e_i <= self.number_of_b_connections
        g_exits = {}
        for g_b_i in self.b_connections:
            g_b = self.b_connections[g_b_i]
            assert g_b_i in self.b_return_tuples
            g_b_i_rt = self.b_return_tuples[g_b_i]
            assert len(g_b_i_rt) == len(set(g_b_i_rt.values()))
            g_b_i_rt_targets = {}
            previous_target = 0
            for g_b_i_rt_e_j in g_b_i_rt:
                assert 1 <= g_b_i_rt_e_j <= g_b.number_of_exits, f"1 <= {g_b_i_rt_e_j} <= {g_b.number_of_exits}: {self}"
                g_b_i_rt_e_j_e_t = g_b_i_rt[g_b_i_rt_e_j]
                assert 1 <= g_b_i_rt_e_j_e_t <= self.number_of_exits
                assert g_b_i_rt_e_j_e_t not in g_b_i_rt_targets
                g_b_i_rt_targets[g_b_i_rt_e_j_e_t] = None
                if g_b_i_rt_e_j_e_t not in g_exits:
                    if previous_target != 0:
                        assert g_b_i_rt_e_j_e_t == previous_target + 1
                    previous_target = g_b_i_rt_e_j_e_t
            g_exits |= g_b_i_rt_targets
        return True

    def pre_compute_number_of_paths_and_inputs_per_exit(self):
        self.number_of_paths_per_exit = dict([(i, 0) for i in range(1, self.number_of_exits + 1)])
        self.number_of_inputs_per_exit = dict([(i, 0) for i in range(1, self.number_of_exits + 1)])
        g_a = self.a_connection
        for g_b_i in self.b_connections:
            a_number_of_paths = g_a.number_of_paths_per_exit[g_b_i]
            a_number_of_inputs = g_a.number_of_inputs_per_exit[g_b_i]
            g_b = self.b_connections[g_b_i]
            g_b_i_rt = self.b_return_tuples[g_b_i]
            for g_b_i_rt_e_j in g_b_i_rt:
                e_i = g_b_i_rt[g_b_i_rt_e_j]
                b_number_of_paths = g_b.number_of_paths_per_exit[g_b_i_rt_e_j]
                b_number_of_inputs = g_b.number_of_inputs_per_exit[g_b_i_rt_e_j]
                self.number_of_paths_per_exit[e_i] += a_number_of_paths * b_number_of_paths
                self.number_of_inputs_per_exit[e_i] += a_number_of_inputs * b_number_of_inputs
        assert self.number_of_paths() >= self.number_of_inputs() >= self.number_of_exits

    def representative(self):
        self.pre_compute_number_of_paths_and_inputs_per_exit()
        if self in BV_Internal_Grouping.representatives:
            BV_Internal_Grouping.representatives_hits += 1
        else:
            assert self.is_consistent()
            BV_Internal_Grouping.representatives[self] = self
        return BV_Internal_Grouping.representatives[self]

    def projection_proto(level, input_i, number_of_input_bits, number_of_output_bits):
        # generalizing CFLOBDD projection to bitvectors of size >= 1
        if level == 0:
            assert input_i == 0 and number_of_output_bits == number_of_input_bits
            return BV_Fork_Grouping.projection_proto(number_of_input_bits)
        else:
            assert 0 <= input_i < 2**level
            assert number_of_output_bits % number_of_input_bits == 0
            assert 0 < number_of_output_bits <= (2**level - input_i) * number_of_input_bits

            g = BV_Internal_Grouping(level, number_of_input_bits, 2**number_of_output_bits)

            if input_i < 2**(level - 1):
                a_number_of_output_bits = min((2**(level - 1) - input_i) * number_of_input_bits,
                    number_of_output_bits)
                g.a_connection = BV_Internal_Grouping.projection_proto(level - 1,
                    input_i, number_of_input_bits, a_number_of_output_bits)
                # g.a_return_tuple == {} representing g.a_return_tuple = dict([(e, e)
                    # for e in range(1, 2**a_number_of_output_bits + 1)])

                input_i = 2**(level - 1)
            else:
                a_number_of_output_bits = 0

                g.a_connection = BV_No_Distinction_Proto.representative(level - 1,
                    number_of_input_bits)
                # g.a_return_tuple == {} representing g.a_return_tuple[1] = 1

            g.number_of_b_connections = 2**a_number_of_output_bits

            b_number_of_output_bits = number_of_output_bits - a_number_of_output_bits

            if b_number_of_output_bits == 0:
                projection_proto = BV_No_Distinction_Proto.representative(level - 1,
                    number_of_input_bits)
            else:
                projection_proto = BV_Internal_Grouping.projection_proto(level - 1,
                    input_i - 2**(level - 1),
                    number_of_input_bits,
                    b_number_of_output_bits)

            g.b_connections = dict([(c, projection_proto)
                for c in range(1, g.number_of_b_connections + 1)])
            g.b_return_tuples = dict([(c,
                dict([(e, 2**b_number_of_output_bits * (c - 1) + e)
                    for e in range(1, 2**b_number_of_output_bits + 1)]))
                for c in range(1, g.number_of_b_connections + 1)])

            return g.representative()

    def pair_product(self, g2):
        assert isinstance(g2, BV_Grouping)

        g1 = self

        assert g1.level == g2.level
        assert g1.number_of_input_bits == g2.number_of_input_bits

        if g2.is_no_distinction_proto():
            return g2.pair_product(g1, False)
        else:
            if g1.is_pair_product_cached(g2):
                return g1.get_cached_pair_product(g2)

            assert isinstance(g2, BV_Internal_Grouping)

            g_a, pt_a = g1.a_connection.pair_product(g2.a_connection)

            g = BV_Internal_Grouping(g1.level, g1.number_of_input_bits)

            g.a_connection = g_a
            # g.a_return_tuple == {} representing g.a_return_tuple = dict([(i, i) for i in pt_a])

            g.number_of_b_connections = len(pt_a)

            pt_ans = {}
            pt_ans_inv = {}

            for j in pt_a:
                g_b, pt_b = g1.b_connections[pt_a[j][0]].pair_product(g2.b_connections[pt_a[j][1]])

                g.b_connections[j] = g_b
                g.b_return_tuples[j] = {}

                for i in pt_b:
                    c1 = g1.b_return_tuples[pt_a[j][0]][pt_b[i][0]]
                    c2 = g2.b_return_tuples[pt_a[j][1]][pt_b[i][1]]

                    if (c1, c2) in pt_ans_inv:
                        g.b_return_tuples[j][len(g.b_return_tuples[j]) + 1] = pt_ans_inv[(c1, c2)]
                    else:
                        g.number_of_exits += 1
                        g.b_return_tuples[j][len(g.b_return_tuples[j]) + 1] = g.number_of_exits
                        pt_ans[len(pt_ans) + 1] = (c1, c2)
                        pt_ans_inv[(c1, c2)] = len(pt_ans)

            return g1.cache_pair_product(g2, g.representative(), pt_ans)

    def triple_product(self, g2, g3):
        assert isinstance(g2, BV_Grouping) and isinstance(g3, BV_Grouping)

        g1 = self

        assert g1.level == g2.level == g3.level
        assert g1.number_of_input_bits == g2.number_of_input_bits == g3.number_of_input_bits

        if g2.is_no_distinction_proto():
            return g2.triple_product(g1, g3, 2)
        elif g3.is_no_distinction_proto():
            return g3.triple_product(g1, g2, 3)
        else:
            if g1.is_triple_product_cached(g2, g3):
                return g1.get_cached_triple_product(g2, g3)

            assert isinstance(g2, BV_Internal_Grouping) and isinstance(g3, BV_Internal_Grouping)

            g_a, tt_a = g1.a_connection.triple_product(g2.a_connection, g3.a_connection)

            g = BV_Internal_Grouping(g1.level, g1.number_of_input_bits)

            g.a_connection = g_a
            # g.a_return_tuple == {} representing g.a_return_tuple = dict([(i, i) for i in tt_a])

            g.number_of_b_connections = len(tt_a)

            pt_ans = {}
            pt_ans_inv = {}

            for j in tt_a:
                g_b, pt_b = g1.b_connections[tt_a[j][0]].triple_product(g2.b_connections[tt_a[j][1]],
                    g3.b_connections[tt_a[j][2]])

                g.b_connections[j] = g_b
                g.b_return_tuples[j] = {}

                for i in pt_b:
                    c1 = g1.b_return_tuples[tt_a[j][0]][pt_b[i][0]]
                    c2 = g2.b_return_tuples[tt_a[j][1]][pt_b[i][1]]
                    c3 = g3.b_return_tuples[tt_a[j][2]][pt_b[i][2]]

                    if (c1, c2, c3) in pt_ans_inv:
                        g.b_return_tuples[j][len(g.b_return_tuples[j]) + 1] = pt_ans_inv[(c1, c2, c3)]
                    else:
                        g.number_of_exits += 1
                        g.b_return_tuples[j][len(g.b_return_tuples[j]) + 1] = g.number_of_exits
                        pt_ans[len(pt_ans) + 1] = (c1, c2, c3)
                        pt_ans_inv[(c1, c2, c3)] = len(pt_ans)

            return g1.cache_triple_product(g2, g3, g.representative(), pt_ans)

    def insert_b_connection(self, h, return_tuple):
        assert isinstance(h, BV_Grouping)

        for i in self.b_connections:
            if self.b_connections[i] == h and self.b_return_tuples[i] == return_tuple:
                return i

        self.number_of_b_connections += 1
        self.b_connections[self.number_of_b_connections] = h
        self.b_return_tuples[self.number_of_b_connections] = return_tuple

        return self.number_of_b_connections

    def reduce(self, reduction_tuple):
        reduction_length, reduction = super().reduce(reduction_tuple)

        if reduction_length == 1:
            return reduction
        else:
            g = self

            if g.is_reduction_cached(reduction_tuple):
                return g.get_cached_reduction(reduction_tuple)

            g_prime = BV_Internal_Grouping(g.level, g.number_of_input_bits, reduction_length)

            reduction_tuple_a = {}

            for i in g.b_connections:
                induced_return_tuple, induced_reduction_tuple = \
                    CFLOBVDD.linear_collapse_classes_leftmost(dict(enumerate([reduction_tuple[v]
                        for v in g.b_return_tuples[i].values()], 1)))

                h = g.b_connections[i].reduce(induced_reduction_tuple)

                position = g_prime.insert_b_connection(h, induced_return_tuple)

                reduction_tuple_a[len(reduction_tuple_a) + 1] = position

            induced_return_tuple, induced_reduction_tuple = \
                CFLOBVDD.linear_collapse_classes_leftmost(reduction_tuple_a)

            g_prime.a_connection = g.a_connection.reduce(induced_reduction_tuple)
            assert all([i == induced_return_tuple[i] for i in induced_return_tuple])
            # g_prime.a_return_tuple == {} representing g_prime.a_return_tuple = induced_return_tuple

            return g.cache_reduction(reduction_tuple, g_prime.representative())

class BV_No_Distinction_Proto(BV_Internal_Grouping):
    representatives = {}
    representatives_hits = 0

    def __init__(self, level, number_of_input_bits):
        assert level > 0
        super().__init__(level, number_of_input_bits, 1)

    def representative(level, number_of_input_bits):
        if level == 0:
            return BV_Dont_Care_Grouping.representative(number_of_input_bits)
        elif (level, number_of_input_bits) in BV_No_Distinction_Proto.representatives:
            BV_No_Distinction_Proto.representatives_hits += 1
            return BV_No_Distinction_Proto.representatives[(level, number_of_input_bits)]
        else:
            g = BV_No_Distinction_Proto(level, number_of_input_bits)

            g.a_connection = BV_No_Distinction_Proto.representative(level - 1,
                number_of_input_bits)
            # g.a_return_tuple == {} representing g.a_return_tuple[1] = 1

            g.number_of_b_connections = 1
            g.b_connections[1] = g.a_connection
            g.b_return_tuples[1] = {1:1}

            g.pre_compute_number_of_paths_and_inputs_per_exit()

            BV_No_Distinction_Proto.representatives[(level, number_of_input_bits)] = g

            return g

    def pair_product(self, g2, inorder = True):
        assert isinstance(g2, BV_Grouping)

        g1 = self

        assert g1.level == g2.level
        assert g1.number_of_input_bits == g2.number_of_input_bits

        return BV_Dont_Care_Grouping.pair_product(g1, g2, inorder)

    def triple_product(self, g2, g3, order = 1):
        assert isinstance(g2, BV_Grouping) and isinstance(g3, BV_Grouping)

        g1 = self

        assert g1.level == g2.level == g3.level
        assert g1.number_of_input_bits == g2.number_of_input_bits == g3.number_of_input_bits

        return BV_Dont_Care_Grouping.triple_product(g1, g2, g3, order)

    def reduce(self, reduction_tuple):
        assert reduction_tuple == {1:1}
        return self

class Collapsed_Classes:
    cache = {}
    cache_hits = 0

    def __init__(self, classes):
        self.classes = classes

    def __hash__(self):
        return hash((tuple(self.classes.values()), isinstance(self.classes[1], bool)))

    def __eq__(self, c2):
        return isinstance(c2, Collapsed_Classes) and self.classes == c2.classes

    def are_collapsed_classes_cached(equiv_classes):
        if Collapsed_Classes(equiv_classes) in Collapsed_Classes.cache:
            Collapsed_Classes.cache_hits += 1
            return True
        else:
            return False

    def get_collapsed_classes(equiv_classes):
        return Collapsed_Classes.cache[Collapsed_Classes(equiv_classes)]

    def cache_collapsed_classes(equiv_classes, projected_classes, renumbered_classes):
        collapsed_classes = Collapsed_Classes(equiv_classes)
        if collapsed_classes not in Collapsed_Classes.cache:
            Collapsed_Classes.cache[collapsed_classes] = (projected_classes, renumbered_classes)
        return Collapsed_Classes.cache[collapsed_classes]

class CFLOBVDD:
    REDUCE = True

    max_level = 0

    representatives = {}
    representatives_hits = 0

    def __init__(self, grouping, outputs, number_of_input_bits, number_of_output_bits):
        self.grouping = grouping
        self.outputs = outputs
        self.number_of_input_bits = number_of_input_bits
        self.number_of_output_bits = number_of_output_bits

    def __str__(self):
        return ("CFLOBVDD with\n" +
            f"g: {self.grouping}\n" +
            f"o: {self.outputs}\n" +
            f"n_of_i_b: {self.number_of_input_bits}\n" +
            f"n_of_o_b: {self.number_of_output_bits}")

    def __hash__(self):
        return hash((self.grouping,
            tuple(self.outputs.values()),
            self.number_of_input_bits,
            self.number_of_output_bits))

    def __eq__(self, n2):
        return (isinstance(n2, CFLOBVDD) and
            self.grouping == n2.grouping and
            self.outputs == n2.outputs and
            self.number_of_input_bits == n2.number_of_input_bits and
            self.number_of_output_bits == n2.number_of_output_bits)

    def print_profile():
        print(f"BV_Fork_Grouping cache utilization: {utilization(BV_Fork_Grouping.representatives_hits, len(BV_Fork_Grouping.representatives))}")
        print(f"BV_Internal_Grouping cache utilization: {utilization(BV_Internal_Grouping.representatives_hits, len(BV_Internal_Grouping.representatives))}")
        print(f"BV_No_Distinction_Proto cache utilization: {utilization(BV_No_Distinction_Proto.representatives_hits, len(BV_No_Distinction_Proto.representatives))}")
        print(f"BV_Grouping pair-product cache utilization: {utilization(BV_Grouping.pair_product_cache_hits, len(BV_Grouping.pair_product_cache))}")
        print(f"BV_Grouping triple-product cache utilization: {utilization(BV_Grouping.triple_product_cache_hits, len(BV_Grouping.triple_product_cache))}")
        print(f"BV_Grouping reduction cache utilization: {utilization(BV_Grouping.reduction_cache_hits, len(BV_Grouping.reduction_cache))}")
        print(f"CFLOBVDD collapsed-equivalence-classes cache utilization: {utilization(Collapsed_Classes.cache_hits, len(Collapsed_Classes.cache))}")
        print(f"CFLOBVDD cache utilization: {utilization(CFLOBVDD.representatives_hits, len(CFLOBVDD.representatives))}")

    def number_of_paths(self):
        return self.grouping.number_of_paths()

    def number_of_inputs(self):
        return self.grouping.number_of_inputs()

    def number_of_outputs(self):
        return len(self.outputs)

    def number_of_distinct_outputs(self):
        return len(set(self.outputs.values()))

    def get_printed_paths(paths, full_paths = True):
        printed_paths = []
        for path in paths:
            if isinstance(path[0], int):
                assert isinstance(path[1], int)
                index_i = path[0]
                inputs = path[1]
                if inputs == 0:
                    if full_paths:
                        printed_paths += [f"[dontcare @ {index_i}]"]
                else:
                    printed_paths += ["[" +
                        f"input @ {index_i}: " +
                        "|".join([str(input_value) for input_value in BV_Fork_Grouping.get_input_values(inputs)]) +
                        "]"]
            else:
                a_paths = CFLOBVDD.get_printed_paths(path[0], full_paths)
                b_paths = CFLOBVDD.get_printed_paths(path[1], full_paths)
                if a_paths:
                    if b_paths:
                        printed_paths += ["(" + "&".join(a_paths + b_paths) + ")"]
                    else:
                        printed_paths += a_paths
                elif b_paths:
                    printed_paths += b_paths
        if len(printed_paths) > 1:
            return ["[" + "|".join(printed_paths) + "]"]
        else:
            return printed_paths

    def get_printed_value_paths(self, value = None):
        value_paths = ""
        for exit_i in self.outputs:
            if value is None or self.outputs[exit_i] == value:
                if value_paths:
                    value_paths += "\n"
                value_paths += (f"{self.outputs[exit_i]} <- " +
                    CFLOBVDD.get_printed_paths(self.grouping.get_paths(exit_i))[0])
                # without reductions value may appear more than once
        return value_paths

    def get_printed_CFLOBVDD(self, value = None):
        return (f"CFLOBVDD:\n" +
            f"{2**self.grouping.level * self.number_of_input_bits} input bits in total\n" +
            f"{2**self.grouping.level} input variables\n" +
            f"{self.number_of_input_bits} input bits per variable\n" +
            f"{self.number_of_outputs()} output values\n" +
            f"{self.number_of_distinct_outputs()} disctinct output values\n"
            f"{self.number_of_output_bits} output bits per value\n" +
            f"{self.number_of_paths()} paths\n" +
            f"{self.number_of_inputs()} inputs\n" +
            f"{self.get_printed_value_paths(value)}")

    def is_consistent(self):
        assert self.grouping.is_consistent()
        assert self.number_of_outputs() == self.grouping.number_of_exits, f"{self.number_of_outputs()} == {self.grouping.number_of_exits}"
        assert self.number_of_outputs() >= self.number_of_distinct_outputs()
        assert not CFLOBVDD.REDUCE or self.number_of_outputs() == self.number_of_distinct_outputs()
        assert all([0 <= self.outputs[i] < 2**self.number_of_output_bits for i in self.outputs])
        return True

    def representative(grouping, outputs, number_of_input_bits, number_of_output_bits):
        cflobvdd = CFLOBVDD(grouping, outputs, number_of_input_bits, number_of_output_bits)
        if cflobvdd in CFLOBVDD.representatives:
            CFLOBVDD.representatives_hits += 1
        else:
            assert cflobvdd.is_consistent()
            CFLOBVDD.representatives[cflobvdd] = cflobvdd
        return CFLOBVDD.representatives[cflobvdd]

    def is_always_false(self):
        # without reductions False may appear more than once
        return self.number_of_distinct_outputs() == 1 and False in self.outputs.values()

    def is_always_true(self):
        # without reductions True may appear more than once
        return self.number_of_distinct_outputs() == 1 and True in self.outputs.values()

    def constant(level, output, number_of_input_bits, number_of_output_bits):
        return CFLOBVDD.representative(
            BV_No_Distinction_Proto.representative(level, number_of_input_bits),
            {1:output},
            number_of_input_bits,
            number_of_output_bits)

    def byte_constant(number_of_input_bytes, output, number_of_input_bits, number_of_output_bits):
        assert number_of_input_bytes > 0
        assert 0 < number_of_input_bits <= 8
        assert 8 % number_of_input_bits == 0

        level = ceil(log2(number_of_input_bytes * (8 // number_of_input_bits)))

        return CFLOBVDD.constant(level, output, number_of_input_bits, number_of_output_bits)

    def false(level, number_of_input_bits):
        return CFLOBVDD.constant(level, False, number_of_input_bits, 1)

    def true(level, number_of_input_bits):
        return CFLOBVDD.constant(level, True, number_of_input_bits, 1)

    def flip_value_tuple(self):
        # self must be reduced
        assert self.number_of_outputs() == 2
        return CFLOBVDD.representative(self.grouping,
            {1:self.outputs[2], 2:self.outputs[1]},
            self.number_of_input_bits,
            self.number_of_output_bits)

    def complement(self):
        if self == CFLOBVDD.false(self.grouping.level, self.number_of_input_bits):
            return CFLOBVDD.true(self.grouping.level, self.number_of_input_bits)
        elif self == CFLOBVDD.true(self.grouping.level, self.number_of_input_bits):
            return CFLOBVDD.false(self.grouping.level, self.number_of_input_bits)
        else:
            # self must be reduced
            return self.flip_value_tuple()

    def unary_apply_and_reduce(self, op, number_of_output_bits):
        return self.binary_apply_and_reduce(CFLOBVDD.constant(self.grouping.level,
                0, self.number_of_input_bits, number_of_output_bits),
            lambda x, y: op(x), number_of_output_bits)

    def projection(level, input_i, number_of_input_bits, number_of_output_bits):
        assert 0 <= input_i < 2**level
        assert number_of_output_bits % number_of_input_bits == 0
        assert number_of_output_bits <= (2**level - input_i) * number_of_input_bits
        CFLOBVDD.max_level = max(CFLOBVDD.max_level, level)
        return CFLOBVDD.representative(
            BV_Internal_Grouping.projection_proto(level,
                input_i, number_of_input_bits, number_of_output_bits),
            dict([(output + 1, output) for output in range(2**number_of_output_bits)]),
            number_of_input_bits,
            number_of_output_bits)

    def byte_projection(number_of_input_bytes, byte_i, number_of_input_bits, number_of_output_bits):
        assert number_of_input_bytes > 0
        assert 0 <= byte_i < number_of_input_bytes
        assert 0 < number_of_input_bits <= 8
        assert 8 % number_of_input_bits == 0

        level = ceil(log2(number_of_input_bytes * (8 // number_of_input_bits)))
        input_i = byte_i * (8 // number_of_input_bits)

        return CFLOBVDD.projection(level, input_i, number_of_input_bits, number_of_output_bits)

    def collapse_classes_leftmost(equiv_classes):
        # legacy code
        if Collapsed_Classes.are_collapsed_classes_cached(equiv_classes):
            return Collapsed_Classes.get_collapsed_classes(equiv_classes)

        # square-time iteration over equivalence classes
        projected_classes = dict(enumerate([equiv_classes[i]
            for i in equiv_classes if i == min([j for j in equiv_classes
                if equiv_classes[j] == equiv_classes[i]])], 1))

        order_of_projected_classes = dict([(projected_classes[i], i)
            for i in projected_classes])

        return Collapsed_Classes.cache_collapsed_classes(equiv_classes,
            projected_classes,
            dict(enumerate([order_of_projected_classes[v] for v in equiv_classes.values()], 1)))

    def linear_collapse_classes_leftmost(equiv_classes):
        if Collapsed_Classes.are_collapsed_classes_cached(equiv_classes):
            return Collapsed_Classes.get_collapsed_classes(equiv_classes)

        leftmost_equiv_class_index = {}

        projected_classes = {}
        renumbered_classes = {}

        # linear-time iteration over equivalence classes
        for index in equiv_classes:
            value = equiv_classes[index]

            if value not in leftmost_equiv_class_index:
                # remember leftmost equivalence class index
                leftmost_equiv_class_index[value] = len(leftmost_equiv_class_index) + 1

                projected_classes[len(leftmost_equiv_class_index)] = value

            renumbered_classes[index] = leftmost_equiv_class_index[value]

        return Collapsed_Classes.cache_collapsed_classes(equiv_classes,
            projected_classes, renumbered_classes)

    def binary_apply_and_reduce(self, n2, op, number_of_output_bits):
        assert isinstance(n2, CFLOBVDD)

        n1 = self

        assert n1.number_of_input_bits == n2.number_of_input_bits

        g, pt = n1.grouping.pair_product(n2.grouping)

        equiv_classes = dict([(i, op(n1.outputs[pt[i][0]], n2.outputs[pt[i][1]])) for i in pt])

        if CFLOBVDD.REDUCE:
            induced_value_tuple, induced_return_tuple = \
                CFLOBVDD.linear_collapse_classes_leftmost(equiv_classes)
            g = g.reduce(induced_return_tuple)
        else:
            induced_value_tuple = equiv_classes

        return CFLOBVDD.representative(g, induced_value_tuple,
            n1.number_of_input_bits, number_of_output_bits)

    def ternary_apply_and_reduce(self, n2, n3, op, number_of_output_bits):
        assert isinstance(n2, CFLOBVDD) and isinstance(n3, CFLOBVDD)

        n1 = self

        assert n1.number_of_input_bits == n2.number_of_input_bits == n3.number_of_input_bits

        g, tt = n1.grouping.triple_product(n2.grouping, n3.grouping)

        equiv_classes = dict([(i,
            op(n1.outputs[tt[i][0]], n2.outputs[tt[i][1]], n3.outputs[tt[i][2]])) for i in tt])

        if CFLOBVDD.REDUCE:
            induced_value_tuple, induced_return_tuple = \
                CFLOBVDD.linear_collapse_classes_leftmost(equiv_classes)
            g = g.reduce(induced_return_tuple)
        else:
            induced_value_tuple = equiv_classes

        return CFLOBVDD.representative(g, induced_value_tuple,
            n1.number_of_input_bits, number_of_output_bits)

    def test():
        # projection test cases

        CFLOBVDD.projection(0, 0, 1, 1)

        CFLOBVDD.projection(1, 0, 1, 1)
        CFLOBVDD.projection(1, 1, 1, 1)

        CFLOBVDD.projection(1, 0, 1, 2)

        CFLOBVDD.projection(2, 0, 1, 1)
        CFLOBVDD.projection(2, 1, 1, 1)

        CFLOBVDD.projection(2, 0, 1, 2)
        CFLOBVDD.projection(2, 1, 1, 2)
        CFLOBVDD.projection(2, 2, 1, 2)

        CFLOBVDD.projection(2, 0, 2, 2)
        CFLOBVDD.projection(2, 1, 2, 2)
        CFLOBVDD.projection(2, 2, 2, 2)
        CFLOBVDD.projection(2, 3, 2, 2)

        # pairing test cases

        CFLOBVDD.projection(0, 0, 1, 1).grouping.pair_product(CFLOBVDD.projection(0, 0, 1, 1).grouping)

        CFLOBVDD.projection(1, 0, 1, 1).grouping.pair_product(CFLOBVDD.projection(1, 0, 1, 1).grouping)
        CFLOBVDD.projection(1, 0, 1, 1).grouping.pair_product(CFLOBVDD.projection(1, 1, 1, 1).grouping)
        CFLOBVDD.projection(1, 1, 1, 1).grouping.pair_product(CFLOBVDD.projection(1, 0, 1, 1).grouping)
        CFLOBVDD.projection(1, 1, 1, 1).grouping.pair_product(CFLOBVDD.projection(1, 1, 1, 1).grouping)

        CFLOBVDD.projection(1, 0, 1, 2).grouping.pair_product(CFLOBVDD.projection(1, 0, 1, 2).grouping)

        CFLOBVDD.projection(2, 0, 1, 1).grouping.pair_product(CFLOBVDD.projection(2, 0, 1, 1).grouping)
        CFLOBVDD.projection(2, 0, 1, 1).grouping.pair_product(CFLOBVDD.projection(2, 1, 1, 1).grouping)
        CFLOBVDD.projection(2, 1, 1, 1).grouping.pair_product(CFLOBVDD.projection(2, 1, 1, 1).grouping)
        CFLOBVDD.projection(2, 1, 1, 1).grouping.pair_product(CFLOBVDD.projection(2, 0, 1, 1).grouping)

        CFLOBVDD.projection(2, 0, 1, 2).grouping.pair_product(CFLOBVDD.projection(2, 0, 1, 2).grouping)
        CFLOBVDD.projection(2, 0, 1, 2).grouping.pair_product(CFLOBVDD.projection(2, 1, 1, 2).grouping)
        CFLOBVDD.projection(2, 0, 1, 2).grouping.pair_product(CFLOBVDD.projection(2, 2, 1, 2).grouping)
        CFLOBVDD.projection(2, 1, 1, 2).grouping.pair_product(CFLOBVDD.projection(2, 0, 1, 2).grouping)
        CFLOBVDD.projection(2, 1, 1, 2).grouping.pair_product(CFLOBVDD.projection(2, 1, 1, 2).grouping)
        CFLOBVDD.projection(2, 1, 1, 2).grouping.pair_product(CFLOBVDD.projection(2, 2, 1, 2).grouping)
        CFLOBVDD.projection(2, 2, 1, 2).grouping.pair_product(CFLOBVDD.projection(2, 0, 1, 2).grouping)
        CFLOBVDD.projection(2, 2, 1, 2).grouping.pair_product(CFLOBVDD.projection(2, 1, 1, 2).grouping)
        CFLOBVDD.projection(2, 2, 1, 2).grouping.pair_product(CFLOBVDD.projection(2, 2, 1, 2).grouping)
        CFLOBVDD.projection(2, 0, 2, 2).grouping.pair_product(CFLOBVDD.projection(2, 0, 2, 2).grouping)
        CFLOBVDD.projection(2, 0, 2, 2).grouping.pair_product(CFLOBVDD.projection(2, 1, 2, 2).grouping)
        CFLOBVDD.projection(2, 0, 2, 2).grouping.pair_product(CFLOBVDD.projection(2, 2, 2, 2).grouping)
        CFLOBVDD.projection(2, 0, 2, 2).grouping.pair_product(CFLOBVDD.projection(2, 3, 2, 2).grouping)
        CFLOBVDD.projection(2, 1, 2, 2).grouping.pair_product(CFLOBVDD.projection(2, 0, 2, 2).grouping)
        CFLOBVDD.projection(2, 1, 2, 2).grouping.pair_product(CFLOBVDD.projection(2, 1, 2, 2).grouping)
        CFLOBVDD.projection(2, 1, 2, 2).grouping.pair_product(CFLOBVDD.projection(2, 2, 2, 2).grouping)
        CFLOBVDD.projection(2, 1, 2, 2).grouping.pair_product(CFLOBVDD.projection(2, 3, 2, 2).grouping)
        CFLOBVDD.projection(2, 2, 2, 2).grouping.pair_product(CFLOBVDD.projection(2, 0, 2, 2).grouping)
        CFLOBVDD.projection(2, 2, 2, 2).grouping.pair_product(CFLOBVDD.projection(2, 1, 2, 2).grouping)
        CFLOBVDD.projection(2, 2, 2, 2).grouping.pair_product(CFLOBVDD.projection(2, 2, 2, 2).grouping)
        CFLOBVDD.projection(2, 2, 2, 2).grouping.pair_product(CFLOBVDD.projection(2, 3, 2, 2).grouping)
        CFLOBVDD.projection(2, 3, 2, 2).grouping.pair_product(CFLOBVDD.projection(2, 0, 2, 2).grouping)
        CFLOBVDD.projection(2, 3, 2, 2).grouping.pair_product(CFLOBVDD.projection(2, 1, 2, 2).grouping)
        CFLOBVDD.projection(2, 3, 2, 2).grouping.pair_product(CFLOBVDD.projection(2, 2, 2, 2).grouping)
        CFLOBVDD.projection(2, 3, 2, 2).grouping.pair_product(CFLOBVDD.projection(2, 3, 2, 2).grouping)

        # binary apply and reduce test cases

        CFLOBVDD.projection(0, 0, 1, 1).binary_apply_and_reduce(CFLOBVDD.projection(0, 0, 1, 1), lambda x, y: x == y, 1)

        CFLOBVDD.projection(1, 0, 1, 1).binary_apply_and_reduce(CFLOBVDD.projection(1, 0, 1, 1), lambda x, y: x == y, 1)
        CFLOBVDD.projection(1, 0, 1, 1).binary_apply_and_reduce(CFLOBVDD.projection(1, 1, 1, 1), lambda x, y: x == y, 1)
        CFLOBVDD.projection(1, 1, 1, 1).binary_apply_and_reduce(CFLOBVDD.projection(1, 0, 1, 1), lambda x, y: x == y, 1)
        CFLOBVDD.projection(1, 1, 1, 1).binary_apply_and_reduce(CFLOBVDD.projection(1, 1, 1, 1), lambda x, y: x == y, 1)

        CFLOBVDD.projection(1, 0, 1, 2).binary_apply_and_reduce(CFLOBVDD.projection(1, 0, 1, 2), lambda x, y: x == y, 1)

        CFLOBVDD.projection(2, 0, 1, 1).binary_apply_and_reduce(CFLOBVDD.projection(2, 0, 1, 1), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 0, 1, 1).binary_apply_and_reduce(CFLOBVDD.projection(2, 1, 1, 1), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 1, 1, 1).binary_apply_and_reduce(CFLOBVDD.projection(2, 1, 1, 1), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 1, 1, 1).binary_apply_and_reduce(CFLOBVDD.projection(2, 0, 1, 1), lambda x, y: x == y, 1)

        CFLOBVDD.projection(2, 0, 1, 2).binary_apply_and_reduce(CFLOBVDD.projection(2, 0, 1, 2), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 0, 1, 2).binary_apply_and_reduce(CFLOBVDD.projection(2, 1, 1, 2), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 0, 1, 2).binary_apply_and_reduce(CFLOBVDD.projection(2, 2, 1, 2), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 1, 1, 2).binary_apply_and_reduce(CFLOBVDD.projection(2, 0, 1, 2), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 1, 1, 2).binary_apply_and_reduce(CFLOBVDD.projection(2, 1, 1, 2), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 1, 1, 2).binary_apply_and_reduce(CFLOBVDD.projection(2, 2, 1, 2), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 2, 1, 2).binary_apply_and_reduce(CFLOBVDD.projection(2, 0, 1, 2), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 2, 1, 2).binary_apply_and_reduce(CFLOBVDD.projection(2, 1, 1, 2), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 2, 1, 2).binary_apply_and_reduce(CFLOBVDD.projection(2, 2, 1, 2), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 0, 2, 2).binary_apply_and_reduce(CFLOBVDD.projection(2, 0, 2, 2), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 0, 2, 2).binary_apply_and_reduce(CFLOBVDD.projection(2, 1, 2, 2), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 0, 2, 2).binary_apply_and_reduce(CFLOBVDD.projection(2, 2, 2, 2), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 0, 2, 2).binary_apply_and_reduce(CFLOBVDD.projection(2, 3, 2, 2), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 1, 2, 2).binary_apply_and_reduce(CFLOBVDD.projection(2, 0, 2, 2), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 1, 2, 2).binary_apply_and_reduce(CFLOBVDD.projection(2, 1, 2, 2), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 1, 2, 2).binary_apply_and_reduce(CFLOBVDD.projection(2, 2, 2, 2), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 1, 2, 2).binary_apply_and_reduce(CFLOBVDD.projection(2, 3, 2, 2), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 2, 2, 2).binary_apply_and_reduce(CFLOBVDD.projection(2, 0, 2, 2), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 2, 2, 2).binary_apply_and_reduce(CFLOBVDD.projection(2, 1, 2, 2), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 2, 2, 2).binary_apply_and_reduce(CFLOBVDD.projection(2, 2, 2, 2), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 2, 2, 2).binary_apply_and_reduce(CFLOBVDD.projection(2, 3, 2, 2), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 3, 2, 2).binary_apply_and_reduce(CFLOBVDD.projection(2, 0, 2, 2), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 3, 2, 2).binary_apply_and_reduce(CFLOBVDD.projection(2, 1, 2, 2), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 3, 2, 2).binary_apply_and_reduce(CFLOBVDD.projection(2, 2, 2, 2), lambda x, y: x == y, 1)
        CFLOBVDD.projection(2, 3, 2, 2).binary_apply_and_reduce(CFLOBVDD.projection(2, 3, 2, 2), lambda x, y: x == y, 1)

        # ternary apply and reduce test cases

        CFLOBVDD.projection(2, 0, 1, 1).ternary_apply_and_reduce(CFLOBVDD.projection(2, 1, 1, 1),
            CFLOBVDD.projection(2, 2, 1, 1), lambda x, y, z: y if x else z, 1)
        CFLOBVDD.projection(2, 1, 1, 1).ternary_apply_and_reduce(CFLOBVDD.projection(2, 2, 1, 1),
            CFLOBVDD.projection(2, 3, 1, 1), lambda x, y, z: y if x else z, 1)
        CFLOBVDD.projection(2, 0, 1, 1).ternary_apply_and_reduce(CFLOBVDD.projection(2, 2, 1, 1),
            CFLOBVDD.projection(2, 3, 1, 1), lambda x, y, z: y if x else z, 1)
        CFLOBVDD.projection(2, 0, 1, 1).ternary_apply_and_reduce(CFLOBVDD.projection(2, 2, 1, 1),
            CFLOBVDD.projection(2, 3, 1, 1), lambda x, y, z: y if x else z, 1)

        CFLOBVDD.projection(2, 0, 2, 2).ternary_apply_and_reduce(CFLOBVDD.projection(2, 1, 2, 2),
            CFLOBVDD.projection(2, 2, 2, 2), lambda x, y, z: y if x else z, 2)
        CFLOBVDD.projection(2, 1, 2, 2).ternary_apply_and_reduce(CFLOBVDD.projection(2, 2, 2, 2),
            CFLOBVDD.projection(2, 3, 2, 2), lambda x, y, z: y if x else z, 2)
        CFLOBVDD.projection(2, 0, 2, 2).ternary_apply_and_reduce(CFLOBVDD.projection(2, 2, 2, 2),
            CFLOBVDD.projection(2, 3, 2, 2), lambda x, y, z: y if x else z, 2)
        CFLOBVDD.projection(2, 0, 2, 2).ternary_apply_and_reduce(CFLOBVDD.projection(2, 2, 2, 2),
            CFLOBVDD.projection(2, 3, 2, 2), lambda x, y, z: y if x else z, 2)

        CFLOBVDD.projection(2, 0, 4, 4).ternary_apply_and_reduce(CFLOBVDD.projection(2, 1, 4, 4),
            CFLOBVDD.projection(2, 2, 4, 4), lambda x, y, z: y if x else z, 4)
        CFLOBVDD.projection(2, 1, 4, 4).ternary_apply_and_reduce(CFLOBVDD.projection(2, 2, 4, 4),
            CFLOBVDD.projection(2, 3, 4, 4), lambda x, y, z: y if x else z, 4)
        CFLOBVDD.projection(2, 0, 4, 4).ternary_apply_and_reduce(CFLOBVDD.projection(2, 2, 4, 4),
            CFLOBVDD.projection(2, 3, 4, 4), lambda x, y, z: y if x else z, 4)
        CFLOBVDD.projection(2, 0, 4, 4).ternary_apply_and_reduce(CFLOBVDD.projection(2, 2, 4, 4),
            CFLOBVDD.projection(2, 3, 4, 4), lambda x, y, z: y if x else z, 4)