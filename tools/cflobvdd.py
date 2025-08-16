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

import bvdd as BVDD

from math import log2
from math import ceil

class BV_Grouping:
    pair_product_cache = {}
    pair_product_cache_hits = 0

    triple_product_cache = {}
    triple_product_cache_hits = 0

    reduction_cache = {}
    reduction_cache_hits = 0

    def __init__(self, level, number_of_exits):
        assert level >= 0
        self.level = level
        self.fork_level = level
        self.number_of_exits = number_of_exits

    def __repr__(self):
        return f"{self.level} w/ {self.number_of_exits} exits"

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
                return 1, BV_No_Distinction_Proto.representative(self.level, self.fork_level)
            else:
                return reduction_length, self

class BV_Dont_Care_Grouping(BV_Grouping):
    representatives = None

    def __init__(self, fork_level):
        super().__init__(fork_level, 1)

    def __repr__(self):
        return "dontcare @ " + super().__repr__()

    def is_consistent(self):
        assert super().is_consistent()
        return True

    def number_of_connections(self):
        return 0

    def number_of_distinct_inputs(self, exit_i):
        assert exit_i == 1
        return 1

    def get_paths(self, exit_i, index_i = 0):
        assert exit_i == 1
        return [(index_i, 0)]

    def representative(fork_level):
        if BV_Dont_Care_Grouping.representatives is None:
            BV_Dont_Care_Grouping.representatives = BV_Dont_Care_Grouping(fork_level)
            assert BV_Dont_Care_Grouping.representatives.is_consistent()
        return BV_Dont_Care_Grouping.representatives

    def pair_product(self, g2, inorder = True):
        assert isinstance(g2, BV_Grouping)

        if inorder:
            g1 = self
        else:
            g1 = g2
            g2 = self

        if g1.is_pair_product_cached(g2):
            return g1.get_cached_pair_product(g2)

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
    # generalizing CFLOBDD forking to BVDDs
    representatives = {}
    representatives_hits = 0

    def __init__(self, level, number_of_exits, bvdd):
        super().__init__(level, number_of_exits)
        self.bvdd = bvdd

    def __repr__(self):
        indentation = " " * (CFLOBVDD.max_level - self.level + 1)
        return (indentation + "\n" +
            indentation + "fork @ " + super().__repr__() + ":\n" +
            indentation + f"{self.bvdd}")

    def __hash__(self):
        return hash((self.level, self.number_of_exits, self.bvdd))

    def __eq__(self, g2):
        return (isinstance(g2, BV_Fork_Grouping) and
            self.level == g2.level and
            self.number_of_exits == g2.number_of_exits and
            self.bvdd == g2.bvdd)

    def is_consistent(self):
        assert super().is_consistent()
        # TODO: assert len(self.bvdd.number_of_exits) == self.number_of_exits
        assert self.bvdd.is_consistent()
        return True

    def number_of_connections(self):
        return self.bvdd.number_of_connections()

    def number_of_distinct_inputs(self, exit_i):
        return self.bvdd.number_of_distinct_inputs(exit_i)

    def get_input_values(inputs):
        return BVDD.BVDD.get_input_values(inputs)

    def get_paths(self, exit_i, index_i = 0):
        assert 1 <= exit_i <= self.number_of_exits
        return self.bvdd.get_paths(exit_i, index_i)

    def representative(self):
        if self in BV_Fork_Grouping.representatives:
            BV_Fork_Grouping.representatives_hits += 1
        else:
            assert self.is_consistent()
            BV_Fork_Grouping.representatives[self] = self
        return BV_Fork_Grouping.representatives[self]

    def projection_proto(level, input_i):
        return BV_Fork_Grouping(level, 256, BVDD.BVDD.projection_proto(input_i)).representative()

    def pair_product(self, g2):
        assert isinstance(g2, BV_Grouping)

        g1 = self

        if g2.is_no_distinction_proto():
            return g2.pair_product(g1, False)
        else:
            if g1.is_pair_product_cached(g2):
                return g1.get_cached_pair_product(g2)

            assert isinstance(g2, BV_Fork_Grouping)

            g, pt = g1.bvdd.pair_product(g2.bvdd)

            return g1.cache_pair_product(g2,
                BV_Fork_Grouping(self.level, len(pt), g).representative(), pt)

    def triple_product(self, g2, g3):
        assert isinstance(g2, BV_Grouping) and isinstance(g3, BV_Grouping)

        g1 = self

        if g2.is_no_distinction_proto():
            return g2.triple_product(g1, g3, 2)
        elif g3.is_no_distinction_proto():
            return g3.triple_product(g1, g2, 3)
        else:
            if g1.is_triple_product_cached(g2, g3):
                return g1.get_cached_triple_product(g2, g3)

            assert isinstance(g2, BV_Fork_Grouping) and isinstance(g3, BV_Fork_Grouping)

            g, tt = g1.bvdd.triple_product(g2.bvdd, g3.bvdd)

            return g1.cache_triple_product(g2, g3,
                BV_Fork_Grouping(self.level, len(tt), g).representative(), tt)

    def reduce(self, reduction_tuple):
        reduction_length, reduction = super().reduce(reduction_tuple)

        if reduction_length == 1:
            return reduction
        else:
            if self.is_reduction_cached(reduction_tuple):
                return self.get_cached_reduction(reduction_tuple)

            bvdd = self.bvdd.reduce(reduction_tuple)

            if bvdd.is_dont_care():
                g = BV_Dont_Care_Grouping.representative(self.fork_level)
            else:
                g = BV_Fork_Grouping(self.level, reduction_length, bvdd).representative()

            assert g.number_of_exits == reduction_length

            return self.cache_reduction(reduction_tuple, g)

class BV_Internal_Grouping(BV_Grouping):
    representatives = {}
    representatives_hits = 0

    def __init__(self, level, fork_level, number_of_exits = 0):
        assert level > 0
        super().__init__(level, number_of_exits)
        assert 0 <= fork_level <= level
        self.fork_level = fork_level
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
            self.number_of_exits,
            self.a_connection,
            tuple(self.a_return_tuple.values()),
            self.number_of_b_connections,
            tuple(self.b_connections.values()),
            tuple([(tuple(rt), tuple(rt.values())) for rt in self.b_return_tuples.values()])))

    def __eq__(self, g2):
        return (isinstance(g2, BV_Internal_Grouping) and
            self.level == g2.level and
            self.number_of_exits == g2.number_of_exits and
            self.a_connection == g2.a_connection and
            self.a_return_tuple == g2.a_return_tuple and
            self.number_of_b_connections == g2.number_of_b_connections and
            self.b_connections == g2.b_connections and
            self.b_return_tuples == g2.b_return_tuples)

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

    def number_of_connections(self):
        g_a = self.a_connection
        count = g_a.number_of_connections()
        for g_b_i in self.b_connections:
            g_b = self.b_connections[g_b_i]
            count += g_b.number_of_connections()
        return count

    def number_of_distinct_inputs(self, exit_i):
        assert 1 <= exit_i <= self.number_of_exits
        count = 0
        g_a = self.a_connection
        for g_b_i in self.b_connections:
            g_b = self.b_connections[g_b_i]
            g_b_i_rt = self.b_return_tuples[g_b_i]
            for g_b_i_rt_e_j in g_b_i_rt:
                if exit_i == g_b_i_rt[g_b_i_rt_e_j]:
                    count += (g_a.number_of_distinct_inputs(g_b_i) *
                        g_b.number_of_distinct_inputs(g_b_i_rt_e_j))
        return count

    def get_paths(self, exit_i, index_i = 0):
        inputs = []
        for b_i in self.b_return_tuples:
            b_rt = self.b_return_tuples[b_i]
            for b_e_i in b_rt:
                if exit_i == b_rt[b_e_i]:
                    inputs += [(self.a_connection.get_paths(b_i, index_i),
                        self.b_connections[b_i].get_paths(b_e_i, index_i + 2**(self.level - 1)))]
                    break
        return inputs

    def representative(self):
        if self in BV_Internal_Grouping.representatives:
            BV_Internal_Grouping.representatives_hits += 1
        else:
            assert self.is_consistent()
            BV_Internal_Grouping.representatives[self] = self
        return BV_Internal_Grouping.representatives[self]

    def projection_proto(level, fork_level, input_i):
        # generalizing CFLOBDD projection to CFLOBVDD projection
        assert 0 <= input_i < 2**level
        if level == fork_level:
            return BV_Fork_Grouping.projection_proto(level, input_i)
        else:
            g = BV_Internal_Grouping(level, fork_level, 256)

            if input_i < 2**(level - 1):
                g.a_connection = BV_Internal_Grouping.projection_proto(level - 1, fork_level,
                    input_i)
                # g.a_return_tuple == {} representing g.a_return_tuple = dict([(e, e)
                    # for e in range(1, 256 + 1)])

                g.number_of_b_connections = 256

                projection_proto = BV_No_Distinction_Proto.representative(level - 1, fork_level)

                g.b_connections = dict([(c, projection_proto) for c in range(1, 256 + 1)])
                g.b_return_tuples = dict([(e, {1:e}) for e in range(1, 256 + 1)])
            else:
                g.a_connection = BV_No_Distinction_Proto.representative(level - 1, fork_level)
                # g.a_return_tuple == {} representing g.a_return_tuple[1] = 1

                g.number_of_b_connections = 1

                projection_proto = BV_Internal_Grouping.projection_proto(level - 1, fork_level,
                    input_i - 2**(level - 1))

                g.b_connections = {1:projection_proto}
                g.b_return_tuples = {1:dict([(e, e) for e in range(1, 256 + 1)])}

            return g.representative()

    def pair_product(self, g2):
        assert isinstance(g2, BV_Grouping)

        g1 = self

        assert g1.level == g2.level

        if g2.is_no_distinction_proto():
            return g2.pair_product(g1, False)
        else:
            if g1.is_pair_product_cached(g2):
                return g1.get_cached_pair_product(g2)

            assert isinstance(g2, BV_Internal_Grouping)

            g_a, pt_a = g1.a_connection.pair_product(g2.a_connection)

            g = BV_Internal_Grouping(g1.level, g1.fork_level)

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

        if g2.is_no_distinction_proto():
            return g2.triple_product(g1, g3, 2)
        elif g3.is_no_distinction_proto():
            return g3.triple_product(g1, g2, 3)
        else:
            if g1.is_triple_product_cached(g2, g3):
                return g1.get_cached_triple_product(g2, g3)

            assert isinstance(g2, BV_Internal_Grouping) and isinstance(g3, BV_Internal_Grouping)

            g_a, tt_a = g1.a_connection.triple_product(g2.a_connection, g3.a_connection)

            g = BV_Internal_Grouping(g1.level, g1.fork_level)

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

            g_prime = BV_Internal_Grouping(g.level, g.fork_level, reduction_length)

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

    def __init__(self, level, fork_level):
        assert level > 0
        assert 0 <= fork_level <= level
        super().__init__(level, fork_level, 1)

    def representative(level, fork_level):
        if level == fork_level:
            return BV_Dont_Care_Grouping.representative(fork_level)
        elif level in BV_No_Distinction_Proto.representatives:
            BV_No_Distinction_Proto.representatives_hits += 1
            return BV_No_Distinction_Proto.representatives[level]
        else:
            g = BV_No_Distinction_Proto(level, fork_level)

            g.a_connection = BV_No_Distinction_Proto.representative(level - 1, fork_level)
            # g.a_return_tuple == {} representing g.a_return_tuple[1] = 1

            g.number_of_b_connections = 1
            g.b_connections[1] = g.a_connection
            g.b_return_tuples[1] = {1:1}

            BV_No_Distinction_Proto.representatives[level] = g

            return g

    def pair_product(self, g2, inorder = True):
        assert isinstance(g2, BV_Grouping)

        g1 = self

        assert g1.level == g2.level

        return BV_Dont_Care_Grouping.pair_product(g1, g2, inorder)

    def triple_product(self, g2, g3, order = 1):
        assert isinstance(g2, BV_Grouping) and isinstance(g3, BV_Grouping)

        g1 = self

        assert g1.level == g2.level == g3.level

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

    def __init__(self, grouping, outputs):
        self.grouping = grouping
        self.outputs = outputs

    def __str__(self):
        return ("CFLOBVDD with\n" +
            f"g: {self.grouping}\n" +
            f"o: {self.outputs}\n")

    def __hash__(self):
        return hash((self.grouping, tuple(self.outputs.values())))

    def __eq__(self, n2):
        return (isinstance(n2, CFLOBVDD) and
            self.grouping == n2.grouping and
            self.outputs == n2.outputs)

    def print_profile():
        print(f"BV_Fork_Grouping cache utilization: {BVDD.utilization(BV_Fork_Grouping.representatives_hits, len(BV_Fork_Grouping.representatives))}")
        print(f"BV_Internal_Grouping cache utilization: {BVDD.utilization(BV_Internal_Grouping.representatives_hits, len(BV_Internal_Grouping.representatives))}")
        print(f"BV_No_Distinction_Proto cache utilization: {BVDD.utilization(BV_No_Distinction_Proto.representatives_hits, len(BV_No_Distinction_Proto.representatives))}")
        print(f"BV_Grouping pair-product cache utilization: {BVDD.utilization(BV_Grouping.pair_product_cache_hits, len(BV_Grouping.pair_product_cache))}")
        print(f"BV_Grouping triple-product cache utilization: {BVDD.utilization(BV_Grouping.triple_product_cache_hits, len(BV_Grouping.triple_product_cache))}")
        print(f"BV_Grouping reduction cache utilization: {BVDD.utilization(BV_Grouping.reduction_cache_hits, len(BV_Grouping.reduction_cache))}")
        print(f"CFLOBVDD collapsed-equivalence-classes cache utilization: {BVDD.utilization(Collapsed_Classes.cache_hits, len(Collapsed_Classes.cache))}")
        print(f"CFLOBVDD cache utilization: {BVDD.utilization(CFLOBVDD.representatives_hits, len(CFLOBVDD.representatives))}")

    def number_of_connections(self):
        return self.grouping.number_of_connections()

    def number_of_outputs(self):
        return len(self.outputs)

    def number_of_distinct_outputs(self):
        return len(set(self.outputs.values()))

    def number_of_distinct_inputs(self):
        return sum(self.grouping.number_of_distinct_inputs(exit_i) for exit_i in self.outputs)

    def number_of_solutions(self, value):
        return sum(self.grouping.number_of_distinct_inputs(exit_i)
            for exit_i in self.outputs if self.outputs[exit_i] == value)

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
            f"{2**self.grouping.level} input variables\n" +
            f"{self.number_of_connections()} connections\n" +
            f"{self.number_of_outputs()} output values\n" +
            f"{self.number_of_distinct_outputs()} disctinct output values\n"
            f"{self.number_of_distinct_inputs()} distinct inputs\n" +
            f"{self.number_of_solutions(value)} solutions\n" +
            f"{self.get_printed_value_paths(value)}")

    def is_consistent(self):
        assert self.grouping.is_consistent()
        assert self.number_of_outputs() == self.grouping.number_of_exits, f"{self.number_of_outputs()} == {self.grouping.number_of_exits}"
        assert self.number_of_outputs() >= self.number_of_distinct_outputs()
        assert not CFLOBVDD.REDUCE or self.number_of_outputs() == self.number_of_distinct_outputs()
        return True

    def representative(grouping, outputs):
        cflobvdd = CFLOBVDD(grouping, outputs)
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

    def constant(level, fork_level, output = 0):
        CFLOBVDD.max_level = max(CFLOBVDD.max_level, level)
        return CFLOBVDD.representative(
            BV_No_Distinction_Proto.representative(level, fork_level), {1:output})

    def byte_constant(level, fork_level, number_of_input_bytes, output):
        assert number_of_input_bytes > 0
        level = max(level, fork_level, ceil(log2(number_of_input_bytes)))
        return CFLOBVDD.constant(level, fork_level, output)

    def false(level, fork_level):
        return CFLOBVDD.constant(level, fork_level, False)

    def true(level, fork_level):
        return CFLOBVDD.constant(level, fork_level, True)

    def flip_value_tuple(self):
        # self must be reduced
        assert self.number_of_outputs() == 2
        return CFLOBVDD.representative(self.grouping, {1:self.outputs[2], 2:self.outputs[1]})

    def complement(self):
        if self == CFLOBVDD.false(self.grouping.level, self.grouping.fork_level):
            return CFLOBVDD.true(self.grouping.level, self.grouping.fork_level)
        elif self == CFLOBVDD.true(self.grouping.level, self.grouping.fork_level):
            return CFLOBVDD.false(self.grouping.level, self.grouping.fork_level)
        else:
            # self must be reduced
            return self.flip_value_tuple()

    def unary_apply_and_reduce(self, op, number_of_output_bits):
        return self.binary_apply_and_reduce(
            CFLOBVDD.constant(self.grouping.level, self.grouping.fork_level),
            lambda x, y: op(x),
            number_of_output_bits)

    def projection(level, fork_level, input_i):
        assert 0 <= fork_level <= level
        assert 0 <= input_i < 2**level
        CFLOBVDD.max_level = max(CFLOBVDD.max_level, level)
        return CFLOBVDD.representative(
            BV_Internal_Grouping.projection_proto(level, fork_level, input_i),
            dict([(output + 1, output) for output in range(256)]))

    def byte_projection(level, fork_level, number_of_input_bytes, byte_i):
        assert 0 <= byte_i < number_of_input_bytes
        level = max(level, fork_level, ceil(log2(number_of_input_bytes)))
        return CFLOBVDD.projection(level, fork_level, byte_i)

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

        g, pt = n1.grouping.pair_product(n2.grouping)

        equiv_classes = dict([(i, op(n1.outputs[pt[i][0]], n2.outputs[pt[i][1]])) for i in pt])

        assert all(0 <= equiv_classes[i] < 2**number_of_output_bits for i in pt)

        if CFLOBVDD.REDUCE:
            induced_value_tuple, induced_return_tuple = \
                CFLOBVDD.linear_collapse_classes_leftmost(equiv_classes)
            g = g.reduce(induced_return_tuple)
        else:
            induced_value_tuple = equiv_classes

        return CFLOBVDD.representative(g, induced_value_tuple)

    def ternary_apply_and_reduce(self, n2, n3, op, number_of_output_bits):
        assert isinstance(n2, CFLOBVDD) and isinstance(n3, CFLOBVDD)

        n1 = self

        g, tt = n1.grouping.triple_product(n2.grouping, n3.grouping)

        equiv_classes = dict([(i,
            op(n1.outputs[tt[i][0]], n2.outputs[tt[i][1]], n3.outputs[tt[i][2]])) for i in tt])

        assert all(0 <= equiv_classes[i] < 2**number_of_output_bits for i in tt)

        if CFLOBVDD.REDUCE:
            induced_value_tuple, induced_return_tuple = \
                CFLOBVDD.linear_collapse_classes_leftmost(equiv_classes)
            g = g.reduce(induced_return_tuple)
        else:
            induced_value_tuple = equiv_classes

        return CFLOBVDD.representative(g, induced_value_tuple)