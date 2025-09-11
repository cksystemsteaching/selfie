#!/usr/bin/env python3

# Copyright (c) the Selfie Project authors. All rights reserved.
# Please see the AUTHORS file for details. Use of this source code is
# governed by a BSD license that can be found in the LICENSE file.

# Selfie is a project of the Computational Systems Group at the
# Department of Computer Sciences of the University of Salzburg
# in Austria. For further information and code please refer to:

# selfie.cs.uni-salzburg.at

# Context-free language ordered bitvector decision diagrams (CFLOBVDDs)

# CFLOBVDDs generalize CFLOBDDs in two ways:

# CFLOBVDDs are CFLOBDDs over multi-node bitvector decision diagrams (BVDDs)
# rather than single-node BDDs. A single node of a BVDD maps a bitvector of
# size n, rather than just one bit, to no more than 2^n different values,
# rather than just to no more than two different values. Hence a tree of
# BVDD nodes of depth f maps a bitvector of size n*2^f bits to no more
# than 2^(n*2^f) different values. A CFLOBVDD of depth l>=f over BVDDs
# (mapping n*2^f-bit bitvectors) maps a bitvector of size n*2^(l-f) bits
# to no more than 2^(n*2^(l-f)) different values.

# CFLOBVDDs are kept minimal with respect to all recursively pairwise
# reorderings of BVDDs in CFLOBVDDs (out of the factorially many possible
# reorderings). Reorderings are explored from CFLOBVDD root nodes down to
# a configurable level called swap level. CFLOBVDDs are initialized with
# single-node BVDDs at level 0 which may then grow to a configurable level
# called fork level (downsampling). If the swap level is less than the
# fork level, BVDDs may be split in half recursively down to swap level
# to explore reorderings (upsampling).

# ------------------------------------------------------------

import bvdd as BVDD

from math import log2
from math import ceil

import threading

class BV_Grouping:
    NO_SWAP_CACHING = True
    swap_cache_lock = threading.Lock()
    swap_cache = {}
    swap_cache_hits = 0

    NO_UPSAMPLE_CACHING = False
    upsample_cache_lock = threading.Lock()
    upsample_cache = {}
    upsample_cache_hits = 0

    NO_DOWNSAMPLE_CACHING = False
    downsample_cache_lock = threading.Lock()
    downsample_cache = {}
    downsample_cache_hits = 0

    NO_COMPRESSED_CACHING = False
    compressed_cache_lock = threading.Lock()
    compressed_cache = {}
    compressed_cache_hits = 0

    NO_PAIR_CACHING = False
    pair_product_cache_lock = threading.Lock()
    pair_product_cache = {}
    pair_product_cache_hits = 0

    NO_TRIPLE_CACHING = False
    triple_product_cache_lock = threading.Lock()
    triple_product_cache = {}
    triple_product_cache_hits = 0

    NO_REDUCTION_CACHING = False
    reduction_cache_lock = threading.Lock()
    reduction_cache = {}
    reduction_cache_hits = 0

    NO_CLASSES_CACHING = False
    NO_REPRESENTATIVES = False

    def __init__(self, level, number_of_exits):
        assert level >= 0
        self.level = level
        self.swap_level = level
        self.fork_level = level
        self.number_of_exits = number_of_exits

    def __repr__(self):
        return f"{self.level} w/ {self.number_of_exits} exits"

    def is_consistent(self):
        assert self.number_of_exits > 0
        return True

    def is_swap_cached(self):
        if self in BV_Grouping.swap_cache:
            BV_Grouping.swap_cache_hits += 1
            return True
        else:
            return False

    def get_cached_swap(self):
        assert self.is_swap_cached()
        return BV_Grouping.swap_cache[self]

    def cache_swap(self, g):
        if BV_Grouping.NO_SWAP_CACHING:
            return g
        with BV_Grouping.swap_cache_lock:
            if self not in BV_Grouping.swap_cache:
                BV_Grouping.swap_cache[self] = g
                # swapping is involutory (self-inverse) but only modulo compression
        return BV_Grouping.swap_cache[self]

    def is_upsample_cached(self):
        if self in BV_Grouping.upsample_cache:
            BV_Grouping.upsample_cache_hits += 1
            return True
        else:
            return False

    def get_cached_upsample(self):
        assert self.is_upsample_cached()
        return BV_Grouping.upsample_cache[self]

    def cache_upsample(self, g):
        if BV_Grouping.NO_UPSAMPLE_CACHING:
            return g
        with BV_Grouping.upsample_cache_lock:
            if self not in BV_Grouping.upsample_cache:
                BV_Grouping.upsample_cache[self] = g
        return BV_Grouping.upsample_cache[self]

    def is_downsample_cached(self):
        if self in BV_Grouping.downsample_cache:
            BV_Grouping.downsample_cache_hits += 1
            return True
        else:
            return False

    def get_cached_downsample(self):
        assert self.is_downsample_cached()
        return BV_Grouping.downsample_cache[self]

    def cache_downsample(self, g):
        if BV_Grouping.NO_DOWNSAMPLE_CACHING:
            return g
        with BV_Grouping.downsample_cache_lock:
            if self not in BV_Grouping.downsample_cache:
                BV_Grouping.downsample_cache[self] = g
        return BV_Grouping.downsample_cache[self]

    def downsample(self):
        assert self.level <= self.fork_level

        if self.is_downsample_cached():
            return self.get_cached_downsample()

        g = self.downsample_uncached()

        # downsampling is inverse of upsampling: assert self is g.upsample_uncached()

        return self.cache_downsample(g)

    def is_compressed_cached(self):
        if self in BV_Grouping.compressed_cache:
            BV_Grouping.compressed_cache_hits += 1
            return True
        else:
            return False

    def get_cached_compressed(self):
        assert self.is_compressed_cached()
        return BV_Grouping.compressed_cache[self]

    def cache_compressed(self, g):
        if BV_Grouping.NO_COMPRESSED_CACHING:
            return g
        with BV_Grouping.compressed_cache_lock:
            if self not in BV_Grouping.compressed_cache:
                BV_Grouping.compressed_cache[self] = g
        return BV_Grouping.compressed_cache[self]

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
        if BV_Grouping.NO_PAIR_CACHING:
            return (pair_product, pt_ans)
        with BV_Grouping.pair_product_cache_lock:
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

    def cache_triple_product(self, g2, g3, triple_product, tt_ans):
        if BV_Grouping.NO_TRIPLE_CACHING:
            return (triple_product, tt_ans)
        with BV_Grouping.triple_product_cache_lock:
            if (self, g2, g3) not in BV_Grouping.triple_product_cache:
                BV_Grouping.triple_product_cache[(self, g2, g3)] = (triple_product, tt_ans)
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
        if BV_Grouping.NO_REDUCTION_CACHING:
            return reduction
        reduction_hash = BV_Grouping.reduction_hash(reduction_tuple)
        with BV_Grouping.reduction_cache_lock:
            if (self, reduction_hash) not in BV_Grouping.reduction_cache:
                BV_Grouping.reduction_cache[(self, reduction_hash)] = reduction
        return BV_Grouping.reduction_cache[(self, reduction_hash)]

    def is_no_distinction_proto(self):
        return (isinstance(self, BV_Dont_Care_Grouping) or
            isinstance(self, BV_No_Distinction_Proto))

    def reduce(self, reduction_tuple):
        assert len(reduction_tuple) == self.number_of_exits
        if reduction_tuple == dict(enumerate(range(1, len(reduction_tuple) + 1), 1)):
            return 1, self
        else:
            reduction_length = len(set(reduction_tuple.values()))
            if reduction_length == 1:
                return 1, BV_No_Distinction_Proto.representative(self.level,
                    self.swap_level, self.fork_level)
            else:
                return reduction_length, self

class BV_Dont_Care_Grouping(BV_Grouping):
    representatives_lock = threading.Lock()
    representatives = None

    def __init__(self):
        super().__init__(0, 1)

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

    def representative():
        if BV_Grouping.NO_REPRESENTATIVES:
            return BV_Dont_Care_Grouping()
        if BV_Dont_Care_Grouping.representatives is None:
            with BV_Dont_Care_Grouping.representatives_lock:
                if BV_Dont_Care_Grouping.representatives is None:
                    BV_Dont_Care_Grouping.representatives = BV_Dont_Care_Grouping()
                    assert BV_Dont_Care_Grouping.representatives.is_consistent()
        return BV_Dont_Care_Grouping.representatives

    def downsample_uncached(self):
        return BV_No_Distinction_Proto.downsample_uncached(self)

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
            g = g2
            pt_ans = dict([(k, (1, k)) for k in range(1, g2.number_of_exits + 1)])
        else:
            g = g1
            pt_ans = dict([(k, (k, 1)) for k in range(1, g1.number_of_exits + 1)])

        return g1.cache_pair_product(g2, g, pt_ans)

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
            g = g3
            tt_ans = dict([(k, (1, 1, k)) for k in range(1, g3.number_of_exits + 1)])
        elif g1.is_no_distinction_proto() and g3.is_no_distinction_proto():
            g = g2
            tt_ans = dict([(k, (1, k, 1)) for k in range(1, g2.number_of_exits + 1)])
        elif g2.is_no_distinction_proto() and g3.is_no_distinction_proto():
            g = g1
            tt_ans = dict([(k, (k, 1, 1)) for k in range(1, g1.number_of_exits + 1)])
        elif g1.is_no_distinction_proto():
            g, pt = g2.pair_product(g3)
            tt_ans = dict([(jk, (1, pt[jk][0], pt[jk][1])) for jk in pt])
        elif g2.is_no_distinction_proto():
            g, pt = g1.pair_product(g3)
            tt_ans = dict([(jk, (pt[jk][0], 1, pt[jk][1])) for jk in pt])
        else:
            assert g3.is_no_distinction_proto()
            g, pt = g1.pair_product(g2)
            tt_ans = dict([(jk, (pt[jk][0], pt[jk][1], 1)) for jk in pt])

        return g1.cache_triple_product(g2, g3, g, tt_ans)

    def reduce(self, reduction_tuple):
        assert reduction_tuple == {1:1}
        return self

    def compress(self):
        return self

class BV_Fork_Grouping(BV_Grouping):
    # generalizing CFLOBDD forking to BVDDs
    representatives_lock = threading.Lock()
    representatives = {}
    representatives_hits = 0

    def __init__(self, level, swap_level, fork_level, number_of_exits, bvdd):
        super().__init__(level, number_of_exits)
        assert 0 <= swap_level
        assert 0 <= fork_level
        self.swap_level = swap_level
        self.fork_level = fork_level
        self.bvdd = bvdd

    def __repr__(self):
        indentation = " " * (CFLOBVDD.max_level - self.level + 1)
        return (indentation + "\n" +
            indentation + "fork @ " + super().__repr__() + ":\n" +
            indentation + f"{self.bvdd}")

    def __hash__(self):
        return hash((self.level, self.swap_level, self.fork_level, self.number_of_exits, self.bvdd))

    def __eq__(self, g2):
        return (isinstance(g2, BV_Fork_Grouping) and
            self.level == g2.level and
            self.swap_level == g2.swap_level and
            self.fork_level == g2.fork_level and
            self.number_of_exits == g2.number_of_exits and
            self.bvdd == g2.bvdd)

    def is_consistent(self):
        assert super().is_consistent()
        assert self.bvdd.is_consistent()
        assert self.bvdd.number_of_exits() == self.number_of_exits
        return True

    def number_of_connections(self):
        # counting CFLOBVDD connections only
        return 0

    def number_of_distinct_inputs(self, exit_i):
        return self.bvdd.number_of_distinct_inputs(exit_i)

    def get_input_values(inputs):
        return BVDD.BVDD.get_input_values(inputs)

    def get_paths(self, exit_i, index_i = 0):
        assert 1 <= exit_i <= self.number_of_exits
        return self.bvdd.get_paths(exit_i, index_i)

    def representative(self):
        if BV_Grouping.NO_REPRESENTATIVES:
            return self
        if self in BV_Fork_Grouping.representatives:
            BV_Fork_Grouping.representatives_hits += 1
        else:
            with BV_Fork_Grouping.representatives_lock:
                if self not in BV_Fork_Grouping.representatives:
                    assert self.is_consistent()
                    BV_Fork_Grouping.representatives[self] = self
        return BV_Fork_Grouping.representatives[self]

    def projection_proto(level, swap_level, fork_level):
        assert level == 0
        bvdd = BVDD.BVDD.projection_proto(0)
        return BV_Fork_Grouping(level, swap_level, fork_level,
            bvdd.number_of_exits(), bvdd).representative()

    def upsample_uncached(self):
        g_a_bvdd, g_a_rt_inv, g_b_rt_inv, g_b_bvdds, g_b_return_tuples = self.bvdd.upsample(self.level)

        assert g_a_bvdd.number_of_exits() == len(g_a_rt_inv)

        if self.level == 0:
            if g_a_bvdd.is_constant():
                return BV_Dont_Care_Grouping.representative()
            else:
                return self

        # TODO: enable different input orderings
        g = BV_Internal_Grouping(self.level, self.swap_level, self.fork_level, True, len(g_b_rt_inv))

        if g_a_bvdd.is_constant():
            g.a_connection = BV_No_Distinction_Proto.representative(self.level - 1,
                self.swap_level, self.fork_level)
        else:
            g.a_connection = BV_Fork_Grouping(self.level - 1, self.swap_level, self.fork_level,
                g_a_bvdd.number_of_exits(), g_a_bvdd).representative()

        assert g.a_connection.number_of_exits == len(g_b_bvdds)

        g.number_of_b_connections = g.a_connection.number_of_exits

        g.b_connections = {}

        for g_b_i in g_b_bvdds:
            if g_b_bvdds[g_b_i].is_constant():
                g_b = BV_No_Distinction_Proto.representative(self.level - 1,
                    self.swap_level, self.fork_level)
            else:
                g_b = BV_Fork_Grouping(self.level - 1, self.swap_level, self.fork_level,
                    g_b_bvdds[g_b_i].number_of_exits(), g_b_bvdds[g_b_i]).representative()
            g.b_connections[g_b_i] = g_b

            assert g_b.number_of_exits == len(g_b_return_tuples[g_b_i])

        g.b_return_tuples = g_b_return_tuples

        if (g.a_connection.is_no_distinction_proto() and
            g.number_of_b_connections == 1 and
            g.b_connections[1].is_no_distinction_proto()):
            return BV_No_Distinction_Proto.representative(self.level, self.swap_level, self.fork_level)
        else:
            return g.representative()

    def upsample(self):
        if self.is_upsample_cached():
            return self.get_cached_upsample()

        g = self.upsample_uncached()

        # upsampling is inverse of downsampling: assert self is g.downsample_uncached()

        return self.cache_upsample(g)

    def downsample(self):
        assert self.level <= self.fork_level
        return self

    def pair_product(self, g2):
        assert isinstance(g2, BV_Grouping)

        g1 = self

        if g2.is_no_distinction_proto():
            return g2.pair_product(g1, False)
        else:
            g1_orig = g1
            g2_orig = g2

            if g1_orig.is_pair_product_cached(g2_orig):
                return g1_orig.get_cached_pair_product(g2_orig)

            if g1.level > g1.swap_level:
                if isinstance(g2, BV_Internal_Grouping):
                    g, pt = g1.upsample().pair_product(g2)
                    return g1_orig.cache_pair_product(g2_orig, g, pt)
                else:
                    pass
                    # TODO: align g1 and g2 when forks support different input orderings
            elif isinstance(g2, BV_Internal_Grouping):
                g2 = g2.downsample()

            assert isinstance(g2, BV_Fork_Grouping)

            # assert g1 and g2 are aligned

            bvdd, pt = g1.bvdd.pair_product(g2.bvdd)

            g = BV_Fork_Grouping(g1.level, g1.swap_level, g1.fork_level, len(pt), bvdd)

            return g1_orig.cache_pair_product(g2_orig, g.representative(), pt)

    def triple_product(self, g2, g3):
        assert isinstance(g2, BV_Grouping) and isinstance(g3, BV_Grouping)

        g1 = self

        if g2.is_no_distinction_proto():
            return g2.triple_product(g1, g3, 2)
        elif g3.is_no_distinction_proto():
            return g3.triple_product(g1, g2, 3)
        else:
            g1_orig = g1
            g2_orig = g2
            g3_orig = g3

            if g1_orig.is_triple_product_cached(g2_orig, g3_orig):
                return g1_orig.get_cached_triple_product(g2_orig, g3_orig)

            if g1.level > g1.swap_level:
                if isinstance(g2, BV_Internal_Grouping):
                    if isinstance(g3, BV_Fork_Grouping):
                        g3 = g3.upsample()
                    assert isinstance(g3, BV_Internal_Grouping)
                    g, tt = g1.upsample().triple_product(g2, g3)
                    return g1_orig.cache_triple_product(g2_orig, g3_orig, g, tt)
                elif isinstance(g3, BV_Internal_Grouping):
                    assert isinstance(g2, BV_Fork_Grouping)
                    g, tt = g1.upsample().triple_product(g2.upsample(), g3)
                    return g1_orig.cache_triple_product(g2_orig, g3_orig, g, tt)
                else:
                    pass
                    # TODO: align g1, g2, g3 when forks support different input orderings
            else:
                if isinstance(g2, BV_Internal_Grouping):
                    g2 = g2.downsample()
                if isinstance(g3, BV_Internal_Grouping):
                    g3 = g3.downsample()

            assert isinstance(g2, BV_Fork_Grouping) and isinstance(g3, BV_Fork_Grouping)

            # assert g1, g2, g3 are aligned

            bvdd, tt = g1.bvdd.triple_product(g2.bvdd, g3.bvdd)

            g = BV_Fork_Grouping(g1.level, g1.swap_level, g1.fork_level, len(tt), bvdd)

            return g1_orig.cache_triple_product(g2_orig, g3_orig, g.representative(), tt)

    def reduce(self, reduction_tuple):
        reduction_length, reduction = super().reduce(reduction_tuple)

        if reduction_length == 1:
            return reduction
        else:
            if self.is_reduction_cached(reduction_tuple):
                return self.get_cached_reduction(reduction_tuple)

            bvdd = self.bvdd.reduce(reduction_tuple)

            if bvdd.is_constant():
                g = No_Distinction_Proto.representative(self.level,
                    self.swap_level, self.fork_level)
            else:
                g = BV_Fork_Grouping(self.level, self.swap_level, self.fork_level,
                    reduction_length, bvdd).representative()

            assert g.number_of_exits == reduction_length

            return self.cache_reduction(reduction_tuple, g)

    def compress(self):
        # equivalent to pair_product of No_Distinction_Proto with self where
        # pair_product for No_Distinction_Proto actually traverses its connections
        # (except for final downsampling as BVDDs do not yet different input orderings)

        if self.level == self.swap_level:
            return self

        assert self.level > self.swap_level

        if self.is_compressed_cached():
            return self.get_cached_compressed()

        g = self.upsample().compress()

        # TODO: enable when forks support different input orderings
        # if self.level <= self.fork_level:
        #     g = g.downsample()

        return self.cache_compressed(g)

class BV_Internal_Grouping(BV_Grouping):
    representatives_lock = threading.Lock()
    representatives = {}
    representatives_hits = 0

    def __init__(self, level, swap_level, fork_level, a2b, number_of_exits = 0):
        assert level > 0
        super().__init__(level, number_of_exits)
        assert 0 <= swap_level
        assert 0 <= fork_level
        self.swap_level = swap_level
        self.fork_level = fork_level
        self.a2b = a2b
        self.a_connection = None
        self.a_return_tuple = {}
        self.number_of_b_connections = 0
        self.b_connections = {}
        self.b_return_tuples = {}

    def __repr__(self):
        indentation = " " * (CFLOBVDD.max_level - self.level + 1)
        return (indentation + "\n" +
            indentation + f"{type(self).__name__} @ " + super().__repr__() + ":\n" +
            indentation + f"a2b: {self.a2b}\n" +
            indentation + f"a_c: {self.a_connection}\n" +
            indentation + f"a_rt: {self.a_return_tuple}\n" +
            indentation + f"n_of_b: {self.number_of_b_connections}\n" +
            indentation + f"b_c: {self.b_connections}\n" +
            indentation + f"b_rt: {self.b_return_tuples}")

    def __hash__(self):
        return hash((self.level,
            self.number_of_exits,
            self.a2b,
            self.a_connection,
            tuple(self.a_return_tuple.values()),
            self.number_of_b_connections,
            tuple(self.b_connections.values()),
            tuple([(tuple(rt), tuple(rt.values())) for rt in self.b_return_tuples.values()])))

    def __eq__(self, g2):
        return (isinstance(g2, BV_Internal_Grouping) and
            self.level == g2.level and
            self.number_of_exits == g2.number_of_exits and
            self.a2b == g2.a2b and
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
        n = 0
        for g_b_i in self.b_connections:
            g_b = self.b_connections[g_b_i]
            assert g_b_i in self.b_return_tuples
            g_b_i_rt = self.b_return_tuples[g_b_i]
            assert len(g_b_i_rt) == len(set(g_b_i_rt.values()))
            max_g_b_i_rt_e_j_e_t = n
            for g_b_i_rt_e_j in g_b_i_rt:
                assert 1 <= g_b_i_rt_e_j <= g_b.number_of_exits
                g_b_i_rt_e_j_e_t = g_b_i_rt[g_b_i_rt_e_j]
                assert 1 <= g_b_i_rt_e_j_e_t <= self.number_of_exits
                if g_b_i_rt_e_j_e_t > max_g_b_i_rt_e_j_e_t:
                    # TODO: canonicalize swapped groupings and then check consistency here
                    max_g_b_i_rt_e_j_e_t = g_b_i_rt_e_j_e_t
            n = max(n, max_g_b_i_rt_e_j_e_t)
        return True

    def number_of_connections(self):
        g_a = self.a_connection
        count = g_a.number_of_connections() + g_a.number_of_exits
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
        assert 1 <= exit_i <= self.number_of_exits
        if self.a2b:
            a_index_i = index_i
            b_index_i = index_i + 2**(self.level - 1)
        else:
            a_index_i = index_i + 2**(self.level - 1)
            b_index_i = index_i
        inputs = []
        for b_i in self.b_return_tuples:
            b_rt = self.b_return_tuples[b_i]
            for b_e_i in b_rt:
                if exit_i == b_rt[b_e_i]:
                    inputs += [(self.a_connection.get_paths(b_i, a_index_i),
                        self.b_connections[b_i].get_paths(b_e_i, b_index_i))]
                    break
        return inputs

    def representative(self):
        if BV_Grouping.NO_REPRESENTATIVES:
            return self
        if self in BV_Internal_Grouping.representatives:
            BV_Internal_Grouping.representatives_hits += 1
        else:
            with BV_Internal_Grouping.representatives_lock:
                if self not in BV_Internal_Grouping.representatives:
                    assert self.is_consistent()
                    BV_Internal_Grouping.representatives[self] = self
        return BV_Internal_Grouping.representatives[self]

    def projection_proto(level, swap_level, fork_level, input_i):
        # generalizing CFLOBDD projection to generational CFLOBVDD projection
        assert 0 <= input_i < 2**level
        if level == 0:
            return BV_Fork_Grouping.projection_proto(level, swap_level, fork_level)
        else:
            g = BV_Internal_Grouping(level, swap_level, fork_level, True)

            if input_i < 2**(level - 1):
                g.a_connection = BV_Internal_Grouping.projection_proto(level - 1,
                    swap_level, fork_level, input_i)
                g.number_of_exits = g.a_connection.number_of_exits
                # g.a_return_tuple == {} representing g.a_return_tuple = dict([(e, e)
                    # for e in range(1, g.number_of_exits + 1)])

                g.number_of_b_connections = g.number_of_exits

                projection_proto = BV_No_Distinction_Proto.representative(level - 1,
                    swap_level, fork_level)

                g.b_connections = dict([(c, projection_proto)
                    for c in range(1, g.number_of_b_connections + 1)])
                g.b_return_tuples = dict([(e, {1:e}) for e in range(1, g.number_of_exits + 1)])
            else:
                g.a_connection = BV_No_Distinction_Proto.representative(level - 1,
                    swap_level, fork_level)
                # g.a_return_tuple == {} representing g.a_return_tuple[1] = 1

                g.number_of_b_connections = 1

                projection_proto = BV_Internal_Grouping.projection_proto(level - 1,
                    swap_level, fork_level, input_i - 2**(level - 1))

                g.number_of_exits = projection_proto.number_of_exits

                g.b_connections = {1:projection_proto}
                g.b_return_tuples = {1:dict([(e, e) for e in range(1, g.number_of_exits + 1)])}

            return g.representative()

    def swap_uncached(self):
        assert self.level > self.swap_level

        g = BV_Internal_Grouping(self.level, self.swap_level, self.fork_level,
            not self.a2b, self.number_of_exits)

        g.a_connection = BV_No_Distinction_Proto.representative(self.level - 1,
            self.swap_level, self.fork_level)
        g.b_return_tuples = {1:{}}

        # a_connection becomes product of all b_connections which
        # is already reduced because a_return_tuple is idempotent
        for g_b_i in self.b_connections:
            g_b = self.b_connections[g_b_i]
            g_b_i_rt = self.b_return_tuples[g_b_i]
            g.a_connection, pt = g.a_connection.pair_product(g_b)
            g.b_return_tuples = dict([(i,
                # pt[i][0] is the exit index of the already paired b_connections
                # pt[i][1] is the exit index of the next b_connection being paired
                # extend b_return_tuples for reduced versions of a_connection below
                g.b_return_tuples[pt[i][0]] |
                    # with the original exit of the next b_connection being paired
                    {len(g.b_return_tuples[pt[i][0]]) + 1:g_b_i_rt[pt[i][1]]}) for i in pt])

        g.number_of_b_connections = len(g.b_return_tuples)

        # b_connections become reduced versions of a_connection
        for g_b_i in g.b_return_tuples:
            g_b_i_rt = g.b_return_tuples[g_b_i]

            induced_return_tuple, induced_reduction_tuple = \
                CFLOBVDD.linear_collapse_classes_leftmost(g_b_i_rt)

            g.b_connections[g_b_i] = self.a_connection.reduce(induced_reduction_tuple)
            g.b_return_tuples[g_b_i] = induced_return_tuple

        return g.representative()

    def swap(self):
        assert self.level > self.swap_level

        if self.is_swap_cached():
            return self.get_cached_swap()

        if BV_Grouping.NO_SWAP_CACHING:
            NO_PAIR_CACHING = BV_Grouping.NO_PAIR_CACHING
            NO_REDUCTION_CACHING = BV_Grouping.NO_REDUCTION_CACHING
            NO_CLASSES_CACHING = BV_Grouping.NO_CLASSES_CACHING
            NO_REPRESENTATIVES = BV_Grouping.NO_REPRESENTATIVES

            BV_Grouping.NO_PAIR_CACHING = True
            BV_Grouping.NO_REDUCTION_CACHING = True
            BV_Grouping.NO_CLASSES_CACHING = True
            BV_Grouping.NO_REPRESENTATIVES = True

        g = self.swap_uncached()

        if BV_Grouping.NO_SWAP_CACHING:
            BV_Grouping.NO_PAIR_CACHING = NO_PAIR_CACHING
            BV_Grouping.NO_REDUCTION_CACHING = NO_REDUCTION_CACHING
            BV_Grouping.NO_CLASSES_CACHING = NO_CLASSES_CACHING
            BV_Grouping.NO_REPRESENTATIVES = NO_REPRESENTATIVES

        # swapping is involutory: assert self is g.swap_uncached()

        return self.cache_swap(g)

    def downsample_uncached(self):
        assert self.level <= self.fork_level

        if self.a2b:
            g = self
        else:
            # forks do not yet support different input orderings
            g = self.swap()

        g_a_bvdd = g.a_connection.downsample().bvdd

        g_b_bvdds = {}

        for g_b_i in g.b_connections:
            g_b = g.b_connections[g_b_i]
            g_b_bvdds[g_b_i] = g_b.downsample().bvdd

        bvdd = g_a_bvdd.downsample(g.level, g_b_bvdds, g.b_return_tuples)

        assert bvdd.number_of_exits() == g.number_of_exits

        g = BV_Fork_Grouping(g.level, g.swap_level, g.fork_level, g.number_of_exits, bvdd)

        return g.representative()

    def pair_compressed(self, g2, g1_other, g2_other):
        assert isinstance(g2, BV_Internal_Grouping)

        g1 = self

        size = g1.number_of_b_connections + g2.number_of_b_connections
        size_other = g1_other.number_of_b_connections + g2_other.number_of_b_connections

        if size < size_other:
            return g1.representative(), g2.representative()
        elif size > size_other:
            return g1_other.representative(), g2_other.representative()
        elif g1.a2b:
            # prefer original input ordering
            return g1.representative(), g2.representative()
        else:
            return g1_other.representative(), g2_other.representative()

    def pair_align(self, g2):
        assert isinstance(g2, BV_Internal_Grouping)

        g1 = self

        g1_swapped = g1.swap()
        g2_swapped = g2.swap()

        if g1.a2b == g2.a2b:
            return g1.pair_compressed(g2, g1_swapped, g2_swapped)
        else:
            return g1_swapped.pair_compressed(g2, g1, g2_swapped)

    def pair_product(self, g2):
        assert isinstance(g2, BV_Grouping)

        g1 = self

        assert g1.level == g2.level

        if g2.is_no_distinction_proto():
            return g2.pair_product(g1, False)
        else:
            g1_orig = g1
            g2_orig = g2

            if g1_orig.is_pair_product_cached(g2_orig):
                return g1_orig.get_cached_pair_product(g2_orig)

            if g1.level > g1.swap_level:
                if isinstance(g2, BV_Fork_Grouping):
                    g2 = g2.upsample()
                # g1 and g2 may be unaligned
                g1, g2 = g1.pair_align(g2)
            elif isinstance(g2, BV_Fork_Grouping):
                g, pt_ans = g1.downsample().pair_product(g2)
                return g1_orig.cache_pair_product(g2_orig, g, pt_ans)

            assert isinstance(g2, BV_Internal_Grouping)

            assert g1.a2b == g2.a2b

            if g1.level <= g1.fork_level:
                # g1 and g2 are downsampled in original order (decompressing)
                g, pt_ans = g1.downsample().pair_product(g2.downsample())
                return g1_orig.cache_pair_product(g2_orig, g, pt_ans)

            g = BV_Internal_Grouping(g1.level, g1.swap_level, g1.fork_level, g1.a2b)

            g_a, pt_a = g1.a_connection.pair_product(g2.a_connection)

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

            return g1_orig.cache_pair_product(g2_orig, g.representative(), pt_ans)

    def triple_compressed(self, g2, g3, g1_other, g2_other, g3_other):
        assert isinstance(g2, BV_Internal_Grouping) and isinstance(g3, BV_Internal_Grouping)

        g1 = self

        size = (g1.number_of_b_connections +
            g2.number_of_b_connections +
            g3.number_of_b_connections)
        size_other = (g1_other.number_of_b_connections +
            g2_other.number_of_b_connections +
            g3_other.number_of_b_connections)

        if size < size_other:
            return g1.representative(), g2.representative(), g3.representative()
        elif size > size_other:
            return g1_other.representative(), g2_other.representative(), g3_other.representative()
        elif g1.a2b:
            # prefer original input ordering
            return g1.representative(), g2.representative(), g3.representative()
        else:
            return g1_other.representative(), g2_other.representative(), g3_other.representative()

    def triple_align(self, g2, g3):
        assert isinstance(g2, BV_Internal_Grouping) and isinstance(g3, BV_Internal_Grouping)

        g1 = self

        g1_swapped = g1.swap()
        g2_swapped = g2.swap()
        g3_swapped = g3.swap()

        if g1.a2b == g2.a2b:
            if g2.a2b == g3.a2b:
                return g1.triple_compressed(g2, g3, g1_swapped, g2_swapped, g3_swapped)
            else:
                return g1.triple_compressed(g2, g3_swapped, g1_swapped, g2_swapped, g3)
        elif g2.a2b == g3.a2b:
            return g1.triple_compressed(g2_swapped, g3_swapped, g1_swapped, g2, g3)
        else:
            return g1.triple_compressed(g2_swapped, g3, g1_swapped, g2, g3_swapped)

    def triple_product(self, g2, g3):
        assert isinstance(g2, BV_Grouping) and isinstance(g3, BV_Grouping)

        g1 = self

        assert g1.level == g2.level == g3.level

        if g2.is_no_distinction_proto():
            return g2.triple_product(g1, g3, 2)
        elif g3.is_no_distinction_proto():
            return g3.triple_product(g1, g2, 3)
        else:
            g1_orig = g1
            g2_orig = g2
            g3_orig = g3

            if g1_orig.is_triple_product_cached(g2_orig, g3_orig):
                return g1_orig.get_cached_triple_product(g2_orig, g3_orig)

            if g1.level > g1.swap_level:
                if isinstance(g2, BV_Fork_Grouping):
                    g2 = g2.upsample()
                if isinstance(g3, BV_Fork_Grouping):
                    g3 = g3.upsample()
                # g1, g2, g3 may be unaligned
                g1, g2, g3 = g1.triple_align(g2, g3)
            elif isinstance(g2, BV_Fork_Grouping):
                if isinstance(g3, BV_Internal_Grouping):
                    g3 = g3.downsample()
                assert isinstance(g3, BV_Fork_Grouping)
                g, tt_ans = g1.downsample().triple_product(g2, g3)
                return g1_orig.cache_triple_product(g2_orig, g3_orig, g, tt_ans)
            elif isinstance(g3, BV_Fork_Grouping):
                assert isinstance(g2, BV_Internal_Grouping)
                g, tt_ans = g1.downsample().triple_product(g2.downsample(), g3)
                return g1_orig.cache_triple_product(g2_orig, g3_orig, g, tt_ans)

            assert isinstance(g2, BV_Internal_Grouping) and isinstance(g3, BV_Internal_Grouping)

            assert g1.a2b == g2.a2b == g3.a2b

            if g1.level <= g1.fork_level:
                # g1, g2, g3 are downsampled in original order (decompressing)
                g, tt_ans = g1.downsample().triple_product(g2.downsample(), g3.downsample())
                return g1_orig.cache_triple_product(g2_orig, g3_orig, g, tt_ans)

            g = BV_Internal_Grouping(g1.level, g1.swap_level, g1.fork_level, g1.a2b)

            g_a, tt_a = g1.a_connection.triple_product(g2.a_connection, g3.a_connection)

            g.a_connection = g_a
            # g.a_return_tuple == {} representing g.a_return_tuple = dict([(i, i) for i in tt_a])

            g.number_of_b_connections = len(tt_a)

            tt_ans = {}
            tt_ans_inv = {}

            for j in tt_a:
                g_b, tt_b = g1.b_connections[tt_a[j][0]].triple_product(g2.b_connections[tt_a[j][1]],
                    g3.b_connections[tt_a[j][2]])

                g.b_connections[j] = g_b
                g.b_return_tuples[j] = {}

                for i in tt_b:
                    c1 = g1.b_return_tuples[tt_a[j][0]][tt_b[i][0]]
                    c2 = g2.b_return_tuples[tt_a[j][1]][tt_b[i][1]]
                    c3 = g3.b_return_tuples[tt_a[j][2]][tt_b[i][2]]

                    if (c1, c2, c3) in tt_ans_inv:
                        g.b_return_tuples[j][len(g.b_return_tuples[j]) + 1] = tt_ans_inv[(c1, c2, c3)]
                    else:
                        g.number_of_exits += 1
                        g.b_return_tuples[j][len(g.b_return_tuples[j]) + 1] = g.number_of_exits
                        tt_ans[len(tt_ans) + 1] = (c1, c2, c3)
                        tt_ans_inv[(c1, c2, c3)] = len(tt_ans)

            return g1_orig.cache_triple_product(g2_orig, g3_orig, g.representative(), tt_ans)

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

            g_prime = BV_Internal_Grouping(g.level, g.swap_level, g.fork_level,
                g.a2b, reduction_length)

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

    def compress(self):
        # equivalent to pair_product of No_Distinction_Proto with self where
        # pair_product for No_Distinction_Proto actually traverses its connections
        # (except for final downsampling as BVDDs do not yet different input orderings)

        if self.level == self.swap_level:
            return self

        assert self.level > self.swap_level

        if self.is_compressed_cached():
            return self.get_cached_compressed()

        # compress in levels top-down

        g_swapped = self.swap()

        g = (g_swapped if g_swapped.number_of_b_connections < self.number_of_b_connections else
            self if g_swapped.number_of_b_connections > self.number_of_b_connections else
            # prefer original input ordering
            g_swapped if g_swapped.a2b else self)

        compressed_a_connection = g.a_connection.compress()

        has_been_compressed = compressed_a_connection is not g.a_connection

        compressed_b_connections = {}

        for g_b_i in g.b_connections:
            g_b = g.b_connections[g_b_i]
            compressed_b_connections[g_b_i] = g_b.compress()

            has_been_compressed |= compressed_b_connections[g_b_i] is not g_b

        if has_been_compressed:
            compressed_g = BV_Internal_Grouping(g.level, g.swap_level, g.fork_level,
                g.a2b, g.number_of_exits)

            compressed_g.a_connection = compressed_a_connection
            compressed_g.number_of_b_connections = g.number_of_b_connections
            compressed_g.b_connections = compressed_b_connections
            compressed_g.b_return_tuples = g.b_return_tuples

            return self.cache_compressed(compressed_g.representative())
        else:
            return self.cache_compressed(g.representative())

class BV_No_Distinction_Proto(BV_Internal_Grouping):
    representatives_lock = threading.Lock()
    representatives = {}
    representatives_hits = 0

    def __init__(self, level, swap_level, fork_level):
        assert level > 0
        assert 0 <= swap_level
        assert 0 <= fork_level
        super().__init__(level, swap_level, fork_level, True, 1)

    def representative(level, swap_level, fork_level):
        if level == 0:
            return BV_Dont_Care_Grouping.representative()
        elif level in BV_No_Distinction_Proto.representatives:
            BV_No_Distinction_Proto.representatives_hits += 1
            return BV_No_Distinction_Proto.representatives[level]
        else:
            g = BV_No_Distinction_Proto(level, swap_level, fork_level)

            g.a_connection = BV_No_Distinction_Proto.representative(level - 1,
                swap_level, fork_level)
            # g.a_return_tuple == {} representing g.a_return_tuple[1] = 1

            g.number_of_b_connections = 1
            g.b_connections[1] = g.a_connection
            g.b_return_tuples[1] = {1:1}

            if BV_Grouping.NO_REPRESENTATIVES:
                return g
            if level not in BV_No_Distinction_Proto.representatives:
                with BV_No_Distinction_Proto.representatives_lock:
                    if level not in BV_No_Distinction_Proto.representatives:
                        BV_No_Distinction_Proto.representatives[level] = g

            return BV_No_Distinction_Proto.representatives[level]

    def swap(self):
        assert self.level > self.swap_level
        return self

    def downsample_uncached(self):
        return BV_Fork_Grouping(self.level, self.swap_level, self.fork_level,
            1, BVDD.BVDD.constant(1)).representative()

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

    def compress(self):
        return self

class Collapsed_Classes:
    cache_lock = threading.Lock()
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
        if BV_Grouping.NO_CLASSES_CACHING:
            return (projected_classes, renumbered_classes)
        collapsed_classes = Collapsed_Classes(equiv_classes)
        with Collapsed_Classes.cache_lock:
            if collapsed_classes not in Collapsed_Classes.cache:
                Collapsed_Classes.cache[collapsed_classes] = (projected_classes, renumbered_classes)
        return Collapsed_Classes.cache[collapsed_classes]

class CFLOBVDD:
    REDUCE = True

    max_level_lock = threading.Lock()
    max_level = 0

    representatives_lock = threading.Lock()
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
        print("CFLOBVDD cache profile:")
        print(f"forks:          {BVDD.utilization(BV_Fork_Grouping.representatives_hits, len(BV_Fork_Grouping.representatives))}")
        print(f"internals:      {BVDD.utilization(BV_Internal_Grouping.representatives_hits, len(BV_Internal_Grouping.representatives))}")
        print(f"protos:         {BVDD.utilization(BV_No_Distinction_Proto.representatives_hits, len(BV_No_Distinction_Proto.representatives))}")
        print(f"swap:           {BVDD.utilization(BV_Grouping.swap_cache_hits, len(BV_Grouping.swap_cache))}")
        print(f"upsample:       {BVDD.utilization(BV_Grouping.upsample_cache_hits, len(BV_Grouping.upsample_cache))}")
        print(f"downsample:     {BVDD.utilization(BV_Grouping.downsample_cache_hits, len(BV_Grouping.downsample_cache))}")
        print(f"compressed:     {BVDD.utilization(BV_Grouping.compressed_cache_hits, len(BV_Grouping.compressed_cache))}")
        print(f"pair product:   {BVDD.utilization(BV_Grouping.pair_product_cache_hits, len(BV_Grouping.pair_product_cache))}")
        print(f"triple product: {BVDD.utilization(BV_Grouping.triple_product_cache_hits, len(BV_Grouping.triple_product_cache))}")
        print(f"reduction:      {BVDD.utilization(BV_Grouping.reduction_cache_hits, len(BV_Grouping.reduction_cache))}")
        print(f"classes:        {BVDD.utilization(Collapsed_Classes.cache_hits, len(Collapsed_Classes.cache))}")
        print(f"CFLOBVDDs:      {BVDD.utilization(CFLOBVDD.representatives_hits, len(CFLOBVDD.representatives))}")

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
                    printed_paths += ["[" + f"input @ {index_i}: " +
                        BV_Fork_Grouping.get_input_values(inputs) + "]"]
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
            f"{self.number_of_distinct_outputs()} disctinct output values (exits)\n"
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
        if BV_Grouping.NO_REPRESENTATIVES:
            return cflobvdd
        if cflobvdd in CFLOBVDD.representatives:
            CFLOBVDD.representatives_hits += 1
        else:
            with CFLOBVDD.representatives_lock:
                if cflobvdd not in CFLOBVDD.representatives:
                    assert cflobvdd.is_consistent()
                    CFLOBVDD.representatives[cflobvdd] = cflobvdd
        return CFLOBVDD.representatives[cflobvdd]

    def is_always_false(self):
        # without reductions False may appear more than once
        return self.number_of_distinct_outputs() == 1 and False in self.outputs.values()

    def is_always_true(self):
        # without reductions True may appear more than once
        return self.number_of_distinct_outputs() == 1 and True in self.outputs.values()

    def constant(level, swap_level, fork_level, output = 0):
        assert 0 <= swap_level <= level
        assert 0 <= fork_level <= level
        with CFLOBVDD.max_level_lock:
            CFLOBVDD.max_level = max(CFLOBVDD.max_level, level)
        return CFLOBVDD.representative(
            BV_No_Distinction_Proto.representative(level, swap_level, fork_level), {1:output})

    def byte_constant(level, swap_level, fork_level, number_of_input_bytes, output):
        assert number_of_input_bytes > 0
        level = max(level, swap_level, fork_level, ceil(log2(number_of_input_bytes)))
        return CFLOBVDD.constant(level, swap_level, fork_level, output)

    def false(level, swap_level, fork_level):
        return CFLOBVDD.constant(level, swap_level, fork_level, False)

    def true(level, swap_level, fork_level):
        return CFLOBVDD.constant(level, swap_level, fork_level, True)

    def flip_value_tuple(self):
        # self must be reduced
        assert self.number_of_outputs() == 2
        return CFLOBVDD.representative(self.grouping, {1:self.outputs[2], 2:self.outputs[1]})

    def complement(self):
        if self == CFLOBVDD.false(self.grouping.level, self.grouping.swap_level, self.grouping.fork_level):
            return CFLOBVDD.true(self.grouping.level, self.grouping.swap_level, self.grouping.fork_level)
        elif self == CFLOBVDD.true(self.grouping.level, self.grouping.swap_level, self.grouping.fork_level):
            return CFLOBVDD.false(self.grouping.level, self.grouping.swap_level, self.grouping.fork_level)
        else:
            # self must be reduced
            return self.flip_value_tuple()

    def unary_apply_and_reduce(self, op, number_of_output_bits):
        return self.binary_apply_and_reduce(
            CFLOBVDD.constant(self.grouping.level,
                self.grouping.swap_level, self.grouping.fork_level),
            lambda x, y: op(x),
            number_of_output_bits)

    def projection(level, swap_level, fork_level, input_i, reorder = False):
        assert 0 <= swap_level <= level
        assert 0 <= fork_level <= level
        assert 0 <= input_i < 2**level
        with CFLOBVDD.max_level_lock:
            CFLOBVDD.max_level = max(CFLOBVDD.max_level, level)
        grouping = BV_Internal_Grouping.projection_proto(level, swap_level, fork_level, input_i)
        if reorder:
            grouping = grouping.compress()
        return CFLOBVDD.representative(grouping,
            dict([(output + 1, output) for output in range(grouping.number_of_exits)]))

    def byte_projection(level, swap_level, fork_level, number_of_input_bytes, byte_i, reorder = False):
        level = max(level, swap_level, fork_level, ceil(log2(number_of_input_bytes)))
        assert 0 <= byte_i < 2**level
        return CFLOBVDD.projection(level, swap_level, fork_level, byte_i, reorder)

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

        g = g.compress()

        if CFLOBVDD.REDUCE:
            induced_value_tuple, induced_return_tuple = \
                CFLOBVDD.linear_collapse_classes_leftmost(equiv_classes)
            g = g.reduce(induced_return_tuple).compress()
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

        g = g.compress()

        if CFLOBVDD.REDUCE:
            induced_value_tuple, induced_return_tuple = \
                CFLOBVDD.linear_collapse_classes_leftmost(equiv_classes)
            g = g.reduce(induced_return_tuple).compress()
        else:
            induced_value_tuple = equiv_classes

        return CFLOBVDD.representative(g, induced_value_tuple)