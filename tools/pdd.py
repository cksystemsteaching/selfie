#!/usr/bin/env python3

# Copyright (c) the Selfie Project authors. All rights reserved.
# Please see the AUTHORS file for details. Use of this source code is
# governed by a BSD license that can be found in the LICENSE file.

# Selfie is a project of the Computational Systems Group at the
# Department of Computer Sciences of the University of Salzburg
# in Austria. For further information and code please refer to:

# selfie.cs.uni-salzburg.at

# Partitioned Decision Diagrams (PDDs)

# ------------------------------------------------------------

import bvdd as BVDD

import threading

class PDD_uncached:
    def __init__(self, o2s):
        self.o2s = o2s

    def __str__(self):
        return "PDD: " + ", ".join([f"{inputs} -> {output_value}"
            for output_value, inputs in self.o2s.items()])

    def is_consistent(self):
        for output1_value in self.o2s:
            inputs1 = self.o2s[output1_value]
            if len(self.o2s) == 1:
                if inputs1.is_not_full():
                    return False
            for output2_value in self.o2s:
                if output1_value != output2_value:
                    inputs2 = self.o2s[output2_value]
                    if inputs1.intersection(inputs2).is_not_empty():
                        return False
        return True

    def number_of_distinct_inputs(self):
        return sum([self.o2s[output_value].number_of_partitioned_inputs() for output_value in self.o2s])

    def number_of_connections(self):
        return sum([self.o2s[output_value].number_of_connections() for output_value in self.o2s])

    def number_of_outputs(self):
        return len(self.o2s)

    def is_always_false(self):
        return len(self.o2s) == 1 and False in self.o2s

    def is_always_true(self):
        return len(self.o2s) == 1 and True in self.o2s

    def constant(output_value, clss):
        assert isinstance(output_value, bool) or isinstance(output_value, int)
        return PDD({output_value:clss.partitioned_constant()})

    def projection(index, clss):
        return PDD(dict([(input_value, clss.partitioned_projection(index, input_value))
            for input_value in range(256)]))

    def map(self, inputs, output_value):
        if output_value not in self.o2s:
            self.o2s[output_value] = inputs
        else:
            self.o2s[output_value] = self.o2s[output_value].union(inputs)

    def compute_unary(self, op, op_id = None, bits = None):
        new_pdd = PDD({})
        for output_value in self.o2s:
            new_pdd.map(self.o2s[output_value], op(output_value))
        return new_pdd

    def compute_binary(self, op, pdd2, op_id = None, bits = None):
        assert type(pdd2) is type(self)
        pdd1 = self
        new_pdd = PDD({})
        for output1_value in pdd1.o2s:
            for output2_value in pdd2.o2s:
                intersection = pdd1.o2s[output1_value].intersection(pdd2.o2s[output2_value])
                if intersection.is_not_empty():
                    new_pdd.map(intersection, op(output1_value, output2_value))
        return new_pdd

    def compute_ite(self, pdd2, pdd3, op_id = None, bits = None):
        assert type(pdd2) is type(self)
        assert type(pdd3) is type(self)
        pdd1 = self
        new_pdd = PDD({})
        for output1_value in pdd1.o2s:
            assert isinstance(output1_value, bool)
            if output1_value:
                for output2_value in pdd2.o2s:
                    intersection = pdd1.o2s[output1_value].intersection(pdd2.o2s[output2_value])
                    if intersection.is_not_empty():
                        new_pdd.map(intersection, output2_value)
            else:
                for output3_value in pdd3.o2s:
                    intersection = pdd1.o2s[output1_value].intersection(pdd3.o2s[output3_value])
                    if intersection.is_not_empty():
                        new_pdd.map(intersection, output3_value)
        return new_pdd

    def compute_ternary(self, op, pdd2, pdd3, op_id = None, bits = None):
        assert type(pdd2) is type(self)
        assert type(pdd3) is type(self)
        pdd1 = self
        new_pdd = PDD({})
        for output1_value in pdd1.o2s:
            for output2_value in pdd2.o2s:
                for output3_value in pdd3.o2s:
                    intersection = pdd1.o2s[output1_value].intersection(
                        pdd2.o2s[output2_value],
                        pdd3.o2s[output3_value])
                    if intersection.is_not_empty():
                        new_pdd.map(intersection,
                            op(output1_value, output2_value, output3_value))
        return new_pdd

    def compute_ite_slow(self, pdd2, pdd3, op_id = None, bits = None):
        assert type(pdd2) is type(self)
        assert type(pdd3) is type(self)
        return self.compute_ternary(lambda x, y, z: y if x else z, pdd2, pdd3, op_id, bits)

    def get_printed_inputs(self, output_value):
        return (f"{type(self).__name__}:" +
            f"{self.o2s[output_value].get_printed_inputs(0)} -> {output_value}")

class PDD_cached(PDD_uncached):
    compute_unary_lock = threading.Lock()
    compute_unary_cache = {}
    compute_unary_hits = 0

    def compute_unary(self, op, op_id = None, bits = None, unary = None):
        if op_id is None:
            return super().compute_unary(op, op_id, bits)
        elif (op_id, self) in PDD_cached.compute_unary_cache:
            # assert (super().compute_unary(op, op_id, bits) ==
            #     PDD_cached.compute_unary_cache[(op_id, self)])
            PDD_cached.compute_unary_hits += 1
        elif unary:
            # lock is acquired
            PDD_cached.compute_unary_cache[(op_id, self)] = unary
        else:
            # concurrent without acquiring lock
            unary = super().compute_unary(op, op_id, bits)
            with PDD_cached.compute_unary_lock:
                return self.compute_unary(op, op_id, bits, unary)
        return PDD_cached.compute_unary_cache[(op_id, self)]

    compute_binary_lock = threading.Lock()
    compute_binary_cache = {}
    compute_binary_hits = 0

    def compute_binary(self, op, pdd2, op_id = None, bits = None, binary = None):
        if op_id is None:
            return super().compute_binary(op, pdd2, op_id, bits)
        elif (op_id, self, pdd2) in PDD_cached.compute_binary_cache:
            # assert (super().compute_binary(op, pdd2, op_id, bits) ==
            #     PDD_cached.compute_binary_cache[(op_id, self, pdd2)])
            PDD_cached.compute_binary_hits += 1
        elif binary:
            # lock is acquired
            PDD_cached.compute_binary_cache[(op_id, self, pdd2)] = binary
        else:
            # concurrent without acquiring lock
            binary = super().compute_binary(op, pdd2, op_id, bits)
            with PDD_cached.compute_binary_lock:
                return self.compute_binary(op, pdd2, op_id, bits, binary)
        return PDD_cached.compute_binary_cache[(op_id, self, pdd2)]

    compute_ite_lock = threading.Lock()
    compute_ite_cache = {}
    compute_ite_hits = 0

    def compute_ite(self, pdd2, pdd3, op_id = None, bits = None, ite = None):
        if op_id is None:
            return super().compute_ite(pdd2, pdd3, op_id, bits)
        elif (op_id, self, pdd2, pdd3) in PDD_cached.compute_ite_cache:
            # assert (super().compute_ite(pdd2, pdd3, op_id, bits) ==
            #     PDD_cached.compute_ite_cache[(op_id, self, pdd2, pdd3)])
            PDD_cached.compute_ite_hits += 1
        elif ite:
            # lock is acquired
            PDD_cached.compute_ite_cache[(op_id, self, pdd2, pdd3)] = ite
        else:
            # concurrent without acquiring lock
            ite = super().compute_ite(pdd2, pdd3, op_id, bits)
            with PDD_cached.compute_ite_lock:
                return self.compute_ite(pdd2, pdd3, op_id, bits, ite)
        return PDD_cached.compute_ite_cache[(op_id, self, pdd2, pdd3)]

    compute_ternary_lock = threading.Lock()
    compute_ternary_cache = {}
    compute_ternary_hits = 0

    def compute_ternary(self, op, pdd2, pdd3, op_id = None, bits = None, ternary = None):
        if op_id is None:
            return super().compute_ternary(op, pdd2, pdd3, op_id, bits)
        elif (op_id, self, pdd2, pdd3) in PDD_cached.compute_ternary_cache:
            # assert (super().compute_ternary(op, pdd2, pdd3, op_id, bits) ==
            #     PDD_cached.compute_ternary_cache[(op_id, self, pdd2, pdd3)])
            PDD_cached.compute_ternary_hits += 1
        elif ternary:
            # lock is acquired
            PDD_cached.compute_ternary_cache[(op_id, self, pdd2, pdd3)] = ternary
        else:
            # concurrent without acquiring lock
            ternary = super().compute_ternary(op, pdd2, pdd3, op_id, bits)
            with PDD_cached.compute_ternary_lock:
                return self.compute_ternary(op, pdd2, pdd3, op_id, bits, ternary)
        return PDD_cached.compute_ternary_cache[(op_id, self, pdd2, pdd3)]

    def print_profile():
        print("PDD cache profile:")
        print(f"unary operators:   {BVDD.utilization(PDD_cached.compute_unary_hits, len(PDD_cached.compute_unary_cache))}")
        print(f"binary operators:  {BVDD.utilization(PDD_cached.compute_binary_hits, len(PDD_cached.compute_binary_cache))}")
        print(f"ite operators:     {BVDD.utilization(PDD_cached.compute_ite_hits, len(PDD_cached.compute_ite_cache))}")
        print(f"ternary operators: {BVDD.utilization(PDD_cached.compute_ternary_hits, len(PDD_cached.compute_ternary_cache))}")

class PDD(PDD_cached):
    pass