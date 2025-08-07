#!/usr/bin/env python3

# Copyright (c) the Selfie Project authors. All rights reserved.
# Please see the AUTHORS file for details. Use of this source code is
# governed by a BSD license that can be found in the LICENSE file.

# Selfie is a project of the Computational Systems Group at the
# Department of Computer Sciences of the University of Salzburg
# in Austria. For further information and code please refer to:

# selfie.cs.uni-salzburg.at

# Bitvector decision diagrams (BVDDs)

# Given an n-bit bitvector (currently for n == 8 only),
# we use 2**n-bit unsigned integers to represent
# sets of n-bit bitvector values that in turn represent
# branches in BVDDs over any number of n-bit bitvectors.

# Theta(2**n)-time set intersection (bitwise conjunction) with
# Omega(1/n) and O(2**n/n) spatial overhead

# ------------------------------------------------------------

def utilization(hits, misses):
    if hits + misses == 0:
        return "0.0%"
    else:
        return f"{round(hits / (hits + misses) * 100, 2)}% ({hits} hits, {misses} misses)"

class SBDD:
    def get_input_values(inputs):
        input_value = 0
        input_values = []
        while inputs != 0:
            if inputs % 2 == 1:
                input_values += [input_value]
            inputs //= 2
            input_value += 1
        return input_values

    def union(self):
        union = 0
        for inputs in self.get_s2o():
            assert inputs & union == 0
            union |= inputs
        return union

    def number_of_inputs(self):
        return self.union().bit_count()

    def is_consistent(self):
        return self.number_of_inputs() == 256

    def map(o2s, inputs, output):
        if output not in o2s:
            o2s[output] = inputs
        else:
            o2s[output] |= inputs

    def is_reduced(self):
        assert self.is_consistent()
        return True

    def compute_ite(self, bvdd2, bvdd3):
        assert type(bvdd2) is type(self)
        assert type(bvdd3) is type(self)
        return self.compute_ternary(lambda x, y, z: y if x else z, bvdd2, bvdd3)

    def print_profile():
        pass

class SBDD_i2o(SBDD):
    # single-byte decision diagram with naive input-to-output mapping
    def __init__(self, i2o):
        self.i2o = i2o

    def __str__(self):
        if self.is_consistent() and self.number_of_distinct_outputs() == 1:
            # all inputs map to the same output in a consistent BVDD
            return str([f"[0,255] -> {next(iter(self.i2o.values()))}"])
        else:
            return str([f"{input_value} -> {output}" for input_value, output in self.i2o.items()])

    def get_s2o(self):
        return self.i2o

    def set(self, input_value, output):
        assert input_value not in self.i2o
        self.i2o[input_value] = output

    def number_of_inputs(self):
        return len(self.i2o)

    def number_of_outputs(self):
        return len(self.i2o.values())

    def number_of_distinct_outputs(self):
        return len(set(self.i2o.values()))

    def get_only_output(self):
        assert self.number_of_distinct_outputs() == 1
        return next(iter(self.i2o.values()))

    def is_always_false(self):
        return self.number_of_distinct_outputs() == 1 and False in self.i2o.values()

    def is_always_true(self):
        return self.number_of_distinct_outputs() == 1 and True in self.i2o.values()

    def constant_BVDD(self, output):
        assert (isinstance(output, bool) or
            isinstance(output, int) or
            isinstance(output, type(self)))
        self.i2o = dict([(input_value, output) for input_value in range(256)])
        return self

    def constant(output_value):
        return SBDD_i2o({}).constant_BVDD(output_value)

    def projection_BVDD(self, index = 0):
        self.i2o = dict([(input_value, input_value) for input_value in range(256)])
        return self

    def projection(index = 0):
        return SBDD_i2o({}).projection_BVDD(index)

    def compute_unary(self, op):
        return type(self)(dict([(input_value, op(self.i2o[input_value]))
            for input_value in self.i2o]))

    def compute_binary(self, op, bvdd2):
        assert type(bvdd2) is type(self)
        bvdd1 = self
        return type(self)(dict([(input_value, op(bvdd1.i2o[input_value], bvdd2.i2o[input_value]))
            for input_value in range(256)])) # bvdd1.i2o.keys() & bvdd2.i2o.keys()

    def compute_ternary(self, op, bvdd2, bvdd3):
        assert type(bvdd2) is type(self)
        assert type(bvdd3) is type(self)
        bvdd1 = self
        return type(self)(dict([(input_value,
            op(bvdd1.i2o[input_value], bvdd2.i2o[input_value], bvdd3.i2o[input_value]))
                for input_value in range(256)])) # bvdd1.i2o.keys() & bvdd2.i2o.keys() & bvdd3.i2o.keys()

    def get_printed_BVDD(self, output_value):
        return [input_value for input_value in self.i2o if self.i2o[input_value] == output_value]

class SBDD_s2o(SBDD):
    # single-byte decision diagram with input-sets-to-output mapping
    def __init__(self, s2o):
        self.s2o = s2o

    def __str__(self):
        if self.is_consistent() and self.number_of_distinct_outputs() == 1:
            # all inputs map to the same output in a consistent BVDD
            return str([f"[0,255] -> {next(iter(self.s2o.values()))}"])
        else:
            return str([f"{SBDD.get_input_values(inputs)} -> {output}" for inputs, output in self.s2o.items()])

    def get_s2o(self):
        return self.s2o

    def set(self, inputs, output):
        assert inputs not in self.s2o
        self.s2o[inputs] = output

    def number_of_outputs(self):
        return len(self.s2o.values())

    def number_of_distinct_outputs(self):
        return len(set(self.s2o.values()))

    def get_only_output(self):
        assert self.number_of_distinct_outputs() == 1
        return next(iter(self.s2o.values()))

    def is_reduced(self):
        assert self.is_consistent()
        return self.number_of_outputs() == self.number_of_distinct_outputs()

    def is_always_false(self):
        return self.number_of_distinct_outputs() == 1 and False in self.s2o.values()

    def is_always_true(self):
        return self.number_of_distinct_outputs() == 1 and True in self.s2o.values()

    def constant_BVDD(self, output):
        assert (isinstance(output, bool) or
            isinstance(output, int) or
            type(output) is type(self))
        self.s2o = {2**256-1:output}
        return self

    def constant(output_value):
        return SBDD_s2o({}).constant_BVDD(output_value)

    def projection_BVDD(self, index = 0):
        self.s2o = dict([(2**input_value, input_value) for input_value in range(256)])
        return self

    def projection(index = 0):
        return SBDD_s2o({}).projection_BVDD(index)

    def reduce(self):
        if not self.is_reduced():
            o2s = {}
            for inputs in self.s2o:
                SBDD.map(o2s, inputs, self.s2o[inputs])
            self.s2o = dict([(inputs, output) for output, inputs in o2s.items()])
        return self

    def compute_unary(self, op):
        return type(self)(dict([(inputs, op(self.s2o[inputs])) for inputs in self.s2o])).reduce()

    def intersect_binary(self, bvdd2):
        assert type(bvdd2) is type(self)
        bvdd1 = self
        return [(inputs1, inputs2)
            for inputs1 in bvdd1.s2o
                for inputs2 in bvdd2.s2o
                    if inputs1 & inputs2]

    def compute_binary(self, op, bvdd2):
        assert type(bvdd2) is type(self)
        bvdd1 = self
        return type(self)(dict([(inputs[0] & inputs[1], op(bvdd1.s2o[inputs[0]], bvdd2.s2o[inputs[1]]))
            for inputs in bvdd1.intersect_binary(bvdd2)])).reduce()

    def intersect_ternary(self, bvdd2, bvdd3):
        assert type(bvdd2) is type(self)
        assert type(bvdd3) is type(self)
        bvdd1 = self
        return [(inputs1, inputs2, inputs3)
            for inputs1 in bvdd1.s2o
                for inputs2 in bvdd2.s2o
                    for inputs3 in bvdd3.s2o
                        if inputs1 & inputs2 & inputs3]

    def compute_ternary(self, op, bvdd2, bvdd3):
        assert type(bvdd2) is type(self)
        assert type(bvdd3) is type(self)
        bvdd1 = self
        return type(self)(dict([(inputs[0] & inputs[1] & inputs[2],
            op(bvdd1.s2o[inputs[0]], bvdd2.s2o[inputs[1]], bvdd3.s2o[inputs[2]]))
                for inputs in bvdd1.intersect_ternary(bvdd2, bvdd3)])).reduce()

    def get_printed_BVDD(self, output_value):
        return [SBDD.get_input_values(inputs) for inputs in self.s2o if self.s2o[inputs] == output_value]

class SBDD_o2s(SBDD):
    # single-byte decision diagram with output-to-input-sets mapping
    def __init__(self, o2s):
        self.o2s = o2s

    def __str__(self):
        if self.is_consistent() and self.number_of_distinct_outputs() == 1:
            # all inputs map to the same output in a consistent BVDD
            return str([f"[0,255] -> {next(iter(self.o2s))}"])
        else:
            return str([f"{SBDD.get_input_values(inputs)} -> {output}" for output, inputs in self.o2s.items()])

    def get_s2o(self):
        return dict([(inputs, output) for output, inputs in self.o2s.items()])

    def set(self, inputs, output):
        assert output not in self.o2s
        self.o2s[output] = inputs

    def number_of_outputs(self):
        return len(self.o2s)

    def number_of_distinct_outputs(self):
        return self.number_of_outputs()

    def get_only_output(self):
        assert self.number_of_distinct_outputs() == 1
        return next(iter(self.o2s))

    def is_always_false(self):
        return self.number_of_outputs() == 1 and False in self.o2s

    def is_always_true(self):
        return self.number_of_outputs() == 1 and True in self.o2s

    def constant_BVDD(self, output):
        assert (isinstance(output, bool) or
            isinstance(output, int) or
            type(output) is type(self))
        self.o2s = {output:2**256-1}
        return self

    def constant(output_value):
        return SBDD_o2s({}).constant_BVDD(output_value)

    def projection_BVDD(self, index = 0):
        self.o2s = dict([(input_value, 2**input_value) for input_value in range(256)])
        return self

    def projection(index = 0):
        return SBDD_o2s({}).projection_BVDD(index)

    def map(self, inputs, output):
        SBDD.map(self.o2s, inputs, output)

    def compute_unary(self, op):
        new_bvdd = type(self)({})
        for output in self.o2s:
            new_bvdd.map(self.o2s[output], op(output))
        return new_bvdd

    def intersect_binary(self, bvdd2):
        assert type(bvdd2) is type(self)
        bvdd1 = self
        return [(output1, output2)
            for output1 in bvdd1.o2s
                for output2 in bvdd2.o2s
                    if bvdd1.o2s[output1] & bvdd2.o2s[output2]]

    def compute_binary(self, op, bvdd2):
        assert type(bvdd2) is type(self)
        bvdd1 = self
        new_bvdd = type(self)({})
        for output_tuple in bvdd1.intersect_binary(bvdd2):
            new_bvdd.map(bvdd1.o2s[output_tuple[0]] & bvdd2.o2s[output_tuple[1]],
                op(output_tuple[0], output_tuple[1]))
        return new_bvdd

    def intersect_ternary(self, bvdd2, bvdd3):
        assert type(bvdd2) is type(self)
        assert type(bvdd3) is type(self)
        bvdd1 = self
        return [(output1, output2, output3)
            for output1 in bvdd1.o2s
                for output2 in bvdd2.o2s
                    for output3 in bvdd3.o2s
                        if bvdd1.o2s[output1] & bvdd2.o2s[output2] & bvdd3.o2s[output3]]

    def compute_ternary(self, op, bvdd2, bvdd3):
        assert type(bvdd2) is type(self)
        assert type(bvdd3) is type(self)
        bvdd1 = self
        new_bvdd = type(self)({})
        for output_tuple in bvdd1.intersect_ternary(bvdd2, bvdd3):
            new_bvdd.map(bvdd1.o2s[output_tuple[0]] & bvdd2.o2s[output_tuple[1]] & bvdd3.o2s[output_tuple[2]],
                op(output_tuple[0], output_tuple[1], output_tuple[2]))
        return new_bvdd

    def get_printed_BVDD(self, output_value):
        return SBDD.get_input_values(self.o2s[output_value]) if output_value in self.o2s else []

class BVDD_uncached(SBDD_o2s):
    def number_of_outputs(self):
        count = 0
        s2o = self.get_s2o()
        for inputs in s2o:
            output = s2o[inputs]
            if isinstance(output, BVDD):
                count += output.number_of_outputs()
            else:
                count += 1
        return count

    def constant(output_value):
        return BVDD({}).constant_BVDD(output_value)

    def projection(index):
        if index == 0:
            return BVDD({}).projection_BVDD()
        else:
            return BVDD({}).constant_BVDD(BVDD.projection(index - 1))

    def reduce_BVDD(self):
        # assert index > 0
        assert self.is_reduced()
        if self.number_of_distinct_outputs() == 1:
            # all inputs map to the same output
            return self.get_only_output()
        else:
            return self

    def op_unary(op, output1):
        if isinstance(output1, BVDD):
            return output1.compute_unary(op).reduce_BVDD()
        else:
            return op(output1)

    def compute_unary(self, op):
        return super().compute_unary(lambda x: BVDD.op_unary(op, x))

    def op_binary(op, output1, output2):
        if isinstance(output1, BVDD):
            if isinstance(output2, BVDD):
                return output1.compute_binary(op, output2).reduce_BVDD()
            else:
                return output1.compute_unary(lambda x: op(x, output2)).reduce_BVDD()
        elif isinstance(output2, BVDD):
            return output2.compute_unary(lambda x: op(output1, x)).reduce_BVDD()
        else:
            return op(output1, output2)

    def compute_binary(self, op, bvdd2):
        assert isinstance(bvdd2, bool) or isinstance(bvdd2, int) or isinstance(bvdd2, BVDD)
        return super().compute_binary(lambda x, y: BVDD.op_binary(op, x, y), bvdd2)

    def op_ternary(op, output1, output2, output3):
        if isinstance(output1, BVDD):
            if isinstance(output2, BVDD):
                if isinstance(output3, BVDD):
                    return output1.compute_ternary(output2, output3).reduce_BVDD()
                else:
                    return output1.compute_binary(lambda x, y: op(x, y, output3), output2).reduce_BVDD()
            elif isinstance(output3, BVDD):
                return output1.compute_binary(lambda x, y: op(x, output2, y), output3).reduce_BVDD()
            else:
                return output1.compute_unary(lambda x: op(x, output2, output3)).reduce_BVDD()
        elif isinstance(output2, BVDD):
            if isinstance(output3, BVDD):
                return output2.compute_binary(lambda x, y: op(output1, x, y), output3).reduce_BVDD()
            else:
                return output2.compute_unary(lambda x: op(output1, x, output3)).reduce_BVDD()
        elif isinstance(output3, BVDD):
            return output3.compute_unary(lambda x: op(output1, output2, x)).reduce_BVDD()
        else:
            return op(output1, output2, output3)

    def compute_ternary(self, op, bvdd2, bvdd3):
        assert isinstance(bvdd2, bool) or isinstance(bvdd2, int) or isinstance(bvdd2, BVDD)
        assert isinstance(bvdd3, bool) or isinstance(bvdd3, int) or isinstance(bvdd3, BVDD)
        return super().compute_ternary(lambda x, y, z: BVDD.op_ternary(op, x, y, z), bvdd2, bvdd3)

    def extract(self, output_value):
        new_bvdd = BVDD({})
        s2o = self.get_s2o()
        for inputs in s2o:
            output = s2o[inputs]
            if output == output_value:
                new_bvdd.set(inputs, output)
            elif isinstance(output, BVDD):
                extracted_bvdd = output.extract(output_value)
                if extracted_bvdd.get_s2o():
                    new_bvdd.set(inputs, extracted_bvdd)
        # BVDD may be incomplete, only use for printing
        return new_bvdd

    def get_printed_BVDD(self, output_value):
        return self.extract(output_value)

import threading

class BVDD_cached(BVDD_uncached):
    intersect_binary_lock = threading.Lock()
    intersect_binary_cache = {}
    intersect_binary_hits = 0

    def intersect_binary(self, bvdd2, intersection = None):
        if (self, bvdd2) in BVDD_cached.intersect_binary_cache:
            BVDD_cached.intersect_binary_hits += 1
        elif intersection:
            # lock is acquired
            BVDD_cached.intersect_binary_cache[(self, bvdd2)] = intersection
        else:
            # concurrent without acquiring lock
            intersection = super().intersect_binary(bvdd2)
            with BVDD_cached.intersect_binary_lock:
                return self.intersect_binary(bvdd2, intersection)
        return BVDD_cached.intersect_binary_cache[(self, bvdd2)]

    intersect_ternary_lock = threading.Lock()
    intersect_ternary_cache = {}
    intersect_ternary_hits = 0

    def intersect_ternary(self, bvdd2, bvdd3, intersection = None):
        if (self, bvdd2, bvdd3) in BVDD_cached.intersect_ternary_cache:
            BVDD_cached.intersect_ternary_hits += 1
        elif intersection:
            # lock is acquired
            BVDD_cached.intersect_ternary_cache[(self, bvdd2, bvdd3)] = intersection
        else:
            # concurrent without acquiring lock
            intersection = super().intersect_ternary(bvdd2, bvdd3)
            with BVDD_cached.intersect_ternary_lock:
                return self.intersect_ternary(bvdd2, bvdd3, intersection)
        return BVDD_cached.intersect_ternary_cache[(self, bvdd2, bvdd3)]

    constant_lock = threading.Lock()
    constant_cache = {}
    constant_hits = 0

    def constant_BVDD(self, output, constant = None):
        if output in BVDD_cached.constant_cache:
            BVDD_cached.constant_hits += 1
        elif constant:
            # lock is acquired
            BVDD_cached.constant_cache[output] = constant
        else:
            # concurrent without acquiring lock
            constant = super().constant_BVDD(output)
            with BVDD_cached.constant_lock:
                return self.constant_BVDD(output, constant)
        return BVDD_cached.constant_cache[output]

    projection_lock = threading.Lock()
    projection_cache = {}
    projection_hits = 0

    def projection_BVDD(self, index = 0, projection = None):
        if index in BVDD_cached.projection_cache:
            BVDD_cached.projection_hits += 1
        elif projection:
            # lock is acquired
            BVDD_cached.projection_cache[index] = projection
        else:
            # concurrent without acquiring lock
            projection = super().projection_BVDD(index)
            with BVDD_cached.projection_lock:
                return self.projection_BVDD(index, projection)
        return BVDD_cached.projection_cache[index]

    compute_unary_lock = threading.Lock()
    compute_unary_cache = {}
    compute_unary_hits = 0

    def compute_unary(self, op, unary = None):
        if (op, self) in BVDD_cached.compute_unary_cache:
            BVDD_cached.compute_unary_hits += 1
        elif unary:
            # lock is acquired
            BVDD_cached.compute_unary_cache[(op, self)] = unary
        else:
            # concurrent without acquiring lock
            unary = super().compute_unary(op)
            with BVDD_cached.compute_unary_lock:
                return self.compute_unary(op, unary)
        return BVDD_cached.compute_unary_cache[(op, self)]

    compute_binary_lock = threading.Lock()
    compute_binary_cache = {}
    compute_binary_hits = 0

    def compute_binary(self, op, bvdd2, binary = None):
        if (op, self, bvdd2) in BVDD_cached.compute_binary_cache:
            BVDD_cached.compute_binary_hits += 1
        elif binary:
            # lock is acquired
            BVDD_cached.compute_binary_cache[(op, self, bvdd2)] = binary
        else:
            # concurrent without acquiring lock
            binary = super().compute_binary(op, bvdd2)
            with BVDD_cached.compute_binary_lock:
                return self.compute_binary(op, bvdd2, binary)
        return BVDD_cached.compute_binary_cache[(op, self, bvdd2)]

    compute_ternary_lock = threading.Lock()
    compute_ternary_cache = {}
    compute_ternary_hits = 0

    def compute_ternary(self, op, bvdd2, bvdd3, ternary = None):
        if (op, self, bvdd2, bvdd3) in BVDD_cached.compute_ternary_cache:
            BVDD_cached.compute_ternary_hits += 1
        elif ternary:
            # lock is acquired
            BVDD_cached.compute_ternary_cache[(op, self, bvdd2, bvdd3)] = ternary
        else:
            # concurrent without acquiring lock
            ternary = super().compute_ternary(op, bvdd2, bvdd3)
            with BVDD_cached.compute_ternary_lock:
                return self.compute_ternary(op, bvdd2, bvdd3, ternary)
        return BVDD_cached.compute_ternary_cache[(op, self, bvdd2, bvdd3)]

    def print_profile():
        print(f"Binary intersection cache utilization: {utilization(BVDD_cached.intersect_binary_hits, len(BVDD_cached.intersect_binary_cache))}")
        print(f"Ternary intersection cache utilization: {utilization(BVDD_cached.intersect_ternary_hits, len(BVDD_cached.intersect_ternary_cache))}")
        print(f"Constant cache utilization: {utilization(BVDD_cached.constant_hits, len(BVDD_cached.constant_cache))}")
        print(f"Projection cache utilization: {utilization(BVDD_cached.projection_hits, len(BVDD_cached.projection_cache))}")
        print(f"Unary cache utilization: {utilization(BVDD_cached.compute_unary_hits, len(BVDD_cached.compute_unary_cache))}")
        print(f"Binary cache utilization: {utilization(BVDD_cached.compute_binary_hits, len(BVDD_cached.compute_binary_cache))}")
        print(f"Ternary cache utilization: {utilization(BVDD_cached.compute_ternary_hits, len(BVDD_cached.compute_ternary_cache))}")

class BVDD(BVDD_uncached):
    pass