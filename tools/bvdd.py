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
# sets of n-bit bitvector constants that in turn
# represent branches in BVDDs:
# Theta(2**n)-time set intersection (bitwise conjunction) with
# Omega(1/n) and O(2**n/n) spatial overhead

# ------------------------------------------------------------

def utilization(hits, misses):
    if hits + misses == 0:
        return "0.0%"
    else:
        return f"{round(hits / (hits + misses) * 100, 2)}% ({hits} hits, {misses} misses)"

class SBDD:
    def __init__(self, i2o):
        self.i2o = i2o

    def __str__(self):
        return str([f"{input_value}: {output}" for input_value, output in self.i2o.items()])

    def get_i2o(self):
        return self.i2o

    def set(self, input_value, output):
        assert input_value not in self.i2o
        self.i2o[input_value] = output

    def number_of_inputs(self):
        return 256

    def number_of_outputs(self):
        return len(self.i2o.values())

    def number_of_distinct_outputs(self):
        return len(set(self.i2o.values()))

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

    def constant(value):
        return SBDD({}).constant_BVDD(value)

    def projection_BVDD(self, index = 0):
        self.i2o = dict([(input_value, input_value) for input_value in range(256)])
        return self

    def projection(index = 0):
        return SBDD({}).projection_BVDD(index)

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

    def compute_ite(self, bvdd2, bvdd3):
        assert type(bvdd2) is type(self)
        assert type(bvdd3) is type(self)
        return self.compute_ternary(lambda x, y, z: y if x else z, bvdd2, bvdd3)

    def get_printed_BVDD(self, value):
        return [input_value for input_value in self.i2o if self.i2o[input_value] == value]

    def print_profile():
        pass

class SBBVDD_i2o(SBDD):
    def __str__(self):
        return str([f"{SBBVDD_i2o.get_input_values(inputs)}: {output}" for inputs, output in self.i2o.items()])

    def get_input_values(inputs):
        input_value = 0
        input_values = []
        while inputs != 0:
            if inputs % 2 == 1:
                input_values += [input_value]
            inputs //= 2
            input_value += 1
        return input_values

    def set(self, inputs, output):
        assert inputs not in self.i2o
        self.i2o[inputs] = output

    def constant_BVDD(self, output):
        assert (isinstance(output, bool) or
            isinstance(output, int) or
            type(output) is type(self))
        self.i2o = {2**256-1:output}
        return self

    def constant(value):
        return SBBVDD_i2o({}).constant_BVDD(value)

    def projection_BVDD(self, index = 0):
        self.i2o = dict([(2**input_value, input_value) for input_value in range(256)])
        return self

    def projection(index = 0):
        return SBBVDD_i2o({}).projection_BVDD(index)

    def map(o2i, inputs, output):
        if output not in o2i:
            o2i[output] = inputs
        else:
            o2i[output] |= inputs
        return o2i

    def reduce(self):
        o2i = {}
        for inputs in self.i2o:
            o2i = SBBVDD_i2o.map(o2i, inputs, self.i2o[inputs])
        self.i2o = dict([(inputs, output) for output, inputs in o2i.items()])
        return self

    def compute_unary(self, op):
        return type(self)(super().compute_unary(op).i2o).reduce()

    def intersect_binary(self, bvdd2):
        assert type(bvdd2) is type(self)
        bvdd1 = self
        return [(inputs1, inputs2)
            for inputs1 in bvdd1.i2o
                for inputs2 in bvdd2.i2o
                    if inputs1 & inputs2]

    def compute_binary(self, op, bvdd2):
        assert type(bvdd2) is type(self)
        bvdd1 = self
        return type(self)(dict([(inputs[0] & inputs[1], op(bvdd1.i2o[inputs[0]], bvdd2.i2o[inputs[1]]))
            for inputs in bvdd1.intersect_binary(bvdd2)])).reduce()

    def intersect_ternary(self, bvdd2, bvdd3):
        assert type(bvdd2) is type(self)
        assert type(bvdd3) is type(self)
        bvdd1 = self
        return [(inputs1, inputs2, inputs3)
            for inputs1 in bvdd1.i2o
                for inputs2 in bvdd2.i2o
                    for inputs3 in bvdd3.i2o
                        if inputs1 & inputs2 & inputs3]

    def compute_ternary(self, op, bvdd2, bvdd3):
        assert type(bvdd2) is type(self)
        assert type(bvdd3) is type(self)
        bvdd1 = self
        return type(self)(dict([(inputs[0] & inputs[1] & inputs[2],
            op(bvdd1.i2o[inputs[0]], bvdd2.i2o[inputs[1]], bvdd3.i2o[inputs[2]]))
                for inputs in bvdd1.intersect_ternary(bvdd2, bvdd3)])).reduce()

    def get_printed_BVDD(self, value):
        return [SBBVDD_i2o.get_input_values(inputs) for inputs in self.i2o if self.i2o[inputs] == value]

class SBBVDD_o2i(SBDD):
    def __init__(self, o2i):
        self.o2i = o2i

    def __str__(self):
        return str([f"{SBBVDD_i2o.get_input_values(inputs)}: {output}" for output, inputs in self.o2i.items()])

    def get_i2o(self):
        return dict([(inputs, output) for output, inputs in self.o2i.items()])

    def set(self, inputs, output):
        assert output not in self.o2i
        self.o2i[output] = inputs

    def number_of_outputs(self):
        return len(self.o2i)

    def number_of_distinct_outputs(self):
        return self.number_of_outputs()

    def is_always_false(self):
        return self.number_of_outputs() == 1 and False in self.o2i

    def is_always_true(self):
        return self.number_of_outputs() == 1 and True in self.o2i

    def constant_BVDD(self, output):
        assert (isinstance(output, bool) or
            isinstance(output, int) or
            type(output) is type(self))
        self.o2i = {output:2**256-1}
        return self

    def constant(value):
        return SBBVDD_o2i({}).constant_BVDD(value)

    def projection_BVDD(self, index = 0):
        self.o2i = dict([(input_value, 2**input_value) for input_value in range(256)])
        return self

    def projection(index = 0):
        return SBBVDD_o2i({}).projection_BVDD(index)

    def map(self, inputs, output):
        self.o2i = SBBVDD_i2o.map(self.o2i, inputs, output)

    def compute_unary(self, op):
        new_bvdd = type(self)({})
        for output in self.o2i:
            new_bvdd.map(self.o2i[output], op(output))
        return new_bvdd

    def intersect_binary(self, bvdd2):
        assert type(bvdd2) is type(self)
        bvdd1 = self
        return [(output1, output2)
            for output1 in bvdd1.o2i
                for output2 in bvdd2.o2i
                    if bvdd1.o2i[output1] & bvdd2.o2i[output2]]

    def compute_binary(self, op, bvdd2):
        assert type(bvdd2) is type(self)
        bvdd1 = self
        new_bvdd = type(self)({})
        for output_tuple in bvdd1.intersect_binary(bvdd2):
            new_bvdd.map(bvdd1.o2i[output_tuple[0]] & bvdd2.o2i[output_tuple[1]],
                op(output_tuple[0], output_tuple[1]))
        return new_bvdd

    def intersect_ternary(self, bvdd2, bvdd3):
        assert type(bvdd2) is type(self)
        assert type(bvdd3) is type(self)
        bvdd1 = self
        return [(output1, output2, output3)
            for output1 in bvdd1.o2i
                for output2 in bvdd2.o2i
                    for output3 in bvdd3.o2i
                        if bvdd1.o2i[output1] & bvdd2.o2i[output2] & bvdd3.o2i[output3]]

    def compute_ternary(self, op, bvdd2, bvdd3):
        assert type(bvdd2) is type(self)
        assert type(bvdd3) is type(self)
        bvdd1 = self
        new_bvdd = type(self)({})
        for output_tuple in bvdd1.intersect_ternary(bvdd2, bvdd3):
            new_bvdd.map(bvdd1.o2i[output_tuple[0]] & bvdd2.o2i[output_tuple[1]] & bvdd3.o2i[output_tuple[2]],
                op(output_tuple[0], output_tuple[1], output_tuple[2]))
        return new_bvdd

    def get_printed_BVDD(self, value):
        return SBBVDD_i2o.get_input_values(self.o2i[value]) if value in self.o2i else []

class BVDD_uncached(SBBVDD_o2i):
    def constant(value):
        return BVDD({}).constant_BVDD(value)

    def projection(index):
        if index == 0:
            return BVDD({}).projection_BVDD()
        else:
            return BVDD({}).constant_BVDD(BVDD.projection(index - 1))

    def op_unary(op, output1):
        if isinstance(output1, BVDD):
            return output1.compute_unary(op)
        else:
            return op(output1)

    def compute_unary(self, op):
        return super().compute_unary(lambda x: BVDD.op_unary(op, x))

    def op_binary(op, output1, output2):
        if isinstance(output1, BVDD):
            if isinstance(output2, BVDD):
                return output1.compute_binary(op, output2)
            else:
                return output1.compute_unary(lambda x: op(x, output2))
        elif isinstance(output2, BVDD):
            return output2.compute_unary(lambda x: op(output1, x))
        else:
            return op(output1, output2)

    def compute_binary(self, op, bvdd2):
        assert isinstance(bvdd2, bool) or isinstance(bvdd2, int) or isinstance(bvdd2, BVDD)
        return super().compute_binary(lambda x, y: BVDD.op_binary(op, x, y), bvdd2)

    def op_ternary(op, output1, output2, output3):
        if isinstance(output1, BVDD):
            if isinstance(output2, BVDD):
                if isinstance(output3, BVDD):
                    return output1.compute_ternary(output2, output3)
                else:
                    return output1.compute_binary(lambda x, y: op(x, y, output3), output2)
            elif isinstance(output3, BVDD):
                return output1.compute_binary(lambda x, y: op(x, output2, y), output3)
            else:
                return output1.compute_unary(lambda x: op(x, output2, output3))
        elif isinstance(output2, BVDD):
            if isinstance(output3, BVDD):
                return output2.compute_binary(lambda x, y: op(output1, x, y), output3)
            else:
                return output2.compute_unary(lambda x: op(output1, x, output3))
        elif isinstance(output3, BVDD):
            return output3.compute_unary(lambda x: op(output1, output2, x))
        else:
            return op(output1, output2, output3)

    def compute_ternary(self, op, bvdd2, bvdd3):
        assert isinstance(bvdd2, bool) or isinstance(bvdd2, int) or isinstance(bvdd2, BVDD)
        assert isinstance(bvdd3, bool) or isinstance(bvdd3, int) or isinstance(bvdd3, BVDD)
        return super().compute_ternary(lambda x, y, z: BVDD.op_ternary(op, x, y, z), bvdd2, bvdd3)

    def extract(self, value):
        new_bvdd = BVDD({})
        i2o = self.get_i2o()
        for inputs in i2o:
            output = i2o[inputs]
            if output == value:
                new_bvdd.set(inputs, output)
            elif isinstance(output, BVDD):
                extracted_bvdd = output.extract(value)
                if extracted_bvdd.get_i2o():
                    new_bvdd.set(inputs, extracted_bvdd)
        return new_bvdd

    def get_printed_BVDD(self, value):
        return self.extract(value)

class BVDD_cached(BVDD_uncached):
    intersect_binary_cache = {}
    intersect_binary_hits = 0

    def intersect_binary(self, bvdd2):
        if (self, bvdd2) in BVDD_cached.intersect_binary_cache:
            BVDD_cached.intersect_binary_hits += 1
        else:
            BVDD_cached.intersect_binary_cache[(self, bvdd2)] = super().intersect_binary(bvdd2)
        return BVDD_cached.intersect_binary_cache[(self, bvdd2)]

    intersect_ternary_cache = {}
    intersect_ternary_hits = 0

    def intersect_ternary(self, bvdd2, bvdd3):
        if (self, bvdd2, bvdd3) in BVDD_cached.intersect_ternary_cache:
            BVDD_cached.intersect_ternary_hits += 1
        else:
            BVDD_cached.intersect_ternary_cache[(self, bvdd2, bvdd3)] = super().intersect_ternary(bvdd2, bvdd3)
        return BVDD_cached.intersect_ternary_cache[(self, bvdd2, bvdd3)]

    constant_cache = {}
    constant_hits = 0

    def constant_BVDD(self, output):
        if output in BVDD_cached.constant_cache:
            BVDD_cached.constant_hits += 1
        else:
            BVDD_cached.constant_cache[output] = super().constant_BVDD(output)
        return BVDD_cached.constant_cache[output]

    projection_cache = {}
    projection_hits = 0

    def projection_BVDD(self, index = 0):
        if index in BVDD_cached.projection_cache:
            BVDD_cached.projection_hits += 1
        else:
            BVDD_cached.projection_cache[index] = super().projection_BVDD(index)
        return BVDD_cached.projection_cache[index]

    compute_unary_cache = {}
    compute_unary_hits = 0

    def compute_unary(self, op):
        if (op, self) in BVDD_cached.compute_unary_cache:
            BVDD_cached.compute_unary_hits += 1
        else:
            BVDD_cached.compute_unary_cache[(op, self)] = super().compute_unary(op)
        return BVDD_cached.compute_unary_cache[(op, self)]

    compute_binary_cache = {}
    compute_binary_hits = 0

    def compute_binary(self, op, bvdd2):
        if (op, self, bvdd2) in BVDD_cached.compute_binary_cache:
            BVDD_cached.compute_binary_hits += 1
        else:
            BVDD_cached.compute_binary_cache[(op, self, bvdd2)] = super().compute_binary(op, bvdd2)
        return BVDD_cached.compute_binary_cache[(op, self, bvdd2)]

    compute_ternary_cache = {}
    compute_ternary_hits = 0

    def compute_ternary(self, op, bvdd2, bvdd3):
        if (op, self, bvdd2, bvdd3) in BVDD_cached.compute_ternary_cache:
            BVDD_cached.compute_ternary_hits += 1
        else:
            BVDD_cached.compute_ternary_cache[(op, self, bvdd2, bvdd3)] = super().compute_ternary(op, bvdd2, bvdd3)
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