#!/usr/bin/env python3

# Copyright (c) the Selfie Project authors. All rights reserved.
# Please see the AUTHORS file for details. Use of this source code is
# governed by a BSD license that can be found in the LICENSE file.

# Selfie is a project of the Computational Systems Group at the
# Department of Computer Sciences of the University of Salzburg
# in Austria. For further information and code please refer to:

# selfie.cs.uni-salzburg.at

# Bitvector decision diagrams (BVDDs) for single-byte inputs

# ------------------------------------------------------------

def utilization(hits, misses):
    if hits + misses == 0:
        return "0.0%"
    else:
        return f"{round(hits / (hits + misses) * 100, 2)}% ({hits} hits, {misses} misses)"

class SBDD:
    def __init__(self, i2v):
        self.i2v = i2v

    def __str__(self):
        return f"{self.i2v}"

    def number_of_inputs(self):
        return 256

    def number_of_values(self):
        return len(set(self.i2v.values()))

    def is_never_false(self):
        return self.number_of_values() == 1 and True in self.i2v.values()

    def is_never_true(self):
        return self.number_of_values() == 1 and False in self.i2v.values()

    def is_always_false(self):
        return self.is_never_true()

    def is_always_true(self):
        return self.is_never_false()

    def constant(output_value):
        assert isinstance(output_value, bool) or isinstance(output_value, int)
        return SBDD(dict([(input_value, output_value) for input_value in range(256)]))

    def projection():
        return SBDD(dict([(input_value, input_value) for input_value in range(256)]))

    def compute_unary(self, op):
        return type(self)(dict([(input_value, op(self.i2v[input_value])) for input_value in self.i2v]))

    def compute_binary(self, op, bvdd2):
        assert isinstance(bvdd2, SBDD)
        bvdd1 = self
        return type(self)(dict([(input_value, op(bvdd1.i2v[input_value], bvdd2.i2v[input_value]))
            for input_value in range(256)])) # bvdd1.i2v.keys() & bvdd2.i2v.keys()

    def compute_ternary(self, op, bvdd2, bvdd3):
        assert isinstance(bvdd2, SBDD) and isinstance(bvdd3, SBDD)
        bvdd1 = self
        return type(self)(dict([(input_value,
            op(bvdd1.i2v[input_value], bvdd2.i2v[input_value], bvdd3.i2v[input_value]))
                for input_value in range(256)])) # bvdd1.i2v.keys() & bvdd2.i2v.keys() & bvdd3.i2v.keys()

    def compute_ite(self, bvdd2, bvdd3):
        assert isinstance(bvdd2, SBDD) and isinstance(bvdd3, SBDD)
        bvdd1 = self
        return self.compute_ternary(lambda x, y, z: y if x else z, bvdd2, bvdd3)

    def get_printed_BVDD(self, value):
        return [input_value for input_value in self.i2v if self.i2v[input_value] == value]

class SBBVDD_i2v(SBDD):
    def __str__(self):
        return str([f"{SBBVDD_i2v.get_input_values(inputs)}: {value}" for inputs, value in self.i2v.items()])

    def get_input_values(inputs):
        input_value = 0
        input_values = []
        while inputs != 0:
            if inputs % 2 == 1:
                input_values += [input_value]
            inputs //= 2
            input_value += 1
        return input_values

    def constant(output_value):
        assert isinstance(output_value, bool) or isinstance(output_value, int)
        return SBBVDD_i2v({2**256-1:output_value})

    def projection():
        return SBBVDD_i2v(dict([(2**input_value, input_value) for input_value in range(256)]))

    def reduce(self):
        v2i = {}
        for inputs in self.i2v:
            value = self.i2v[inputs]
            if value not in v2i:
                v2i[value] = inputs
            else:
                v2i[value] |= inputs
        self.i2v = {}
        for value in v2i:
            inputs = v2i[value]
            self.i2v[inputs] = value
        return self

    def compute_unary(self, op):
        return type(self)(super().compute_unary(op).i2v).reduce()

    def intersect_binary(self, bvdd2):
        assert isinstance(bvdd2, SBBVDD_i2v)
        bvdd1 = self
        return [(inputs1, inputs2)
            for inputs1 in bvdd1.i2v
                for inputs2 in bvdd2.i2v
                    if inputs1 & inputs2]

    def compute_binary(self, op, bvdd2):
        assert isinstance(bvdd2, SBBVDD_i2v)
        bvdd1 = self
        return type(self)(dict([(inputs[0] & inputs[1], op(bvdd1.i2v[inputs[0]], bvdd2.i2v[inputs[1]]))
            for inputs in bvdd1.intersect_binary(bvdd2)])).reduce()

    def intersect_ternary(self, bvdd2, bvdd3):
        assert isinstance(bvdd2, SBBVDD_i2v)
        assert isinstance(bvdd3, SBBVDD_i2v)
        bvdd1 = self
        return [(inputs1, inputs2, inputs3)
            for inputs1 in bvdd1.i2v
                for inputs2 in bvdd2.i2v
                    for inputs3 in bvdd3.i2v
                        if inputs1 & inputs2 & inputs3]

    def compute_ternary(self, op, bvdd2, bvdd3):
        assert isinstance(bvdd2, SBBVDD_i2v) and isinstance(bvdd3, SBBVDD_i2v)
        bvdd1 = self
        return type(self)(dict([(inputs[0] & inputs[1] & inputs[2],
            op(bvdd1.i2v[inputs[0]], bvdd2.i2v[inputs[1]], bvdd3.i2v[inputs[2]]))
                for inputs in bvdd1.intersect_ternary(bvdd2, bvdd3)])).reduce()

    def get_printed_BVDD(self, value):
        return [SBBVDD_i2v.get_input_values(inputs) for inputs in self.i2v if self.i2v[inputs] == value]

class SBBVDD_v2i(SBDD):
    def __init__(self, v2i):
        self.v2i = v2i

    def __str__(self):
        return str([f"{SBBVDD_i2v.get_input_values(inputs)}: {value}" for value, inputs in self.v2i.items()])

    def number_of_values(self):
        return len(self.v2i)

    def is_never_false(self):
        return self.number_of_values() == 1 and True in self.v2i

    def is_never_true(self):
        return self.number_of_values() == 1 and False in self.v2i

    def constant(output_value):
        assert isinstance(output_value, bool) or isinstance(output_value, int)
        return SBBVDD_v2i({output_value:2**256-1})

    def projection():
        return SBBVDD_v2i(dict([(input_value, 2**input_value) for input_value in range(256)]))

    def map(self, value, inputs):
        if value not in self.v2i:
            self.v2i[value] = inputs
        else:
            self.v2i[value] |= inputs

    def compute_unary(self, op):
        new_bvdd = type(self)({})
        for value in self.v2i:
            new_bvdd.map(op(value), self.v2i[value])
        return new_bvdd

    def intersect_binary(self, bvdd2):
        assert isinstance(bvdd2, SBBVDD_v2i)
        bvdd1 = self
        return [(value1, value2)
            for value1 in bvdd1.v2i
                for value2 in bvdd2.v2i
                    if bvdd1.v2i[value1] & bvdd2.v2i[value2]]

    def compute_binary(self, op, bvdd2):
        assert isinstance(bvdd2, SBBVDD_v2i)
        bvdd1 = self
        new_bvdd = type(self)({})
        for value_tuple in bvdd1.intersect_binary(bvdd2):
            new_bvdd.map(op(value_tuple[0], value_tuple[1]),
                bvdd1.v2i[value_tuple[0]] & bvdd2.v2i[value_tuple[1]])
        return new_bvdd

    def intersect_ternary(self, bvdd2, bvdd3):
        assert isinstance(bvdd2, SBBVDD_v2i)
        assert isinstance(bvdd3, SBBVDD_v2i)
        bvdd1 = self
        return [(value1, value2, value3)
            for value1 in bvdd1.v2i
                for value2 in bvdd2.v2i
                    for value3 in bvdd3.v2i
                        if bvdd1.v2i[value1] & bvdd2.v2i[value2] & bvdd3.v2i[value3]]

    def compute_ternary(self, op, bvdd2, bvdd3):
        assert isinstance(bvdd2, SBBVDD_v2i) and isinstance(bvdd3, SBBVDD_v2i)
        bvdd1 = self
        new_bvdd = type(self)({})
        for value_tuple in bvdd1.intersect_ternary(bvdd2, bvdd3):
            new_bvdd.map(op(value_tuple[0], value_tuple[1], value_tuple[2]),
                bvdd1.v2i[value_tuple[0]] & bvdd2.v2i[value_tuple[1]] & bvdd3.v2i[value_tuple[2]])
        return new_bvdd

    def get_printed_BVDD(self, value):
        return SBBVDD_i2v.get_input_values(self.v2i[value]) if value in self.v2i else ""

class BVDD(SBBVDD_v2i):
    pass