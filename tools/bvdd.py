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

class BVDD:
    def __init__(self, i2v):
        self.i2v = i2v

    def __str__(self):
        return f"{self.i2v}"

    def number_of_inputs(self):
        return len(self.i2v)

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
        return BVDD(dict([(input_value, output_value) for input_value in range(256)]))

    def projection():
        return BVDD(dict([(input_value, input_value) for input_value in range(256)]))

    def compute_unary(self, op):
        return BVDD(dict([(input_value, op(self.i2v[input_value])) for input_value in self.i2v]))

    def compute_binary(self, op, bvdd2):
        assert isinstance(bvdd2, BVDD)
        bvdd1 = self
        return BVDD(dict([(input_value, op(bvdd1.i2v[input_value], bvdd2.i2v[input_value])) for input_value in bvdd1.i2v.keys() & bvdd2.i2v.keys()]))

    def compute_ite(self, bvdd2, bvdd3):
        assert isinstance(bvdd2, BVDD) and isinstance(bvdd3, BVDD)
        bvdd1 = self
        return BVDD(dict([(input_value, bvdd2.i2v[input_value] if bvdd1.i2v[input_value] else bvdd3.i2v[input_value])
            for input_value in bvdd1.i2v.keys() & (bvdd2.i2v.keys() | bvdd3.i2v.keys())]))

    def get_printed_BVDD(self, value):
        return [input_value for input_value in self.i2v if self.i2v[input_value] == value]