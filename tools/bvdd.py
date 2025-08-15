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

class BVDD_Node:
    def __str__(self):
        assert self.is_consistent() and self.is_dont_care()
        # all inputs map to the same output
        return str([f"[0,255] -> {self.get_dont_care_output()}"])

    def is_consistent(self):
        return self.number_of_inputs() == 256

    def is_dont_care(self):
        return self.number_of_distinct_SBDD_outputs() == 1

    def number_of_connections(self):
        count = 0
        for output in self.get_s2o().values():
            if isinstance(output, BVDD):
                count += output.number_of_connections() + 1
            else:
                count += 1
        return count

    def number_of_outputs(self):
        count = 0
        for output in self.get_s2o().values():
            if isinstance(output, BVDD):
                count += output.number_of_connections()
            else:
                count += 1
        return count

    def get_distinct_outputs(self):
        outputs = {}
        for output in self.get_s2o().values():
            if isinstance(output, BVDD):
                outputs |= output.get_distinct_outputs()
            else:
                outputs[output] = output
        return outputs

    def number_of_distinct_outputs(self):
        return len(self.get_distinct_outputs())

    def number_of_distinct_inputs(self, output_value = None):
        if self.is_dont_care():
            # dont-care inputs do not count
            output = self.get_dont_care_output()
            if isinstance(output, BVDD):
                return output.number_of_distinct_inputs(output_value)
            else:
                return 0
        else:
            count = 0
            s2o = self.get_s2o()
            for inputs in s2o:
                output = s2o[inputs]
                if isinstance(output, BVDD):
                    other_count = output.number_of_distinct_inputs(output_value)
                    assert output_value is not None or other_count > 0 # assert output.is_reduced()
                elif output_value is None or output == output_value:
                    other_count = 1
                else:
                    other_count = 0
                count += self.number_of_inputs_for_input(inputs) * other_count
            return count

    def number_of_solutions(self, output_value):
        return self.number_of_distinct_inputs(output_value)

    def get_input_values(inputs):
        assert inputs >= 0
        if inputs == 0:
            return []
        else:
            input_value = 0
            input_values = []
            while inputs != 0:
                if inputs % 2 == 1:
                    input_values += [input_value]
                inputs //= 2
                input_value += 1
            return input_values

    def get_paths(self, exit_i, index_i = 0):
        path = []
        s2o = self.get_s2o()
        for inputs in s2o:
            output = s2o[inputs]
            inputs = 2**inputs if isinstance(self, SBDD_i2o) else inputs
            if isinstance(output, BVDD):
                other_path = output.get_paths(exit_i, index_i + 1)
                if other_path:
                    path += [([(index_i, inputs)], other_path)]
            elif output == exit_i:
                path += [(index_i, inputs)]
        return path

    def union(self):
        # for s2o and o2s only
        union = 0
        for inputs in self.get_s2o():
            assert inputs & union == 0
            union |= inputs
        return union

    def number_of_inputs_for_input(self, inputs):
        # for s2o and o2s only
        return inputs.bit_count()

    def number_of_inputs(self):
        # for s2o and o2s only
        return self.number_of_inputs_for_input(self.union())

    def map(o2s, inputs, output):
        # for s2o and o2s only
        if output not in o2s:
            o2s[output] = inputs
        else:
            o2s[output] |= inputs

    def is_reduced(self):
        assert self.is_consistent()
        return True

    def projection_proto(index):
        return BVDD.projection(index, 1)

    def tuple2exit(tuple_inv, tuple_ins):
        if tuple_ins not in tuple_inv:
            tuple_inv[tuple_ins] = len(tuple_inv) + 1
        return tuple_inv[tuple_ins]

    def pair_product(self, bvdd2):
        pair_inv = {}
        return (self.compute_binary(lambda x, y: BVDD_Node.tuple2exit(pair_inv, (x, y)), bvdd2),
            dict([(pair_inv[pair], pair) for pair in pair_inv]))

    def triple_product(self, bvdd2, bvdd3):
        triple_inv = {}
        return (self.compute_ternary(lambda x, y, z: BVDD_Node.tuple2exit(triple_inv, (x, y, z)), bvdd2, bvdd3),
            dict([(triple_inv[triple], triple) for triple in triple_inv]))

    def reduce_BVDD(self):
        return self

    def reduce(self, reduction_tuple):
        new_bvdd = type(self)({})
        s2o = self.get_s2o()
        for inputs in s2o:
            output = s2o[inputs]
            if isinstance(output, BVDD):
                reduced_output = output.reduce(reduction_tuple)
                new_bvdd.set(inputs, reduced_output)
            else:
                new_bvdd.set(inputs, reduction_tuple[output])
        return new_bvdd.reduce().reduce_BVDD()

    def compute_ite(self, bvdd2, bvdd3):
        assert type(bvdd2) is type(self)
        assert type(bvdd3) is type(self)
        return self.compute_ternary(lambda x, y, z: y if x else z, bvdd2, bvdd3)

    def print_profile():
        pass

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
        return (f"{type(self).__name__}:\n" +
            f"{self.number_of_connections()} connections\n" +
            f"{self.number_of_outputs()} outputs\n" +
            f"{self.number_of_distinct_outputs()} distinct output values\n" +
            f"{self.number_of_distinct_inputs()} distinct inputs\n" +
            f"{self.number_of_solutions(output_value)} solutions\n" +
            f"{self.extract(output_value)}")

class SBDD_i2o(BVDD_Node):
    # single-byte decision diagram with naive input-to-output mapping
    def __init__(self, i2o):
        self.i2o = i2o

    def __str__(self):
        if self.is_consistent() and self.is_dont_care():
            return super().__str__()
        else:
            return str([f"{input_value} -> {output}" for input_value, output in self.i2o.items()])

    def __hash__(self):
        return hash(tuple(self.i2o.items()))

    def __eq__(self, bvdd2):
        return type(bvdd2) is type(self) and self.i2o == bvdd2.i2o

    def get_inputs_for_output(self, output_value):
        inputs = 0
        for input_value in self.i2o:
            output = self.i2o[input_value]
            if output == output_value:
                inputs |= 2**input_value
        return inputs

    def get_s2o(self):
        return self.i2o

    def set(self, input_value, output):
        assert input_value not in self.i2o
        self.i2o[input_value] = output

    def number_of_inputs_for_input(self, input_value):
        return 1

    def number_of_inputs(self):
        return len(self.i2o)

    def number_of_SBDD_outputs(self):
        return len(self.i2o.values())

    def number_of_distinct_SBDD_outputs(self):
        return len(set(self.i2o.values()))

    def get_dont_care_output(self):
        assert self.is_dont_care()
        return next(iter(self.i2o.values()))

    def is_always_false(self):
        return self.is_dont_care() and False in self.i2o.values()

    def is_always_true(self):
        return self.is_dont_care() and True in self.i2o.values()

    def constant_BVDD(self, output):
        assert (isinstance(output, bool) or
            isinstance(output, int) or
            isinstance(output, type(self)))
        self.i2o = dict([(input_value, output) for input_value in range(256)])
        return self

    def constant(output_value):
        return SBDD_i2o({}).constant_BVDD(output_value)

    def projection_BVDD(self, index = 0, offset = 0):
        self.i2o = dict([(input_value, input_value + offset) for input_value in range(256)])
        return self

    def projection(index = 0, offset = 0):
        return SBDD_i2o({}).projection_BVDD(index, offset)

    def reduce(self, reduction_tuple = None):
        if reduction_tuple is not None:
            return super().reduce(reduction_tuple)
        else:
            return self

    def compute_unary(self, op):
        return type(self)(dict([(input_value, op(self.i2o[input_value]))
            for input_value in self.i2o]))

    def intersect_binary(self, bvdd2):
        assert type(bvdd2) is type(self)
        # bvdd1.i2o.keys() & bvdd2.i2o.keys()
        return [(input_value, input_value) for input_value in range(256)]

    def compute_binary(self, op, bvdd2):
        assert type(bvdd2) is type(self)
        bvdd1 = self
        return type(self)(dict([(input_value,
            op(bvdd1.i2o[input_value], bvdd2.i2o[input_value]))
                for input_value, _ in bvdd1.intersect_binary(bvdd2)]))

    def intersect_ternary(self, bvdd2, bvdd3):
        assert type(bvdd2) is type(self)
        assert type(bvdd3) is type(self)
        # bvdd1.i2o.keys() & bvdd2.i2o.keys() & bvdd3.i2o.keys()
        return [(input_value, input_value, input_value) for input_value in range(256)]

    def compute_ternary(self, op, bvdd2, bvdd3):
        assert type(bvdd2) is type(self)
        assert type(bvdd3) is type(self)
        bvdd1 = self
        return type(self)(dict([(input_value,
            op(bvdd1.i2o[input_value], bvdd2.i2o[input_value], bvdd3.i2o[input_value]))
                for input_value, _, _ in bvdd1.intersect_ternary(bvdd2, bvdd3)]))

class SBDD_s2o(BVDD_Node):
    # single-byte decision diagram with input-sets-to-output mapping
    def __init__(self, s2o):
        self.s2o = s2o

    def __str__(self):
        if self.is_consistent() and self.is_dont_care():
            return super().__str__()
        else:
            return str([f"{BVDD_Node.get_input_values(inputs)} -> {output}" for inputs, output in self.s2o.items()])

    def __hash__(self):
        return hash(tuple(self.s2o.items()))

    def __eq__(self, bvdd2):
        return type(bvdd2) is type(self) and self.s2o == bvdd2.s2o

    def get_inputs_for_output(self, output_value):
        assert self.is_reduced()
        for inputs in self.s2o:
            output = self.s2o[inputs]
            if output == output_value:
                return inputs
        return 0

    def get_s2o(self):
        return self.s2o

    def set(self, inputs, output):
        assert inputs not in self.s2o
        self.s2o[inputs] = output

    def number_of_SBDD_outputs(self):
        return len(self.s2o.values())

    def number_of_distinct_SBDD_outputs(self):
        return len(set(self.s2o.values()))

    def get_dont_care_output(self):
        assert self.is_dont_care()
        return next(iter(self.s2o.values()))

    def is_reduced(self):
        assert self.is_consistent()
        return self.number_of_SBDD_outputs() == self.number_of_distinct_SBDD_outputs()

    def is_always_false(self):
        return self.is_dont_care() and False in self.s2o.values()

    def is_always_true(self):
        return self.is_dont_care() and True in self.s2o.values()

    def constant_BVDD(self, output):
        assert (isinstance(output, bool) or
            isinstance(output, int) or
            type(output) is type(self))
        self.s2o = {2**256-1:output}
        return self

    def constant(output_value):
        return SBDD_s2o({}).constant_BVDD(output_value)

    def projection_BVDD(self, index = 0, offset = 0):
        self.s2o = dict([(2**input_value, input_value + offset) for input_value in range(256)])
        return self

    def projection(index = 0, offset = 0):
        return SBDD_s2o({}).projection_BVDD(index, offset)

    def reduce(self, reduction_tuple = None):
        if reduction_tuple is not None:
            return super().reduce(reduction_tuple)
        elif not self.is_reduced():
            o2s = {}
            for inputs in self.s2o:
                BVDD_Node.map(o2s, inputs, self.s2o[inputs])
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
        return type(self)(dict([(inputs1 & inputs2,
            op(bvdd1.s2o[inputs1], bvdd2.s2o[inputs2]))
                for inputs1, inputs2 in bvdd1.intersect_binary(bvdd2)])).reduce()

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
        return type(self)(dict([(inputs1 & inputs2 & inputs3,
            op(bvdd1.s2o[inputs1], bvdd2.s2o[inputs2], bvdd3.s2o[inputs3]))
                for inputs1, inputs2, inputs3 in bvdd1.intersect_ternary(bvdd2, bvdd3)])).reduce()

class SBDD_o2s(BVDD_Node):
    # single-byte decision diagram with output-to-input-sets mapping
    def __init__(self, o2s):
        self.o2s = o2s

    def __str__(self):
        if self.is_consistent() and self.is_dont_care():
            return super().__str__()
        else:
            return str([f"{BVDD_Node.get_input_values(inputs)} -> {output}" for output, inputs in self.o2s.items()])

    def __hash__(self):
        return hash(tuple(self.o2s.items()))

    def __eq__(self, bvdd2):
        return type(bvdd2) is type(self) and self.o2s == bvdd2.o2s

    def get_inputs_for_output(self, output_value):
        return self.o2s[output_value] if output_value in self.o2s else 0

    def get_s2o(self):
        return dict([(inputs, output) for output, inputs in self.o2s.items()])

    def map(self, inputs, output):
        BVDD_Node.map(self.o2s, inputs, output)

    def set(self, inputs, output):
        self.map(inputs, output)

    def number_of_SBDD_outputs(self):
        return len(self.o2s)

    def number_of_distinct_SBDD_outputs(self):
        return self.number_of_SBDD_outputs()

    def get_dont_care_output(self):
        assert self.is_dont_care()
        return next(iter(self.o2s))

    def is_always_false(self):
        return self.is_dont_care() and False in self.o2s

    def is_always_true(self):
        return self.is_dont_care() and True in self.o2s

    def constant_BVDD(self, output):
        assert (isinstance(output, bool) or
            isinstance(output, int) or
            type(output) is type(self))
        self.o2s = {output:2**256-1}
        return self

    def constant(output_value):
        return SBDD_o2s({}).constant_BVDD(output_value)

    def projection_BVDD(self, index = 0, offset = 0):
        self.o2s = dict([(input_value + offset, 2**input_value) for input_value in range(256)])
        return self

    def projection(index = 0, offset = 0):
        return SBDD_o2s({}).projection_BVDD(index, offset)

    def reduce(self, reduction_tuple = None):
        if reduction_tuple is not None:
            return super().reduce(reduction_tuple)
        else:
            return self

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
        for output1, output2 in bvdd1.intersect_binary(bvdd2):
            new_bvdd.map(bvdd1.o2s[output1] & bvdd2.o2s[output2], op(output1, output2))
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
        for output1, output2, output3 in bvdd1.intersect_ternary(bvdd2, bvdd3):
            new_bvdd.map(bvdd1.o2s[output1] & bvdd2.o2s[output2] & bvdd3.o2s[output3],
                op(output1, output2, output3))
        return new_bvdd

class BVDD_uncached(SBDD_o2s):
    def constant(output_value):
        return BVDD({}).constant_BVDD(output_value)

    def projection(index, offset = 0):
        if index == 0:
            return BVDD({}).projection_BVDD(0, offset)
        else:
            return BVDD({}).constant_BVDD(BVDD.projection(index - 1, offset))

    def reduce_BVDD(self):
        # assert index > 0
        assert self.is_reduced()
        if self.is_dont_care():
            # all inputs map to the same output
            return self.get_dont_care_output()
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

    def projection_BVDD(self, index = 0, offset = 0, projection = None):
        if index in BVDD_cached.projection_cache:
            BVDD_cached.projection_hits += 1
        elif projection:
            # lock is acquired
            BVDD_cached.projection_cache[index] = projection
        else:
            # concurrent without acquiring lock
            projection = super().projection_BVDD(index, offset)
            with BVDD_cached.projection_lock:
                return self.projection_BVDD(index, offset, projection)
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