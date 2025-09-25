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

import threading

def utilization(hits, misses):
    if hits + misses == 0:
        return "0.0%"
    else:
        return f"{round(hits / (hits + misses) * 100, 2)}% ({hits} hits, {misses} misses)"

class BVDD_Node:
    node_cache_lock = threading.Lock()
    node_cache = {}
    node_cache_hits = 0

    def __str__(self):
        if self.is_consistent() and self.is_dont_care():
            # all inputs map to the same output
            return "{" + f"[0,255] -> {self.get_dont_care_output()}" + "}"
        else:
            return "{" + ", ".join([f"{BVDD_Node.get_input_values(inputs)} -> {output}"
                for output, inputs in self.get_o2s().items()]) + "}"

    def cache(self):
        if self in BVDD_Node.node_cache:
            BVDD_Node.node_cache_hits += 1
        else:
            with BVDD_Node.node_cache_lock:
                if self not in BVDD_Node.node_cache:
                    BVDD_Node.node_cache[self] = self
        return BVDD_Node.node_cache[self]

    def is_consistent(self):
        return self.number_of_inputs() == 256

    def is_dont_care(self):
        return self.number_of_distinct_SBDD_outputs() == 1

    def is_constant(self):
        return self.is_dont_care() and not isinstance(self.get_dont_care_output(), BVDD)

    def number_of_connections(self):
        count = 0
        for output in self.get_s2o().values():
            if isinstance(output, BVDD):
                count += output.number_of_connections() + 1
        return count

    def number_of_outputs(self):
        count = 0
        for output in self.get_s2o().values():
            if isinstance(output, BVDD):
                count += output.number_of_outputs()
            else:
                count += 1
        return count

    def get_distinct_outputs(self):
        outputs = set()
        for output in self.get_s2o().values():
            if isinstance(output, BVDD):
                outputs |= output.get_distinct_outputs()
            else:
                outputs |= set({output})
        return outputs

    def number_of_distinct_outputs(self):
        return len(self.get_distinct_outputs())

    def number_of_exits(self):
        return self.number_of_distinct_outputs()

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
        assert inputs > 0
        input_values = [input_value for input_value in range(256)
            if 2**input_value & inputs != 0]
        if len(input_values) <= 128:
            return str(input_values)
        else:
            not_input_values = [not_input_value for not_input_value in range(256)
                if 2**not_input_value & inputs == 0]
            return "not " + str(not_input_values)

    def get_paths(self, exit_i, index_i = 0):
        path = []
        o2s = self.get_o2s()
        for output in o2s:
            inputs = o2s[output] if o2s[output] < 2**256-1 else 0
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
        # only for i2o and o2s
        assert self.is_consistent()
        return True

    def projection_proto(index):
        # use offset 1 for CFLOBVDDs
        return BVDD.projection(index, 1)

    def apply(self, return_tuple, index = 0, level = 0):
        new_bvdd = type(self)({})
        s2o = self.get_s2o()
        for inputs in s2o:
            output = s2o[inputs]
            if isinstance(output, BVDD):
                new_bvdd.set(inputs, output.apply(return_tuple, index + 1, level))
            elif index < 2**level - 1:
                new_bvdd.set(inputs, BVDD.constant(output).apply(return_tuple, index + 1, level))
            else:
                new_bvdd.set(inputs, return_tuple[output])
        return new_bvdd.reduce_SBDD().reduce_BVDD(index)

    def link(self, bvdd2, return_tuples):
        new_bvdd = type(self)({})
        s2o = self.get_s2o()
        for inputs in s2o:
            output = s2o[inputs]
            if isinstance(output, BVDD):
                new_bvdd.set(inputs, output.link(bvdd2, return_tuples))
            else:
                # apply may reduce to constant
                new_bvdd.set(inputs, bvdd2.apply(return_tuples[output], 1))
        return new_bvdd.reduce_BVDD()

    def swap(self):
        swap2right_bvdd = type(self)({})
        swap2right_exit_i = 1
        new_bvdd = BVDD.constant(1)
        return_tuples = {1:{}}
        s2o = self.get_s2o()
        for inputs in s2o:
            swap2right_bvdd.set(inputs, swap2right_exit_i)
            swap2right_exit_i += 1
            output = s2o[inputs]
            if not isinstance(output, BVDD):
                output = BVDD.constant(output)
            new_bvdd, pt = new_bvdd.pair_product(output)
            return_tuples = dict([(i,
                # pt[i][0] is the exit index of the already paired swap2left BVDDs
                # pt[i][1] is the exit index or output of the next swap2left BVDD being paired
                return_tuples[pt[i][0]] | {len(return_tuples[pt[i][0]]) + 1:pt[i][1]})
                    for i in pt])
        return new_bvdd.link(swap2right_bvdd, return_tuples)

    def unapply(self, b_rt_inv, rt = None, rt_inv = None, index = 0):
        new_bvdd = type(self)({})
        b_rt_inv = b_rt_inv if b_rt_inv is not None else {}
        rt = rt if rt is not None else {}
        rt_inv = rt_inv if rt_inv is not None else {}
        s2o = self.get_s2o()
        for inputs in s2o:
            output = s2o[inputs]
            if isinstance(output, BVDD):
                output, b_rt_inv, rt, rt_inv = output.unapply(b_rt_inv, rt, rt_inv, index + 1)
                new_bvdd.set(inputs, output)
            else:
                if output not in rt_inv:
                    rt_inv[output] = len(rt_inv) + 1
                    if output not in b_rt_inv:
                        b_rt_inv[output] = len(b_rt_inv) + 1
                    rt[rt_inv[output]] = b_rt_inv[output]
                new_bvdd.set(inputs, rt_inv[output])
        return new_bvdd.reduce_SBDD().reduce_BVDD(index), b_rt_inv, rt, rt_inv

    def upsample(self, level, a_rt_inv = None, b_rt_inv = None, b_cs = None, b_rts = None, index = 0):
        a_c = type(self)({})
        a_rt_inv = a_rt_inv if a_rt_inv is not None else {}
        b_rt_inv = b_rt_inv if b_rt_inv is not None else {}
        b_cs = b_cs if b_cs is not None else {}
        b_rts = b_rts if b_rts is not None else {}
        s2o = self.get_s2o()
        for inputs in s2o:
            output = s2o[inputs]
            if isinstance(output, BVDD):
                assert level > 0
                if index < 2**(level - 1) - 1:
                    output, a_rt_inv, b_rt_inv, b_cs, b_rts = output.upsample(level,
                        a_rt_inv, b_rt_inv, b_cs, b_rts, index + 1)
                    a_c.set(inputs, output)
                else:
                    output, b_rt_inv, rt, rt_inv = output.unapply(b_rt_inv)
                    key = (output, tuple(rt.values()))
                    if key not in a_rt_inv:
                        a_rt_inv[key] = len(a_rt_inv) + 1
                        b_cs[a_rt_inv[key]] = output
                        b_rts[a_rt_inv[key]] = rt
                    a_c.set(inputs, a_rt_inv[key])
            else:
                if output not in a_rt_inv:
                    a_rt_inv[output] = len(a_rt_inv) + 1
                    if output not in b_rt_inv:
                        b_rt_inv[output] = len(b_rt_inv) + 1
                    b_cs[a_rt_inv[output]] = BVDD.constant(1)
                    b_rts[a_rt_inv[output]] = {1:b_rt_inv[output]}
                a_c.set(inputs, a_rt_inv[output])
        return a_c.reduce_SBDD().reduce_BVDD(index), a_rt_inv, b_rt_inv, b_cs, b_rts

    def downsample(self, level, bvdds, return_tuples):
        assert level > 0
        # apply to bvdds may reduce to constants
        return self.apply(dict([(exit_i, bvdds[exit_i].apply(return_tuples[exit_i], 1))
            for exit_i in bvdds]), 0, level - 1)

    def tuple2exit(tuple_inv, tuple_ins):
        if tuple_ins not in tuple_inv:
            tuple_inv[tuple_ins] = len(tuple_inv) + 1
        return tuple_inv[tuple_ins]

    def pair_product(self, bvdd2):
        assert type(bvdd2) is type(self)
        pair_inv = {}
        return (self.compute_binary(lambda x, y: BVDD_Node.tuple2exit(pair_inv, (x, y)), bvdd2),
            dict([(pair_inv[pair], pair) for pair in pair_inv]))

    def triple_product(self, bvdd2, bvdd3):
        assert type(bvdd2) is type(self)
        assert type(bvdd3) is type(self)
        triple_inv = {}
        return (self.compute_ternary(lambda x, y, z: BVDD_Node.tuple2exit(triple_inv, (x, y, z)), bvdd2, bvdd3),
            dict([(triple_inv[triple], triple) for triple in triple_inv]))

    def reduce_SBDD(self):
        # only for i2o and o2s
        return self.cache()

    def reduce_BVDD(self, index = 1):
        # dont-care SBDDs are not reduced
        return self.cache()

    def reduce(self, reduction_tuple, index = 0):
        new_bvdd = type(self)({})
        s2o = self.get_s2o()
        for inputs in s2o:
            output = s2o[inputs]
            if isinstance(output, BVDD):
                reduced_output = output.reduce(reduction_tuple, index + 1)
                new_bvdd.set(inputs, reduced_output)
            else:
                new_bvdd.set(inputs, reduction_tuple[output])
        return new_bvdd.reduce_SBDD().reduce_BVDD(index)

    def compute_ite(self, bvdd2, bvdd3):
        assert type(bvdd2) is type(self)
        assert type(bvdd3) is type(self)
        return self.compute_ternary(lambda x, y, z: y if x else z, bvdd2, bvdd3)

    def print_profile():
        print("BVDD cache profile:")
        print(f"nodes: {utilization(BVDD_Node.node_cache_hits, len(BVDD_Node.node_cache))}")

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
            f"{self.number_of_outputs()} output values\n" +
            f"{self.number_of_distinct_outputs()} distinct output values (exits)\n" +
            f"{self.number_of_distinct_inputs()} distinct inputs\n" +
            f"{self.number_of_solutions(output_value)} solutions\n" +
            f"{self.extract(output_value)}")

class SBDD_i2o(BVDD_Node):
    # single-byte decision diagram with naive input-to-output mapping
    def __init__(self, i2o):
        self.i2o = i2o

    def __hash__(self):
        return hash((tuple(self.i2o.items()), tuple(isinstance(o, bool) for o in self.i2o.values())))

    def __eq__(self, bvdd2):
        return self is bvdd2 or (type(bvdd2) is type(self) and self.i2o == bvdd2.i2o)

    def get_s2o(self):
        return self.i2o

    def get_o2s(self):
        o2s = {}
        for input_value in self.i2o:
            BVDD_Node.map(o2s, 2**input_value, self.i2o[input_value])
        return o2s

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
        return self.is_constant() and False in self.i2o.values()

    def is_always_true(self):
        return self.is_constant() and True in self.i2o.values()

    def constant_BVDD(self, output):
        assert (isinstance(output, bool) or
            isinstance(output, int) or
            isinstance(output, type(self)))
        self.i2o = dict([(input_value, output) for input_value in range(256)])
        return self.reduce_SBDD()

    def constant(output_value):
        return SBDD_i2o({}).constant_BVDD(output_value)

    def projection_BVDD(self, index = 0, offset = 0):
        self.i2o = dict([(input_value, input_value + offset) for input_value in range(256)])
        return self.reduce_SBDD()

    def projection(index = 0, offset = 0):
        return SBDD_i2o({}).projection_BVDD(index, offset)

    def compute_unary(self, op):
        return type(self)(dict([(input_value, op(self.i2o[input_value]))
            for input_value in self.i2o])).reduce_SBDD()

    def intersect_binary(self, bvdd2):
        assert type(bvdd2) is type(self)
        # bvdd1.i2o.keys() & bvdd2.i2o.keys()
        return [(input_value, input_value) for input_value in range(256)]

    def compute_binary(self, op, bvdd2):
        assert type(bvdd2) is type(self)
        bvdd1 = self
        return type(self)(dict([(input_value,
            op(bvdd1.i2o[input_value], bvdd2.i2o[input_value]))
                for input_value, _ in bvdd1.intersect_binary(bvdd2)])).reduce_SBDD()

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
                for input_value, _, _ in bvdd1.intersect_ternary(bvdd2, bvdd3)])).reduce_SBDD()

class SBDD_s2o(BVDD_Node):
    # single-byte decision diagram with input-sets-to-output mapping
    def __init__(self, s2o):
        self.s2o = s2o

    def __hash__(self):
        return hash((tuple(self.s2o.items()), tuple(isinstance(o, bool) for o in self.s2o.values())))

    def __eq__(self, bvdd2):
        return self is bvdd2 or (type(bvdd2) is type(self) and self.s2o == bvdd2.s2o)

    def get_s2o(self):
        return self.s2o

    def get_o2s(self):
        assert self.is_reduced()
        return dict([(output, inputs) for inputs, output in self.s2o.items()])

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
        return self.is_constant() and False in self.s2o.values()

    def is_always_true(self):
        return self.is_constant() and True in self.s2o.values()

    def constant_BVDD(self, output):
        assert (isinstance(output, bool) or
            isinstance(output, int) or
            type(output) is type(self))
        self.s2o = {2**256-1:output}
        return self.reduce_SBDD()

    def constant(output_value):
        return SBDD_s2o({}).constant_BVDD(output_value)

    def projection_BVDD(self, index = 0, offset = 0):
        self.s2o = dict([(2**input_value, input_value + offset) for input_value in range(256)])
        return self.reduce_SBDD()

    def projection(index = 0, offset = 0):
        return SBDD_s2o({}).projection_BVDD(index, offset)

    def reduce_SBDD(self):
        if not self.is_reduced():
            o2s = {}
            for inputs in self.s2o:
                BVDD_Node.map(o2s, inputs, self.s2o[inputs])
            self.s2o = dict([(inputs, output) for output, inputs in o2s.items()])
        return self.cache()

    def compute_unary(self, op):
        return type(self)(dict([(inputs, op(self.s2o[inputs])) for inputs in self.s2o])).reduce_SBDD()

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
                for inputs1, inputs2 in bvdd1.intersect_binary(bvdd2)])).reduce_SBDD()

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
                for inputs1, inputs2, inputs3 in bvdd1.intersect_ternary(bvdd2, bvdd3)])).reduce_SBDD()

class SBDD_o2s(BVDD_Node):
    # single-byte decision diagram with output-to-input-sets mapping
    def __init__(self, o2s):
        self.o2s = o2s

    def __hash__(self):
        return hash((tuple(self.o2s.items()), tuple(isinstance(o, bool) for o in self.o2s)))

    def __eq__(self, bvdd2):
        return self is bvdd2 or (type(bvdd2) is type(self) and self.o2s == bvdd2.o2s)

    def get_s2o(self):
        return dict([(inputs, output) for output, inputs in self.o2s.items()])

    def get_o2s(self):
        return self.o2s

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
        return self.is_constant() and False in self.o2s

    def is_always_true(self):
        return self.is_constant() and True in self.o2s

    def constant_BVDD(self, output):
        assert (isinstance(output, bool) or
            isinstance(output, int) or
            type(output) is type(self))
        self.o2s = {output:2**256-1}
        return self.reduce_SBDD()

    def constant(output_value):
        return SBDD_o2s({}).constant_BVDD(output_value)

    def projection_BVDD(self, index = 0, offset = 0):
        self.o2s = dict([(input_value + offset, 2**input_value) for input_value in range(256)])
        return self.reduce_SBDD()

    def projection(index = 0, offset = 0):
        return SBDD_o2s({}).projection_BVDD(index, offset)

    def compute_unary(self, op):
        new_bvdd = type(self)({})
        for output in self.o2s:
            new_bvdd.map(self.o2s[output], op(output))
        return new_bvdd.reduce_SBDD()

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
        return new_bvdd.reduce_SBDD()

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
        return new_bvdd.reduce_SBDD()

class BVDD_uncached(SBDD_o2s):
    def constant(output_value):
        return BVDD({}).constant_BVDD(output_value)

    def projection(index, offset = 0):
        if index == 0:
            return BVDD({}).projection_BVDD(0, offset)
        else:
            return BVDD({}).constant_BVDD(BVDD.projection(index - 1, offset))

    def reduce_BVDD(self, index = 1):
        assert self.is_reduced()
        if index > 0 and self.is_constant():
            # all inputs map to a constant
            return self.get_dont_care_output()
        else:
            # keep dont-care SBDDs at index 0
            return self.cache()

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
                    return output1.compute_ternary(op, output2, output3).reduce_BVDD()
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
        print("BVDD cache profile:")
        print(f"nodes:                {utilization(BVDD_Node.node_cache_hits, len(BVDD_Node.node_cache))}")
        print(f"binary intersection:  {utilization(BVDD_cached.intersect_binary_hits, len(BVDD_cached.intersect_binary_cache))}")
        print(f"ternary intersection: {utilization(BVDD_cached.intersect_ternary_hits, len(BVDD_cached.intersect_ternary_cache))}")
        print(f"constants:            {utilization(BVDD_cached.constant_hits, len(BVDD_cached.constant_cache))}")
        print(f"projection:           {utilization(BVDD_cached.projection_hits, len(BVDD_cached.projection_cache))}")
        print(f"unary operators:      {utilization(BVDD_cached.compute_unary_hits, len(BVDD_cached.compute_unary_cache))}")
        print(f"binary operators:     {utilization(BVDD_cached.compute_binary_hits, len(BVDD_cached.compute_binary_cache))}")
        print(f"ternary operators:    {utilization(BVDD_cached.compute_ternary_hits, len(BVDD_cached.compute_ternary_cache))}")

class BVDD(BVDD_uncached):
    pass