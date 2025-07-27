#!/usr/bin/env python3

# Copyright (c) the Selfie Project authors. All rights reserved.
# Please see the AUTHORS file for details. Use of this source code is
# governed by a BSD license that can be found in the LICENSE file.

# Selfie is a project of the Computational Systems Group at the
# Department of Computer Sciences of the University of Salzburg
# in Austria. For further information and code please refer to:

# selfie.cs.uni-salzburg.at

# Reduced ordered algebraic bitvector decision diagrams (ROABVDDs)

# ------------------------------------------------------------

from bvdd import utilization

class ROABVDD_Exit:
    bump = 0

    exits = {}
    exit_hits = 0

    def new():
        ID = ROABVDD_Exit.bump
        if ID not in ROABVDD_Exit.exits:
            exit = ROABVDD_Exit(ID)
            ROABVDD_Exit.exits[ID] = exit
        else:
            ROABVDD_Exit.exit_hits += 1
            exit = ROABVDD_Exit.exits[ID]
        ROABVDD_Exit.bump += 1
        return exit

    def __init__(self, ID):
        self.ID = ID

    def __repr__(self):
        return f"Exit({self.ID})"

    def number_of_inputs(self):
        return 0

    def number_of_exits(self, exits = {}):
        if self in exits:
            return exits, 0
        else:
            return exits | {self:None}, 1

    def has_exit(self, exit):
        return self is exit

    def extract(self, exit):
        if self.has_exit(exit):
            return exit
        else:
            return None

    def reduce(self):
        return self

    def dealias(new_value, new_values, new_exits):
        new_values = {} if new_values is None else new_values
        new_exits = {} if new_exits is None else new_exits
        if new_value in new_values:
            new_exit = new_values[new_value]
            assert new_exit in new_exits
        else:
            new_exit = ROABVDD_Exit.new()
            assert new_exit not in new_exits, f"exit {new_exit} for value {new_value} already defined in {new_exits}"
            new_values |= {new_value:new_exit}
            new_exits |= {new_exit:new_value}
        return new_values, new_exits, new_exit

    def compute_unary(self, op, old_exits, new_values = None, new_exits = None):
        return ROABVDD_Exit.dealias(op(old_exits[self]), new_values, new_exits)

    def get_binary_exit(self, bvdd, inorder = True):
        if inorder:
            return self, bvdd
        else:
            return bvdd, self

    def apply_binary(self, bvdd, inorder = True):
        if isinstance(bvdd, ROABVDD_Exit):
            return self.get_binary_exit(bvdd, inorder)
        else:
            return bvdd.intersection(self, not inorder)

    def intersection(self, bvdd, inorder = True):
        return self.apply_binary(bvdd, inorder)

    def merge(self, bvdd, inorder = True):
        assert bvdd is None
        return self.get_binary_exit(None, inorder)

    def union(self, bvdd, inorder = True):
        return self.merge(bvdd, inorder)

    def sample_input_values(self):
        return dict()

class ROABVDD_Node:
    bvdds = {}

    intersection_bvdds = {}
    intersection_hits = 0

    union_bvdds = {}
    union_hits = 0

    def __init__(self, var_index, number_of_input_bits):
        self.var_index = var_index
        self.number_of_input_bits = number_of_input_bits
        self.inputs = 0
        self.outputs = {}

    def get_input_values(inputs):
        input_value = 0
        input_values = []
        while inputs != 0:
            if inputs % 2 == 1:
                input_values += [input_value]
            inputs //= 2
            input_value += 1
        return input_values

    def __str__(self):
        string = ""
        for output in self.outputs:
            for input_value in ROABVDD_Node.get_input_values(self.outputs[output]):
                if string:
                    string += ",\n"
                string += f"{input_value}"
                if isinstance(output, ROABVDD_Exit):
                    string += f" -> {output}"
                else:
                    assert isinstance(output, ROABVDD_Node)
                    string += f" & {output}"
        return f"{{{string}}}"

    def __hash__(self):
        return hash((self.var_index, self.number_of_input_bits, self.inputs, tuple(self.outputs), tuple(self.outputs.values())))

    def __eq__(self, bvdd):
        return (isinstance(bvdd, ROABVDD_Node) and
            self.var_index == bvdd.var_index and
            self.number_of_input_bits == bvdd.number_of_input_bits and
            self.inputs == bvdd.inputs and
            self.outputs == bvdd.outputs)

    def number_of_inputs(self):
        n = 0
        for output in self.outputs:
            n += self.outputs[output].bit_count()
            n += output.number_of_inputs()
        return n

    def number_of_exits(self, exits = {}):
        n = 0
        for output in self.outputs:
            exits, m = output.number_of_exits(exits)
            n += m
        return exits, n

    def set_input(self, inputs, output):
        assert 0 < inputs < 2**2**self.number_of_input_bits
        assert not (inputs & self.inputs)
        if output is not None:
            self.inputs |= inputs
            if output not in self.outputs:
                self.outputs[output] = inputs
            else:
                assert not (inputs & self.outputs[output])
                self.outputs[output] |= inputs
        return self

    def has_exit(self, exit):
        for output in self.outputs:
            if output.has_exit(exit):
                return True
        return False

    def extract(self, exit):
        bvdd = ROABVDD_Node(self.var_index, self.number_of_input_bits)
        for output in self.outputs:
            bvdd.set_input(self.outputs[output], output.extract(exit))
        return bvdd.reduce()

    def reduce(self, sort = True):
        if not self.inputs:
            return None
        elif len(self.outputs) == 1:
            # outputs are all isomorphic
            if next(iter(self.outputs.values())) == 2**2**self.number_of_input_bits - 1:
                # remove nodes that have all outputs and all outputs are isomorphic
                return next(iter(self.outputs.keys()))
        elif sort:
            # sort outputs by inputs to obtain canonical ROABVDDs
            self.outputs = dict(sorted(self.outputs.items(), key=lambda x: x[1]))
        # assert: outputs are all isomorphic due to hashing equivalent objects to the same hash
        if self not in ROABVDD_Node.bvdds:
            ROABVDD_Node.bvdds[self] = self
        return ROABVDD_Node.bvdds[self]

    def compute_unary(self, op, old_exits, new_values = None, new_exits = None):
        unary_bvdd = ROABVDD_Node(self.var_index, self.number_of_input_bits)
        for output in self.outputs:
            new_values, new_exits, new_bvdd = output.compute_unary(op,
                old_exits, new_values, new_exits)
            unary_bvdd.set_input(self.outputs[output], new_bvdd)
        # assert outputs of unary_bvdd are sorted
        return new_values, new_exits, unary_bvdd.reduce(False)

    def compute_binary(bvdd, op, left_exits, right_exits, new_values = None, new_exits = None):
        if isinstance(bvdd, tuple):
            if op is None:
                if bvdd[0] is not None:
                    # ignore right exit of merge and constrain
                    new_value = left_exits[bvdd[0]]
                else:
                    # ignore left exit of merge
                    new_value = right_exits[bvdd[1]]
            else:
                new_value = op(left_exits[bvdd[0]], right_exits[bvdd[1]])
            return ROABVDD_Exit.dealias(new_value, new_values, new_exits)
        else:
            assert isinstance(bvdd, ROABVDD_Node)
            binary_bvdd = ROABVDD_Node(bvdd.var_index, bvdd.number_of_input_bits)
            for output in bvdd.outputs:
                new_values, new_exits, new_bvdd = ROABVDD_Node.compute_binary(output, op,
                    left_exits, right_exits, new_values, new_exits)
                binary_bvdd.set_input(bvdd.outputs[output], new_bvdd)
            # assert outputs of binary_bvdd are sorted
            return new_values, new_exits, binary_bvdd.reduce(False)

    def apply_binary(self, bvdd, inorder = True):
        if isinstance(bvdd, ROABVDD_Exit):
            binary_bvdd = ROABVDD_Node(self.var_index, self.number_of_input_bits)
            for output in self.outputs:
                binary_bvdd.set_input(self.outputs[output],
                    output.intersection(bvdd, inorder))
        else:
            assert isinstance(bvdd, ROABVDD_Node)
            if self.var_index > bvdd.var_index:
                binary_bvdd = ROABVDD_Node(bvdd.var_index, bvdd.number_of_input_bits)
                for output in bvdd.outputs:
                    binary_bvdd.set_input(bvdd.outputs[output],
                        self.intersection(output))
            else:
                binary_bvdd = ROABVDD_Node(self.var_index, self.number_of_input_bits)
                if self.var_index < bvdd.var_index:
                    for output in self.outputs:
                        binary_bvdd.set_input(self.outputs[output],
                            output.intersection(bvdd))
                else:
                    assert self.var_index == bvdd.var_index
                    for output1 in self.outputs:
                        inputs1 = self.outputs[output1] & bvdd.inputs
                        if inputs1:
                            for output2 in bvdd.outputs:
                                inputs2 = inputs1 & bvdd.outputs[output2]
                                if inputs2:
                                    binary_bvdd.set_input(inputs2,
                                        output1.intersection(output2))
                                    inputs1 &= ~bvdd.outputs[output2]
        return binary_bvdd.reduce()

    def intersection(self, bvdd, inorder = True):
        if inorder and (self, bvdd) in ROABVDD_Node.intersection_bvdds:
            ROABVDD_Node.intersection_hits += 1
            return ROABVDD_Node.intersection_bvdds[(self, bvdd)]
        elif not inorder and (bvdd, self) in ROABVDD_Node.intersection_bvdds:
            ROABVDD_Node.intersection_hits += 1
            return ROABVDD_Node.intersection_bvdds[(bvdd, self)]
        else:
            binary_bvdd = self.apply_binary(bvdd, inorder)
            if inorder:
                assert (self, bvdd) not in ROABVDD_Node.intersection_bvdds
                ROABVDD_Node.intersection_bvdds[(self, bvdd)] = binary_bvdd
            else:
                assert (bvdd, self) not in ROABVDD_Node.intersection_bvdds
                ROABVDD_Node.intersection_bvdds[(bvdd, self)] = binary_bvdd
            return binary_bvdd

    def merge(self, bvdd, inorder = True):
        if bvdd is None:
            merge_bvdd = ROABVDD_Node(self.var_index, self.number_of_input_bits)
            for output in self.outputs:
                merge_bvdd.set_input(self.outputs[output], output.union(None, inorder))
        else:
            assert isinstance(bvdd, ROABVDD_Node)
            if self.var_index > bvdd.var_index:
                return bvdd.union(self, not inorder)
            else:
                merge_bvdd = ROABVDD_Node(self.var_index, self.number_of_input_bits)
                if self.var_index < bvdd.var_index:
                    for output in self.outputs:
                        # assert: intersection of self and bvdd is empty
                        assert isinstance(output, ROABVDD_Node)
                        merge_bvdd.set_input(self.outputs[output],
                            output.union(bvdd, inorder))
                    if self.inputs < 2**2**self.number_of_input_bits - 1:
                        inputs = 2**2**self.number_of_input_bits - 1 - self.inputs
                        merge_bvdd.set_input(inputs, bvdd.union(None, not inorder))
                else:
                    assert self.var_index == bvdd.var_index
                    for output1 in self.outputs:
                        inputs1 = self.outputs[output1]
                        if inputs1 & bvdd.inputs:
                            for output2 in bvdd.outputs:
                                inputs2 = inputs1 & bvdd.outputs[output2]
                                if inputs2:
                                    # assert: intersection of self and bvdd is empty
                                    assert isinstance(output1, ROABVDD_Node)
                                    assert isinstance(output2, ROABVDD_Node)
                                    merge_bvdd.set_input(inputs2,
                                        output1.union(output2, inorder))
                                    inputs1 &= ~bvdd.outputs[output2]
                        if inputs1:
                            merge_bvdd.set_input(inputs1, output1.union(None, inorder))
                    for output2 in bvdd.outputs:
                        inputs2 = bvdd.outputs[output2] & ~self.inputs
                        if inputs2:
                            merge_bvdd.set_input(inputs2, output2.union(None, not inorder))
        return merge_bvdd.reduce()

    def union(self, bvdd, inorder = True):
        if inorder and (self, bvdd) in ROABVDD_Node.union_bvdds:
            ROABVDD_Node.union_hits += 1
            return ROABVDD_Node.union_bvdds[(self, bvdd)]
        elif not inorder and (bvdd, self) in ROABVDD_Node.union_bvdds:
            ROABVDD_Node.union_hits += 1
            return ROABVDD_Node.union_bvdds[(bvdd, self)]
        else:
            merge_bvdd = self.merge(bvdd, inorder)
            if inorder:
                assert (self, bvdd) not in ROABVDD_Node.union_bvdds
                ROABVDD_Node.union_bvdds[(self, bvdd)] = merge_bvdd
            else:
                assert (bvdd, self) not in ROABVDD_Node.union_bvdds
                ROABVDD_Node.union_bvdds[(bvdd, self)] = merge_bvdd
            return merge_bvdd

    def sample_input_values(self):
        # Grab an arbitrary branch to walk down to
        outp, inp = next(self.outputs.items())

        vals = outp.sample_input_values()
        vals[self.var_index] = next(ROABVDD_Node.get_input_values(inp))
        return vals

class ROABVDD:
    # a reduced ordered algebraic bitvector decision diagram (ROABVDD) is
    # an algebraic decision diagram (ADD) over bitvectors rather than bits

    # given an n-bit bitvector, we use 2**n-bit unsigned integers
    # to represent sets of n-bit bitvector constants that in turn
    # represent branches in ROABVDDs:
    # Theta(2**n)-time set intersection and union with
    # O(2**n/n) and Omega(n*(2**n-1)/2**n) spatial overhead

    def __init__(self, values, exits, bvdd, number_of_output_bits):
        assert isinstance(values, dict)
        assert isinstance(exits, dict)
        assert isinstance(bvdd, ROABVDD_Exit) or isinstance(bvdd, ROABVDD_Node)
        self.values = values
        self.exits = exits
        self.bvdd = bvdd
        self.number_of_output_bits = number_of_output_bits
        ROABVDD_Exit.bump = 0 # exits only need to be unique within ROABVDDs

    def __str__(self):
        return f"{self.values} {self.exits} {self.bvdd}"

    def print_profile():
        print(f"Exit cache utilization: {utilization(ROABVDD_Exit.exit_hits, len(ROABVDD_Exit.exits))}")
        print(f"Node intersection cache utilization: {utilization(ROABVDD_Node.intersection_hits, len(ROABVDD_Node.intersection_bvdds))}")
        print(f"Node union cache utilization: {utilization(ROABVDD_Node.union_hits, len(ROABVDD_Node.union_bvdds))}")

    def number_of_inputs(self):
        return self.bvdd.number_of_inputs()

    def number_of_values(self):
        return len(self.values)

    def is_consistent(self):
        assert self.number_of_values() == len(self.exits)
        assert self.number_of_values() == self.bvdd.number_of_exits()[1]
        for value in self.values:
            assert 0 <= value < 2**self.number_of_output_bits
            assert self.values[value] in self.exits
            assert self.exits[self.values[value]] == value
            assert self.bvdd.has_exit(self.values[value])
        return True

    def is_never_false(self):
        return self.number_of_values() == 1 and True in self.values

    def is_never_true(self):
        return self.number_of_values() == 1 and False in self.values

    def constant(value, number_of_output_bits):
        assert isinstance(value, bool) or isinstance(value, int)
        exit = ROABVDD_Exit.new()
        return ROABVDD({value:exit}, {exit:value}, exit, number_of_output_bits)

    def projection(var_index, number_of_input_bits, number_of_output_bits):
        bvdd = ROABVDD_Node(var_index, number_of_input_bits)
        values = {}
        exits = {}
        for value in range(2**number_of_input_bits):
            value_exit = ROABVDD_Exit.new()
            values |= {value:value_exit}
            exits |= {value_exit:value}
            bvdd.set_input(2**value, value_exit)
        return ROABVDD(values, exits, bvdd, number_of_output_bits)

    def compute_unary(self, op, number_of_output_bits):
        return ROABVDD(*self.bvdd.compute_unary(op, self.exits), number_of_output_bits)

    def compute_binary(self, op, roabvdd, number_of_output_bits):
        assert isinstance(roabvdd, ROABVDD)
        new_bvdd = self.bvdd.intersection(roabvdd.bvdd)
        if new_bvdd is None:
            # TODO: check whether reachable
            return None
        return ROABVDD(*ROABVDD_Node.compute_binary(new_bvdd, op, self.exits, roabvdd.exits),
            number_of_output_bits)

    def get_false_constraint(self):
        if False in self.values:
            if True in self.values:
                new_bvdd = self.bvdd.extract(self.values[False])
                return ROABVDD({False:self.values[False]}, {self.values[False]:False}, new_bvdd,
                    self.number_of_output_bits)
            else:
                return self
        else:
            return None

    def get_true_constraint(self):
        if True in self.values:
            if False in self.values:
                new_bvdd = self.bvdd.extract(self.values[True])
                return ROABVDD({True:self.values[True]}, {self.values[True]:True}, new_bvdd,
                    self.number_of_output_bits)
            else:
                return self
        else:
            return None

    def constrain(self, constraint):
        return self.compute_binary(None, constraint, self.number_of_output_bits)

    def merge(self, roabvdd):
        assert isinstance(self.bvdd, ROABVDD_Node) and isinstance(roabvdd.bvdd, ROABVDD_Node)
        new_bvdd = self.bvdd.union(roabvdd.bvdd)
        assert new_bvdd is not None
        return ROABVDD(*ROABVDD_Node.compute_binary(new_bvdd, None, self.exits, roabvdd.exits),
            self.number_of_output_bits)

    def compute_ite(self, roabvdd2, roabvdd3):
        new_bvdd2 = roabvdd2.constrain(self.get_true_constraint())
        new_bvdd3 = roabvdd3.constrain(self.get_false_constraint())
        return new_bvdd2.merge(new_bvdd3)

    def get_printed_ROABVDD(self, value):
        assert value is True
        return self.get_true_constraint()