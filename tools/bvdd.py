#!/usr/bin/env python3

# Copyright (c) the Selfie Project authors. All rights reserved.
# Please see the AUTHORS file for details. Use of this source code is
# governed by a BSD license that can be found in the LICENSE file.

# Selfie is a project of the Computational Systems Group at the
# Department of Computer Sciences of the University of Salzburg
# in Austria. For further information and code please refer to:

# selfie.cs.uni-salzburg.at

# Bitvector Decision Diagrams (BVDDs)

# Given an n-bit bitvector (currently for n == 8 only),
# we use 2**n-bit unsigned integers to represent
# sets of n-bit bitvector values that in turn represent
# branches in BVDDs over any number of n-bit bitvectors.

# Theta(2**n)-time set intersection (bitwise conjunction) with
# Omega(1/n) and O(2**n/n) spatial overhead

# ------------------------------------------------------------

from __future__ import annotations

import threading
from abc import ABC, abstractmethod
from typing import Any, override


def utilization(hits: int, misses: int) -> str:
    if hits + misses == 0:
        return "0.0%"
    else:
        return (
            f"{round(hits / (hits + misses) * 100, 2)}% ({hits} hits, {misses} misses)"
        )


class BVDD_Node(ABC):
    has_input: int = 0
    no_input: int = 1

    node_cache_lock: threading.Lock = threading.Lock()
    node_cache: dict[BVDD_Node, BVDD_Node] = {}
    node_cache_hits: int = 0

    @abstractmethod
    def __init__(self, mapping: Any) -> None: ...

    @abstractmethod
    def get_dont_care_output(self) -> Any: ...

    @abstractmethod
    def get_o2s(self) -> dict[Any, int]: ...

    @abstractmethod
    def get_s2o(self) -> dict[int, Any]: ...

    @abstractmethod
    def number_of_distinct_SBDD_outputs(self) -> int: ...

    @abstractmethod
    def set(self, inputs: int, output: Any) -> None: ...

    @abstractmethod
    def compute_unary(
        self, op: Any, op_id: str | None = None, bits: int | None = None
    ) -> BVDD_Node: ...

    @abstractmethod
    def compute_binary(
        self,
        op: Any,
        bvdd2: Any,
        op_id: str | None = None,
        bits: int | None = None,
    ) -> BVDD_Node: ...

    @abstractmethod
    def compute_ternary(
        self,
        op: Any,
        bvdd2: Any,
        bvdd3: Any,
        op_id: str | None = None,
        bits: int | None = None,
    ) -> BVDD_Node: ...

    @override
    def __str__(self) -> str:
        if self.is_consistent() and self.is_dont_care():
            # all inputs map to the same output
            return "{" + f"[0,255] -> {self.get_dont_care_output()}" + "}"
        else:
            return (
                "{"
                + ", ".join(
                    [
                        f"{BVDD_Node.get_input_values(inputs)} -> {output}"
                        for output, inputs in self.get_o2s().items()
                    ]
                )
                + "}"
            )

    def cache(self) -> BVDD_Node:
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
        return self.is_dont_care() and isinstance(self.get_dont_care_output(), int)

    def number_of_connections(self) -> int:
        count = 0
        for output in self.get_s2o().values():
            if isinstance(output, BVDD):
                count += output.number_of_connections() + 1
        return count

    def number_of_outputs(self) -> int:
        count = 0
        for output in self.get_s2o().values():
            if isinstance(output, BVDD):
                count += output.number_of_outputs()
            else:
                count += 1
        return count

    def get_distinct_outputs(self) -> set[Any]:
        outputs: set[Any] = set()
        for output in self.get_s2o().values():
            if isinstance(output, BVDD):
                outputs |= output.get_distinct_outputs()
            else:
                outputs |= set({output})
        return outputs

    def number_of_distinct_outputs(self) -> int:
        return len(self.get_distinct_outputs())

    def number_of_exits(self) -> int:
        return self.number_of_distinct_outputs()

    def number_of_distinct_inputs(self, output_value: Any | None = None) -> int:
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
                    assert (
                        output_value is not None or other_count > 0
                    )  # assert output.is_reduced()
                elif output_value is None or output == output_value:
                    other_count = 1
                else:
                    other_count = 0
                count += self.number_of_inputs_for_input(inputs) * other_count
            return count

    def number_of_solutions(self, output_value: Any) -> int:
        return self.number_of_distinct_inputs(output_value)

    @staticmethod
    def get_input_values(inputs: int) -> str:
        assert inputs > 0
        input_values = [
            input_value for input_value in range(256) if 2**input_value & inputs != 0
        ]
        if len(input_values) <= 128:
            return str(input_values)
        else:
            not_input_values = [
                not_input_value
                for not_input_value in range(256)
                if 2**not_input_value & inputs == 0
            ]
            return "not " + str(not_input_values)

    def get_paths(self, exit_i: Any, index_i: int = 0) -> list[Any]:
        path: list[Any] = []
        o2s = self.get_o2s()
        for output in o2s:
            inputs = o2s[output] if o2s[output] < 2**256 - 1 else 0
            if isinstance(output, BVDD):
                other_path = output.get_paths(exit_i, index_i + 1)
                if other_path:
                    path += [([(index_i, inputs)], other_path)]
            elif output == exit_i:
                path += [(index_i, inputs)]
        return path

    def inputs_union(self) -> int:
        # for s2o and o2s only
        union = 0
        for inputs in self.get_s2o():
            assert inputs & union == 0
            union |= inputs
        return union

    def number_of_inputs_for_input(self, inputs: int) -> int:
        # for s2o and o2s only
        return inputs.bit_count()

    def number_of_inputs(self) -> int:
        # for s2o and o2s only
        return self.number_of_inputs_for_input(self.inputs_union())

    @staticmethod
    def map(o2s: dict[Any, int], inputs: int, output: Any) -> None:
        # for s2o and o2s only
        if output not in o2s:
            o2s[output] = inputs
        else:
            o2s[output] |= inputs

    def is_reduced(self) -> bool:
        # only for i2o and o2s
        assert self.is_consistent()
        return True

    def reduce_SBDD(self) -> BVDD_Node:
        # only for i2o and o2s
        return self.cache()

    def reduce_BVDD(self, index: int = 1) -> BVDD_Node:
        # dont-care SBDDs are not reduced
        return self.cache()

    def reduce(self, reduction_tuple: dict[Any, Any], index: int = 0) -> BVDD_Node:
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

    def compute_ite(
        self,
        bvdd2: BVDD_Node,
        bvdd3: BVDD_Node,
        op_id: str | None = None,
        bits: int | None = None,
    ) -> BVDD_Node:
        assert type(bvdd2) is type(self)
        assert type(bvdd3) is type(self)
        return self.compute_ternary(
            lambda x, y, z: y if x else z, bvdd2, bvdd3, op_id, bits
        )

    # for PDDs

    def number_of_partitioned_inputs(self) -> int:
        return self.number_of_distinct_inputs(BVDD_Node.has_input)

    @staticmethod
    def partitioned_constant() -> BVDD_Node:
        return BVDD.constant(BVDD_Node.has_input)

    @staticmethod
    def partitioned_projection(index: int, input_value: Any) -> BVDD_Node:
        return BVDD.projection(index, 0, input_value)

    @staticmethod
    def op_union(output1: Any, output2: Any) -> Any:
        return output1 if output2 == BVDD_Node.no_input else output2

    def union(self, bvdd2: BVDD_Node) -> BVDD_Node:
        assert type(bvdd2) is type(self)
        return self.compute_binary(
            lambda x, y: BVDD_uncached.op_binary(BVDD_Node.op_union, x, y, "union", 1),
            bvdd2,
            "union",
        )

    @staticmethod
    def op_intersection(output1: Any, output2: Any, output3: Any = 0) -> Any:
        return (
            output1
            if output1 == BVDD_Node.no_input
            else output2
            if output2 == BVDD_Node.no_input
            else output3
        )

    def intersection(
        self, bvdd2: BVDD_Node, bvdd3: BVDD_Node | None = None
    ) -> BVDD_Node:
        assert type(bvdd2) is type(self)
        if bvdd3 is None:
            return self.compute_binary(
                lambda x, y: BVDD_uncached.op_binary(
                    BVDD_Node.op_intersection, x, y, "intersection", 1
                ),
                bvdd2,
                "intersection",
            )
        else:
            assert type(bvdd3) is type(self)
            return self.compute_ternary(
                lambda x, y, z: BVDD_uncached.op_ternary(
                    BVDD_Node.op_intersection, x, y, z, "intersection", 1
                ),
                bvdd2,
                bvdd3,
                "intersection",
            )

    def is_not_empty(self) -> bool:
        return not (
            self.is_constant() and self.get_dont_care_output() == BVDD_Node.no_input
        )

    def is_not_full(self) -> bool:
        return not (
            self.is_constant() and self.get_dont_care_output() == BVDD_Node.has_input
        )

    # for CFLOBVDDs

    @staticmethod
    def projection_proto(index: int, input_value: Any | None = None) -> BVDD_Node:
        # use offset 1 for CFLOBVDDs
        return BVDD.projection(index, 1, input_value)

    def apply(
        self, return_tuple: dict[Any, Any], index: int = 0, level: int = 0
    ) -> BVDD_Node:
        new_bvdd = type(self)({})
        s2o = self.get_s2o()
        for inputs in s2o:
            output = s2o[inputs]
            if isinstance(output, BVDD):
                new_bvdd.set(inputs, output.apply(return_tuple, index + 1, level))
            elif index < 2**level - 1:
                new_bvdd.set(
                    inputs, BVDD.constant(output).apply(return_tuple, index + 1, level)
                )
            else:
                new_bvdd.set(inputs, return_tuple[output])
        return new_bvdd.reduce_SBDD().reduce_BVDD(index)

    def link(self, bvdd2: BVDD_Node, return_tuples: dict[Any, Any]) -> BVDD_Node:
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

    def swap(self) -> BVDD_Node:
        swap2right_bvdd = type(self)({})
        swap2right_exit_i = 1
        new_bvdd = BVDD.constant(1)
        return_tuples = {1: {}}
        s2o = self.get_s2o()
        for inputs in s2o:
            swap2right_bvdd.set(inputs, swap2right_exit_i)
            swap2right_exit_i += 1
            output = s2o[inputs]
            if not isinstance(output, BVDD):
                output = BVDD.constant(output)
            new_bvdd, pt = new_bvdd.pair_product(output)
            return_tuples = dict(
                [
                    (
                        i,
                        # pt[i][0] is the exit index of the already paired swap2left BVDDs
                        # pt[i][1] is the exit index or output of the next swap2left BVDD being paired
                        return_tuples[pt[i][0]]
                        | {len(return_tuples[pt[i][0]]) + 1: pt[i][1]},
                    )
                    for i in pt
                ]
            )
        return new_bvdd.link(swap2right_bvdd, return_tuples)

    def unapply(
        self,
        b_rt_inv: dict[Any, int] | None,
        rt: dict[int, int] | None = None,
        rt_inv: dict[Any, int] | None = None,
        index: int = 0,
    ) -> tuple[BVDD_Node, dict[Any, int], dict[int, int], dict[Any, int]]:
        new_bvdd = type(self)({})
        b_rt_inv = b_rt_inv if b_rt_inv is not None else {}
        rt = rt if rt is not None else {}
        rt_inv = rt_inv if rt_inv is not None else {}
        s2o = self.get_s2o()
        for inputs in s2o:
            output = s2o[inputs]
            if isinstance(output, BVDD):
                output, b_rt_inv, rt, rt_inv = output.unapply(
                    b_rt_inv, rt, rt_inv, index + 1
                )
                new_bvdd.set(inputs, output)
            else:
                if output not in rt_inv:
                    rt_inv[output] = len(rt_inv) + 1
                    if output not in b_rt_inv:
                        b_rt_inv[output] = len(b_rt_inv) + 1
                    rt[rt_inv[output]] = b_rt_inv[output]
                new_bvdd.set(inputs, rt_inv[output])
        return new_bvdd.reduce_SBDD().reduce_BVDD(index), b_rt_inv, rt, rt_inv

    def upsample(
        self,
        level: int,
        a_rt_inv: dict[Any, int] | None = None,
        b_rt_inv: dict[Any, int] | None = None,
        b_cs: dict[int, BVDD_Node] | None = None,
        b_rts: dict[int, dict[int, int]] | None = None,
        index: int = 0,
    ) -> tuple[
        BVDD_Node,
        dict[Any, int],
        dict[Any, int],
        dict[int, BVDD_Node],
        dict[int, dict[int, int]],
    ]:
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
                if index < 2 ** (level - 1) - 1:
                    output, a_rt_inv, b_rt_inv, b_cs, b_rts = output.upsample(
                        level, a_rt_inv, b_rt_inv, b_cs, b_rts, index + 1
                    )
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
                    b_rts[a_rt_inv[output]] = {1: b_rt_inv[output]}
                a_c.set(inputs, a_rt_inv[output])
        return a_c.reduce_SBDD().reduce_BVDD(index), a_rt_inv, b_rt_inv, b_cs, b_rts

    def downsample(
        self,
        level: int,
        bvdds: dict[int, BVDD_Node],
        return_tuples: dict[int, dict[Any, Any]],
    ) -> BVDD_Node:
        assert level > 0
        # apply to bvdds may reduce to constants
        return self.apply(
            dict(
                [
                    (exit_i, bvdds[exit_i].apply(return_tuples[exit_i], 1))
                    for exit_i in bvdds
                ]
            ),
            0,
            level - 1,
        )

    @staticmethod
    def tuple2exit(tuple_inv: dict[Any, int], tuple_ins: Any) -> int:
        if tuple_ins not in tuple_inv:
            tuple_inv[tuple_ins] = len(tuple_inv) + 1
        return tuple_inv[tuple_ins]

    def pair_product(
        self, bvdd2: BVDD_Node
    ) -> tuple[BVDD_Node, dict[int, tuple[Any, Any]]]:
        assert type(bvdd2) is type(self)
        pair_inv: dict[tuple[Any, Any], int] = {}
        return (
            self.compute_binary(
                lambda x, y: BVDD_Node.tuple2exit(pair_inv, (x, y)), bvdd2
            ),
            dict([(pair_inv[pair], pair) for pair in pair_inv]),
        )

    def triple_product(
        self, bvdd2: BVDD_Node, bvdd3: BVDD_Node
    ) -> tuple[BVDD_Node, dict[int, tuple[Any, Any, Any]]]:
        assert type(bvdd2) is type(self)
        assert type(bvdd3) is type(self)
        triple_inv: dict[tuple[Any, Any, Any], int] = {}
        return (
            self.compute_ternary(
                lambda x, y, z: BVDD_Node.tuple2exit(triple_inv, (x, y, z)),
                bvdd2,
                bvdd3,
            ),
            dict([(triple_inv[triple], triple) for triple in triple_inv]),
        )

    @staticmethod
    def print_profile() -> None:
        print("BVDD cache profile:")
        print(
            f"nodes: {utilization(BVDD_Node.node_cache_hits, len(BVDD_Node.node_cache))}"
        )

    def extract(self, output_value: Any) -> BVDD_Node:
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

    def get_printed_inputs(self, output_value: Any) -> str:
        return (
            f"{type(self).__name__}:\n"
            + f"{self.number_of_connections()} connections\n"
            + f"{self.number_of_outputs()} output values\n"
            + f"{self.number_of_distinct_outputs()} distinct output values (exits)\n"
            + f"{self.number_of_distinct_inputs()} distinct inputs\n"
            + f"{self.number_of_solutions(output_value)} solutions\n"
            + f"{self.extract(output_value)}"
        )


class SBDD_i2o(BVDD_Node):
    # single-byte decision diagram with naive input-to-output mapping
    i2o: dict[int, Any]

    def __init__(self, i2o: dict[int, Any]) -> None:
        self.i2o = i2o

    @override
    def __hash__(self) -> int:
        return hash(
            (
                tuple(self.i2o.items()),
                any(isinstance(o, bool) for o in self.i2o.values()),
            )
        )

    @override
    def __eq__(self, bvdd2: object) -> bool:
        return self is bvdd2 or (type(bvdd2) is type(self) and self.i2o == bvdd2.i2o)

    @override
    def get_s2o(self) -> dict[int, Any]:
        return self.i2o

    @override
    def get_o2s(self) -> dict[Any, int]:
        o2s: dict[Any, int] = {}
        for input_value in self.i2o:
            BVDD_Node.map(o2s, 2**input_value, self.i2o[input_value])
        return o2s

    @override
    def set(self, inputs: int, output: Any) -> None:
        assert 0 <= inputs < 256
        assert inputs not in self.i2o
        self.i2o[inputs] = output

    @override
    def number_of_inputs_for_input(self, inputs: int) -> int:
        assert 0 <= inputs < 256
        return 1

    @override
    def number_of_inputs(self) -> int:
        return len(self.i2o)

    def number_of_SBDD_outputs(self) -> int:
        return len(self.i2o.values())

    @override
    def number_of_distinct_SBDD_outputs(self) -> int:
        return len(set(self.i2o.values()))

    @override
    def get_dont_care_output(self) -> Any:
        assert self.is_dont_care()
        return next(iter(self.i2o.values()))

    def is_always_false(self) -> bool:
        return self.is_constant() and False in self.i2o.values()

    def is_always_true(self) -> bool:
        return self.is_constant() and True in self.i2o.values()

    def constant_BVDD(self, output: Any) -> BVDD_Node:
        assert (
            isinstance(output, bool)
            or isinstance(output, int)
            or isinstance(output, type(self))
        )
        self.i2o = dict([(input_value, output) for input_value in range(256)])
        return self.reduce_SBDD()

    @staticmethod
    def constant(output_value: Any) -> BVDD_Node:
        return SBDD_i2o({}).constant_BVDD(output_value)

    def projection_BVDD(self, index: int = 0, offset: int = 0) -> BVDD_Node:
        self.i2o = dict(
            [(input_value, input_value + offset) for input_value in range(256)]
        )
        return self.reduce_SBDD()

    @staticmethod
    def projection(index: int = 0, offset: int = 0) -> BVDD_Node:
        return SBDD_i2o({}).projection_BVDD(index, offset)

    @override
    def compute_unary(
        self, op: Any, op_id: str | None = None, bits: int | None = None
    ) -> BVDD_Node:
        return type(self)(
            dict([(input_value, op(self.i2o[input_value])) for input_value in self.i2o])
        ).reduce_SBDD()

    def get_s(self) -> BVDD_Node:
        new_bvdd = type(self)({})
        new_bvdd.i2o = dict(
            [
                (input_value, input_value_i)
                for input_value_i, input_value in enumerate(self.i2o)
            ]
        )
        return new_bvdd

    def intersect_binary(self, bvdd2: SBDD_i2o) -> list[tuple[int, int]]:
        assert type(bvdd2) is type(self)
        # bvdd1.i2o.keys() & bvdd2.i2o.keys()
        return [(input_value, input_value) for input_value in range(256)]

    @override
    def compute_binary(
        self,
        op: Any,
        bvdd2: SBDD_i2o,
        op_id: str | None = None,
        bits: int | None = None,
    ) -> BVDD_Node:
        assert type(bvdd2) is type(self)
        bvdd1 = self
        return type(self)(
            dict(
                [
                    (input_value, op(bvdd1.i2o[input_value], bvdd2.i2o[input_value]))
                    for input_value, _ in bvdd1.intersect_binary(bvdd2)
                ]
            )
        ).reduce_SBDD()

    def intersect_ternary(
        self, bvdd2: SBDD_i2o, bvdd3: SBDD_i2o
    ) -> list[tuple[int, int, int]]:
        assert type(bvdd2) is type(self)
        assert type(bvdd3) is type(self)
        # bvdd1.i2o.keys() & bvdd2.i2o.keys() & bvdd3.i2o.keys()
        return [(input_value, input_value, input_value) for input_value in range(256)]

    @override
    def compute_ternary(
        self,
        op: Any,
        bvdd2: SBDD_i2o,
        bvdd3: SBDD_i2o,
        op_id: str | None = None,
        bits: int | None = None,
    ) -> BVDD_Node:
        assert type(bvdd2) is type(self)
        assert type(bvdd3) is type(self)
        bvdd1 = self
        return type(self)(
            dict(
                [
                    (
                        input_value,
                        op(
                            bvdd1.i2o[input_value],
                            bvdd2.i2o[input_value],
                            bvdd3.i2o[input_value],
                        ),
                    )
                    for input_value, _, _ in bvdd1.intersect_ternary(bvdd2, bvdd3)
                ]
            )
        ).reduce_SBDD()


class SBDD_s2o(BVDD_Node):
    # single-byte decision diagram with input-sets-to-output mapping
    s2o: dict[int, Any]

    def __init__(self, s2o: dict[int, Any]) -> None:
        self.s2o = s2o

    @override
    def __hash__(self) -> int:
        return hash(
            (
                tuple(self.s2o.items()),
                any(isinstance(o, bool) for o in self.s2o.values()),
            )
        )

    @override
    def __eq__(self, bvdd2: object) -> bool:
        return self is bvdd2 or (type(bvdd2) is type(self) and self.s2o == bvdd2.s2o)

    @override
    def get_s2o(self) -> dict[int, Any]:
        return self.s2o

    @override
    def get_o2s(self) -> dict[Any, int]:
        assert self.is_reduced()
        return dict([(output, inputs) for inputs, output in self.s2o.items()])

    @override
    def set(self, inputs: int, output: Any) -> None:
        assert inputs not in self.s2o
        self.s2o[inputs] = output

    def number_of_SBDD_outputs(self) -> int:
        return len(self.s2o.values())

    @override
    def number_of_distinct_SBDD_outputs(self) -> int:
        return len(set(self.s2o.values()))

    @override
    def get_dont_care_output(self) -> Any:
        assert self.is_dont_care()
        return next(iter(self.s2o.values()))

    @override
    def is_reduced(self) -> bool:
        return self.number_of_SBDD_outputs() == self.number_of_distinct_SBDD_outputs()

    def is_always_false(self) -> bool:
        return self.is_constant() and False in self.s2o.values()

    def is_always_true(self) -> bool:
        return self.is_constant() and True in self.s2o.values()

    def constant_BVDD(self, output: Any) -> BVDD_Node:
        assert (
            isinstance(output, bool)
            or isinstance(output, int)
            or type(output) is type(self)
        )
        self.s2o = {2**256 - 1: output}
        return self.reduce_SBDD()

    @staticmethod
    def constant(output_value: Any) -> BVDD_Node:
        return SBDD_s2o({}).constant_BVDD(output_value)

    def projection_BVDD(self, index: int = 0, offset: int = 0) -> BVDD_Node:
        self.s2o = dict(
            [(2**input_value, input_value + offset) for input_value in range(256)]
        )
        return self.reduce_SBDD()

    @staticmethod
    def projection(index: int = 0, offset: int = 0) -> BVDD_Node:
        return SBDD_s2o({}).projection_BVDD(index, offset)

    @override
    def reduce_SBDD(self) -> BVDD_Node:
        if not self.is_reduced():
            o2s: dict[Any, int] = {}
            for inputs in self.s2o:
                BVDD_Node.map(o2s, inputs, self.s2o[inputs])
            self.s2o = dict([(inputs, output) for output, inputs in o2s.items()])
        return self.cache()

    @override
    def compute_unary(
        self, op: Any, op_id: str | None = None, bits: int | None = None
    ) -> BVDD_Node:
        return type(self)(
            dict([(inputs, op(self.s2o[inputs])) for inputs in self.s2o])
        ).reduce_SBDD()

    def get_s(self) -> BVDD_Node:
        new_bvdd = type(self)({})
        new_bvdd.s2o = dict(
            [(inputs, inputs_i) for inputs_i, inputs in enumerate(self.s2o)]
        )
        return new_bvdd

    def intersect_binary(self, bvdd2: SBDD_s2o) -> list[tuple[int, int, int]]:
        assert type(bvdd2) is type(self)
        bvdd1 = self
        return [
            (inputs1 & inputs2, inputs1_i, inputs2_i)
            for inputs1_i, inputs1 in enumerate(bvdd1.s2o)
            for inputs2_i, inputs2 in enumerate(bvdd2.s2o)
            if inputs1 & inputs2
        ]

    @override
    def compute_binary(
        self,
        op: Any,
        bvdd2: SBDD_s2o,
        op_id: str | None = None,
        bits: int | None = None,
    ) -> BVDD_Node:
        assert type(bvdd2) is type(self)
        bvdd1 = self
        bvdd1_s2o = list(bvdd1.s2o.values())
        bvdd2_s2o = list(bvdd2.s2o.values())
        return type(self)(
            dict(
                [
                    (inputs, op(bvdd1_s2o[inputs1_i], bvdd2_s2o[inputs2_i]))
                    for inputs, inputs1_i, inputs2_i in bvdd1.intersect_binary(bvdd2)
                ]
            )
        ).reduce_SBDD()

    def intersect_ternary(
        self, bvdd2: SBDD_s2o, bvdd3: SBDD_s2o
    ) -> list[tuple[int, int, int, int]]:
        assert type(bvdd2) is type(self)
        assert type(bvdd3) is type(self)
        bvdd1 = self
        return [
            (inputs1 & inputs2 & inputs3, inputs1_i, inputs2_i, inputs3_i)
            for inputs1_i, inputs1 in enumerate(bvdd1.s2o)
            for inputs2_i, inputs2 in enumerate(bvdd2.s2o)
            for inputs3_i, inputs3 in enumerate(bvdd3.s2o)
            if inputs1 & inputs2 & inputs3
        ]

    @override
    def compute_ternary(
        self,
        op: Any,
        bvdd2: SBDD_s2o,
        bvdd3: SBDD_s2o,
        op_id: str | None = None,
        bits: int | None = None,
    ) -> BVDD_Node:
        assert type(bvdd2) is type(self)
        assert type(bvdd3) is type(self)
        bvdd1 = self
        bvdd1_s2o = list(bvdd1.s2o.values())
        bvdd2_s2o = list(bvdd2.s2o.values())
        bvdd3_s2o = list(bvdd3.s2o.values())
        return type(self)(
            dict(
                [
                    (
                        inputs,
                        op(
                            bvdd1_s2o[inputs1_i],
                            bvdd2_s2o[inputs2_i],
                            bvdd3_s2o[inputs3_i],
                        ),
                    )
                    for inputs, inputs1_i, inputs2_i, inputs3_i in bvdd1.intersect_ternary(
                        bvdd2, bvdd3
                    )
                ]
            )
        ).reduce_SBDD()


class SBDD_o2s(BVDD_Node):
    # single-byte decision diagram with output-to-input-sets mapping
    o2s: dict[Any, int]

    def __init__(self, o2s: dict[Any, int]) -> None:
        self.o2s = o2s

    @override
    def __hash__(self) -> int:
        return hash(
            (tuple(self.o2s.items()), any(isinstance(o, bool) for o in self.o2s))
        )

    @override
    def __eq__(self, bvdd2: object) -> bool:
        return self is bvdd2 or (type(bvdd2) is type(self) and self.o2s == bvdd2.o2s)

    @override
    def get_s2o(self) -> dict[int, Any]:
        return dict([(inputs, output) for output, inputs in self.o2s.items()])

    @override
    def get_o2s(self) -> dict[Any, int]:
        return self.o2s

    def SBDD_o2s_map(self, inputs: int, output: Any) -> None:
        BVDD_Node.map(self.o2s, inputs, output)

    @override
    def set(self, inputs: int, output: Any) -> None:
        self.SBDD_o2s_map(inputs, output)

    def number_of_SBDD_outputs(self) -> int:
        return len(self.o2s)

    @override
    def number_of_distinct_SBDD_outputs(self) -> int:
        return self.number_of_SBDD_outputs()

    @override
    def get_dont_care_output(self) -> Any:
        assert self.is_dont_care()
        return next(iter(self.o2s))

    def is_always_false(self) -> bool:
        return self.is_constant() and False in self.o2s

    def is_always_true(self) -> bool:
        return self.is_constant() and True in self.o2s

    def constant_BVDD(self, output: Any) -> BVDD_Node:
        assert (
            isinstance(output, bool)
            or isinstance(output, int)
            or type(output) is type(self)
            or output is None
        )
        self.o2s = {output: 2**256 - 1}
        return self.reduce_SBDD()

    @staticmethod
    def constant(output_value: Any) -> BVDD_Node:
        return SBDD_o2s({}).constant_BVDD(output_value)

    def projection_BVDD(
        self, index: int = 0, offset: int = 0, input_value: Any | None = None
    ) -> BVDD_Node:
        if input_value is not None:
            if isinstance(input_value, int):
                self.o2s = {
                    BVDD_Node.has_input + offset: 2**input_value,
                    BVDD_Node.no_input + offset: (2**256 - 1) & ~(2**input_value),
                }
            else:
                # (0,8) normalizes to input_value (+ 0) with 8 bits
                self.o2s = {(0, 8): 2**256 - 1}
        else:
            self.o2s = dict(
                [(input_value + offset, 2**input_value) for input_value in range(256)]
            )
        return self.reduce_SBDD()

    @staticmethod
    def projection(
        index: int = 0, offset: int = 0, input_value: Any | None = None
    ) -> BVDD_Node:
        return SBDD_o2s({}).projection_BVDD(index, offset, input_value)

    @staticmethod
    def are_not_normalized_outputs(output1: Any, output2: Any, output3: Any) -> bool:
        return (
            not isinstance(output1, tuple)
            and (output2 is None or not isinstance(output2, tuple))
            and (output3 is None or not isinstance(output3, tuple))
        )

    @staticmethod
    def are_not_BVDD(output1: Any, output2: Any, output3: Any) -> bool:
        return (
            not isinstance(output1, BVDD)
            and (output2 is None or not isinstance(output2, BVDD))
            and (output3 is None or not isinstance(output3, BVDD))
        )

    @staticmethod
    def normalize(inputs: int, output_value: Any, bits: int | None) -> Any:
        if bits is None:
            bits = 0
        if (
            isinstance(output_value, BVDD)
            or isinstance(output_value, bool)
            or abs(bits) <= 64
        ):
            # TODO: determine threshold on bits
            return output_value
        else:
            assert inputs > 0
            if inputs & (inputs - 1) != 0:
                # multiple input values
                return output_value
            else:
                # just one input value, make output value dependent on input value
                input_value = inputs.bit_length() - 1
                return output_value - input_value if bits >= 0 else (
                    2**-bits - output_value
                ) - input_value, bits

    @staticmethod
    def denormalize(input_value: int, output: Any) -> Any:
        if not isinstance(output, tuple):
            return output
        else:
            normalized_value = output[0]
            bits = output[1]
            assert 0 <= input_value < 256
            return (
                input_value + normalized_value
                if bits >= 0
                else 2**-bits - (input_value + normalized_value)
            )

    @staticmethod
    def denormalize_op(
        op: Any,
        input_value: int,
        output1: Any,
        output2: Any | None = None,
        output3: Any | None = None,
    ) -> Any:
        output1_value = SBDD_o2s.denormalize(input_value, output1)
        if output2 is None and output2 is None:
            return op(output1_value)
        else:
            output2_value = SBDD_o2s.denormalize(input_value, output2)
            if output3 is None:
                return op(output1_value, output2_value)
            else:
                output3_value = SBDD_o2s.denormalize(input_value, output3)
                return op(output1_value, output2_value, output3_value)

    def normalized_map(
        self,
        bits: int | None,
        op: Any,
        op_id: str | None,
        inputs: int,
        output1: Any,
        output2: Any | None = None,
        output3: Any | None = None,
    ) -> None:
        if SBDD_o2s.are_not_normalized_outputs(output1, output2, output3):
            self.SBDD_o2s_map(
                inputs,
                SBDD_o2s.normalize(
                    inputs,
                    SBDD_o2s.denormalize_op(op, inputs, output1, output2, output3),
                    bits,
                ),
            )
        else:
            if SBDD_o2s.are_not_BVDD(output1, output2, output3):
                if op_id == "ite":
                    self.SBDD_o2s_map(inputs, op(output1, output2, output3))
                    return
                # TODO: pass normalized outputs to other op
            while inputs > 0:
                input_value = (inputs & -inputs).bit_length() - 1
                self.SBDD_o2s_map(
                    2**input_value,
                    SBDD_o2s.normalize(
                        2**input_value,
                        SBDD_o2s.denormalize_op(
                            op, input_value, output1, output2, output3
                        ),
                        bits,
                    ),
                )
                inputs &= inputs - 1

    @override
    def compute_unary(
        self, op: Any, op_id: str | None = None, bits: int | None = None
    ) -> BVDD_Node:
        new_bvdd = type(self)({})
        for output in self.o2s:
            new_bvdd.normalized_map(bits, op, op_id, self.o2s[output], output)
        return new_bvdd.reduce_SBDD()

    def get_s(self) -> BVDD_Node:
        new_bvdd = type(self)({})
        new_bvdd.o2s = dict(enumerate(self.o2s.values()))
        return new_bvdd

    def intersect_binary(self, bvdd2: SBDD_o2s) -> list[tuple[int, int, int]]:
        assert type(bvdd2) is type(self)
        bvdd1 = self
        return [
            (
                bvdd1.o2s[output1] & bvdd2.o2s[output2],
                output1_i,
                output2_i,
            )
            for output1_i, output1 in enumerate(bvdd1.o2s)
            for output2_i, output2 in enumerate(bvdd2.o2s)
            if bvdd1.o2s[output1] & bvdd2.o2s[output2]
        ]

    @override
    def compute_binary(
        self,
        op: Any,
        bvdd2: SBDD_o2s,
        op_id: str | None = None,
        bits: int | None = None,
    ) -> BVDD_Node:
        assert type(bvdd2) is type(self)
        bvdd1 = self
        bvdd1_o2s = list(bvdd1.o2s)
        bvdd2_o2s = list(bvdd2.o2s)
        new_bvdd = type(self)({})
        for inputs, output1_i, output2_i in bvdd1.intersect_binary(bvdd2):
            new_bvdd.normalized_map(
                bits,
                op,
                op_id,
                inputs,
                bvdd1_o2s[output1_i],
                bvdd2_o2s[output2_i],
            )
        return new_bvdd.reduce_SBDD()

    def intersect_ternary(
        self, bvdd2: SBDD_o2s, bvdd3: SBDD_o2s
    ) -> list[tuple[int, int, int, int]]:
        assert type(bvdd2) is type(self)
        assert type(bvdd3) is type(self)
        bvdd1 = self
        return [
            (
                bvdd1.o2s[output1] & bvdd2.o2s[output2] & bvdd3.o2s[output3],
                output1_i,
                output2_i,
                output3_i,
            )
            for output1_i, output1 in enumerate(bvdd1.o2s)
            for output2_i, output2 in enumerate(bvdd2.o2s)
            for output3_i, output3 in enumerate(bvdd3.o2s)
            if bvdd1.o2s[output1] & bvdd2.o2s[output2] & bvdd3.o2s[output3]
        ]

    @override
    def compute_ternary(
        self,
        op: Any,
        bvdd2: SBDD_o2s,
        bvdd3: SBDD_o2s,
        op_id: str | None = None,
        bits: int | None = None,
    ) -> BVDD_Node:
        assert type(bvdd2) is type(self)
        assert type(bvdd3) is type(self)
        bvdd1 = self
        bvdd1_o2s = list(bvdd1.o2s)
        bvdd2_o2s = list(bvdd2.o2s)
        bvdd3_o2s = list(bvdd3.o2s)
        new_bvdd = type(self)({})
        for inputs, output1_i, output2_i, output3_i in bvdd1.intersect_ternary(
            bvdd2, bvdd3
        ):
            new_bvdd.normalized_map(
                bits,
                op,
                op_id,
                inputs,
                bvdd1_o2s[output1_i],
                bvdd2_o2s[output2_i],
                bvdd3_o2s[output3_i],
            )
        return new_bvdd.reduce_SBDD()


class BVDD_uncached(SBDD_o2s):
    @staticmethod
    def constant(output_value: Any) -> BVDD_Node:
        return BVDD({}).constant_BVDD(output_value)

    @staticmethod
    def projection(
        index: int = 0, offset: int = 0, input_value: Any | None = None
    ) -> BVDD_Node:
        if index == 0:
            return BVDD({}).projection_BVDD(0, offset, input_value)
        else:
            return BVDD({}).constant_BVDD(
                BVDD.projection(index - 1, offset, input_value)
            )

    @override
    def reduce_BVDD(self, index: int = 1) -> Any:
        assert self.is_reduced()
        if index > 0 and self.is_constant():
            # all inputs map to a constant
            return self.get_dont_care_output()
        else:
            # keep dont-care SBDDs at index 0
            return self.cache()

    @staticmethod
    def op_unary(op: Any, output1: Any, op_id: str | None, bits: int | None) -> Any:
        if isinstance(output1, BVDD):
            return output1.compute_unary(op, op_id, bits).reduce_BVDD()
        else:
            return op(output1)

    @override
    def compute_unary(
        self, op: Any, op_id: str | None = None, bits: int | None = None
    ) -> BVDD_Node:
        return super().compute_unary(
            lambda x: BVDD.op_unary(op, x, op_id, bits), op_id, bits
        )

    @staticmethod
    def op_binary(
        op: Any,
        output1: Any,
        output2: Any,
        op_id: str | None,
        bits: int | None,
    ) -> Any:
        if not (isinstance(output1, BVDD) or isinstance(output2, BVDD)):
            return op(output1, output2)
        else:
            output1 = output1 if isinstance(output1, BVDD) else BVDD.constant(output1)
            output2 = output2 if isinstance(output2, BVDD) else BVDD.constant(output2)
            return output1.compute_binary(op, output2, op_id, bits).reduce_BVDD()

    @override
    def compute_binary(
        self,
        op: Any,
        bvdd2: Any,
        op_id: str | None = None,
        bits: int | None = None,
    ) -> BVDD_Node:
        return super().compute_binary(
            lambda x, y: BVDD.op_binary(op, x, y, op_id, bits), bvdd2, op_id, bits
        )

    @staticmethod
    def op_ternary(
        op: Any,
        output1: Any,
        output2: Any,
        output3: Any,
        op_id: str | None,
        bits: int | None,
    ) -> Any:
        if not (
            isinstance(output1, BVDD)
            or isinstance(output2, BVDD)
            or isinstance(output3, BVDD)
        ):
            return op(output1, output2, output3)
        else:
            output1 = output1 if isinstance(output1, BVDD) else BVDD.constant(output1)
            output2 = output2 if isinstance(output2, BVDD) else BVDD.constant(output2)
            output3 = output3 if isinstance(output3, BVDD) else BVDD.constant(output3)
            return output1.compute_ternary(
                op, output2, output3, op_id, bits
            ).reduce_BVDD()

    @override
    def compute_ternary(
        self,
        op: Any,
        bvdd2: Any,
        bvdd3: Any,
        op_id: str | None = None,
        bits: int | None = None,
    ) -> BVDD_Node:
        return super().compute_ternary(
            lambda x, y, z: BVDD.op_ternary(op, x, y, z, op_id, bits),
            bvdd2,
            bvdd3,
            op_id,
            bits,
        )


class BVDD_cached(BVDD_uncached):
    intersect_binary_lock: threading.Lock = threading.Lock()
    intersect_binary_cache: dict[
        tuple[BVDD_Node, BVDD_Node], list[tuple[int, int, int]]
    ] = {}
    intersect_binary_hits: int = 0

    @override
    def intersect_binary(
        self, bvdd2: SBDD_o2s, intersection: list[tuple[int, int, int]] | None = None
    ) -> list[tuple[int, int, int]]:
        s1 = self.get_s()
        s2 = bvdd2.get_s()
        if (s1, s2) in BVDD_cached.intersect_binary_cache:
            BVDD_cached.intersect_binary_hits += 1
        elif intersection:
            # lock is acquired
            BVDD_cached.intersect_binary_cache[(s1, s2)] = intersection
        else:
            # concurrent without acquiring lock
            intersection = super().intersect_binary(bvdd2)
            with BVDD_cached.intersect_binary_lock:
                return self.intersect_binary(bvdd2, intersection)
        return BVDD_cached.intersect_binary_cache[(s1, s2)]

    intersect_ternary_lock: threading.Lock = threading.Lock()
    intersect_ternary_cache: dict[
        tuple[BVDD_Node, BVDD_Node, BVDD_Node], list[tuple[int, int, int, int]]
    ] = {}
    intersect_ternary_hits: int = 0

    @override
    def intersect_ternary(
        self,
        bvdd2: SBDD_o2s,
        bvdd3: SBDD_o2s,
        intersection: list[tuple[int, int, int, int]] | None = None,
    ) -> list[tuple[int, int, int, int]]:
        s1 = self.get_s()
        s2 = bvdd2.get_s()
        s3 = bvdd3.get_s()
        if (s1, s2, s3) in BVDD_cached.intersect_ternary_cache:
            BVDD_cached.intersect_ternary_hits += 1
        elif intersection:
            # lock is acquired
            BVDD_cached.intersect_ternary_cache[(s1, s2, s3)] = intersection
        else:
            # concurrent without acquiring lock
            intersection = super().intersect_ternary(bvdd2, bvdd3)
            with BVDD_cached.intersect_ternary_lock:
                return self.intersect_ternary(bvdd2, bvdd3, intersection)
        return BVDD_cached.intersect_ternary_cache[(s1, s2, s3)]

    constant_lock: threading.Lock = threading.Lock()
    constant_cache: dict[Any, BVDD_Node] = {}
    boolean_cache: dict[bool, BVDD_Node] = {}
    constant_hits: int = 0

    @override
    def constant_BVDD(
        self, output: Any, constant: BVDD_Node | None = None
    ) -> BVDD_Node:
        cache = (
            BVDD_cached.boolean_cache
            if isinstance(output, bool)
            else BVDD_cached.constant_cache
        )
        if output in cache:
            BVDD_cached.constant_hits += 1
        elif constant:
            # lock is acquired
            cache[output] = constant
        else:
            # concurrent without acquiring lock
            constant = super().constant_BVDD(output)
            with BVDD_cached.constant_lock:
                return self.constant_BVDD(output, constant)
        return cache[output]

    projection_lock: threading.Lock = threading.Lock()
    projection_cache: dict[tuple[int, int, int | None], BVDD_Node] = {}
    projection_hits: int = 0

    @override
    def projection_BVDD(
        self,
        index: int = 0,
        offset: int = 0,
        input_value: Any | None = None,
        projection: BVDD_Node | None = None,
    ) -> BVDD_Node:
        if (index, offset, input_value) in BVDD_cached.projection_cache:
            BVDD_cached.projection_hits += 1
        elif projection:
            # lock is acquired
            BVDD_cached.projection_cache[(index, offset, input_value)] = projection
        else:
            # concurrent without acquiring lock
            projection = super().projection_BVDD(index, offset, input_value)
            with BVDD_cached.projection_lock:
                return self.projection_BVDD(index, offset, input_value, projection)
        return BVDD_cached.projection_cache[(index, offset, input_value)]

    compute_unary_lock: threading.Lock = threading.Lock()
    compute_unary_cache: dict[tuple[str | None, int | None, BVDD_Node], BVDD_Node] = {}
    compute_unary_hits: int = 0

    @override
    def compute_unary(
        self,
        op: Any,
        op_id: str | None = None,
        bits: int | None = None,
        unary: BVDD_Node | None = None,
    ) -> BVDD_Node:
        if op_id is None:
            return super().compute_unary(op, op_id, bits)
        elif (op_id, bits, self) in BVDD_cached.compute_unary_cache:
            # assert (super().compute_unary(op, op_id, bits) ==
            #     BVDD_cached.compute_unary_cache[(op_id, bits, self)])
            BVDD_cached.compute_unary_hits += 1
        elif unary:
            # lock is acquired
            BVDD_cached.compute_unary_cache[(op_id, bits, self)] = unary
        else:
            # concurrent without acquiring lock
            unary = super().compute_unary(op, op_id, bits)
            with BVDD_cached.compute_unary_lock:
                return self.compute_unary(op, op_id, bits, unary)
        return BVDD_cached.compute_unary_cache[(op_id, bits, self)]

    compute_binary_lock: threading.Lock = threading.Lock()
    compute_binary_cache: dict[
        tuple[str | None, int | None, BVDD_Node, BVDD_Node], BVDD_Node
    ] = {}
    compute_binary_hits: int = 0

    @override
    def compute_binary(
        self,
        op: Any,
        bvdd2: Any,
        op_id: str | None = None,
        bits: int | None = None,
        binary: BVDD_Node | None = None,
    ) -> BVDD_Node:
        if op_id is None:
            return super().compute_binary(op, bvdd2, op_id, bits)
        elif (op_id, bits, self, bvdd2) in BVDD_cached.compute_binary_cache:
            # assert (super().compute_binary(op, bvdd2, op_id, bits) ==
            #     BVDD_cached.compute_binary_cache[(op_id, bits, self, bvdd2)])
            BVDD_cached.compute_binary_hits += 1
        elif binary:
            # lock is acquired
            BVDD_cached.compute_binary_cache[(op_id, bits, self, bvdd2)] = binary
        else:
            # concurrent without acquiring lock
            binary = super().compute_binary(op, bvdd2, op_id, bits)
            with BVDD_cached.compute_binary_lock:
                return self.compute_binary(op, bvdd2, op_id, bits, binary)
        return BVDD_cached.compute_binary_cache[(op_id, bits, self, bvdd2)]

    compute_ternary_lock: threading.Lock = threading.Lock()
    compute_ternary_cache: dict[
        tuple[str | None, int | None, BVDD_Node, BVDD_Node, BVDD_Node], BVDD_Node
    ] = {}
    compute_ternary_hits: int = 0

    @override
    def compute_ternary(
        self,
        op: Any,
        bvdd2: Any,
        bvdd3: Any,
        op_id: str | None = None,
        bits: int | None = None,
        ternary: BVDD_Node | None = None,
    ) -> BVDD_Node:
        if op_id is None:
            return super().compute_ternary(op, bvdd2, bvdd3, op_id, bits)
        elif (op_id, bits, self, bvdd2, bvdd3) in BVDD_cached.compute_ternary_cache:
            # assert (super().compute_ternary(op, bvdd2, bvdd3, op_id, bits) ==
            #     BVDD_cached.compute_ternary_cache[(op_id, bits, self, bvdd2, bvdd3)])
            BVDD_cached.compute_ternary_hits += 1
        elif ternary:
            # lock is acquired
            BVDD_cached.compute_ternary_cache[(op_id, bits, self, bvdd2, bvdd3)] = (
                ternary
            )
        else:
            # concurrent without acquiring lock
            ternary = super().compute_ternary(op, bvdd2, bvdd3, op_id, bits)
            with BVDD_cached.compute_ternary_lock:
                return self.compute_ternary(op, bvdd2, bvdd3, op_id, bits, ternary)
        return BVDD_cached.compute_ternary_cache[(op_id, bits, self, bvdd2, bvdd3)]

    @staticmethod
    def print_profile():
        print("BVDD cache profile:")
        print(
            f"nodes:                {utilization(BVDD_Node.node_cache_hits, len(BVDD_Node.node_cache))}"
        )
        print(
            f"binary intersection:  {utilization(BVDD_cached.intersect_binary_hits, len(BVDD_cached.intersect_binary_cache))}"
        )
        print(
            f"ternary intersection: {utilization(BVDD_cached.intersect_ternary_hits, len(BVDD_cached.intersect_ternary_cache))}"
        )
        print(
            f"constants:            {utilization(BVDD_cached.constant_hits, len(BVDD_cached.constant_cache) + len(BVDD_cached.boolean_cache))}"
        )
        print(
            f"projection:           {utilization(BVDD_cached.projection_hits, len(BVDD_cached.projection_cache))}"
        )
        print(
            f"unary operators:      {utilization(BVDD_cached.compute_unary_hits, len(BVDD_cached.compute_unary_cache))}"
        )
        print(
            f"binary operators:     {utilization(BVDD_cached.compute_binary_hits, len(BVDD_cached.compute_binary_cache))}"
        )
        print(
            f"ternary operators:    {utilization(BVDD_cached.compute_ternary_hits, len(BVDD_cached.compute_ternary_cache))}"
        )


class BVDD(BVDD_cached):
    pass
