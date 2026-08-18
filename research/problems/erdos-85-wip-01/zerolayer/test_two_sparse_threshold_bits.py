#!/usr/bin/env python3
"""Exhaustively test the threshold encoder used by the two-sparse probe."""

import ast
from itertools import product
from pathlib import Path

import z3


path = Path(__file__).with_name("model4444_symbolic_two_sparse_signal.py")
tree = ast.parse(path.read_text(), filename=str(path))
function = next(node for node in tree.body
                if isinstance(node, ast.FunctionDef) and
                node.name == "threshold_bits")
module = ast.Module(body=[function], type_ignores=[])


for length in range(1, 8):
    for maximum in range(1, 6):
        namespace = {"clauses": [], "counter": length}

        def newvar():
            namespace["counter"] += 1
            return namespace["counter"]

        namespace["newvar"] = newvar
        exec(compile(module, str(path), "exec"), namespace)
        thresholds = namespace["threshold_bits"](
            list(range(1, length + 1)), maximum)
        variables = [z3.Bool(f"v_{index}")
                     for index in range(namespace["counter"] + 1)]
        formula = []
        for clause in namespace["clauses"]:
            formula.append(z3.Or(*[
                variables[abs(literal)] if literal > 0 else
                z3.Not(variables[abs(literal)])
                for literal in clause
            ]))

        for values in product([False, True], repeat=length):
            base = z3.Solver()
            base.add(*formula)
            base.add(*[variables[index] == values[index - 1]
                       for index in range(1, length + 1)])
            assert base.check() == z3.sat
            count = sum(values)
            for level in range(1, maximum + 1):
                bit = thresholds[level]
                if bit is None:
                    assert count < level
                    continue
                wrong = z3.Solver()
                wrong.add(*base.assertions())
                wrong.add(variables[bit] != (count >= level))
                assert wrong.check() == z3.unsat, \
                    (length, maximum, values, level)

print("TWO SPARSE THRESHOLD BITS ALL OK")
