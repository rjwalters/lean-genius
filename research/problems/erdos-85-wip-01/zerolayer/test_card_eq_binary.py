#!/usr/bin/env python3
"""Exhaustively test the equivalence binary exact-cardinality counter."""

from itertools import product


def build(n, k):
    nv = n
    clauses = []

    def newvar():
        nonlocal nv
        nv += 1
        return nv

    width = (n + 1).bit_length()
    previous = [None] * width
    for literal in range(1, n + 1):
        carry = literal
        current = []
        for bit in range(width):
            old = previous[bit]
            if old is None:
                current.append(carry)
                carry = None
            elif carry is None:
                current.append(old)
            else:
                result = newvar()
                clauses.extend([
                    (-old, -carry, -result), (-old, carry, result),
                    (old, -carry, result), (old, carry, -result),
                ])
                next_carry = newvar()
                clauses.extend([
                    (-next_carry, old), (-next_carry, carry),
                    (next_carry, -old, -carry),
                ])
                current.append(result)
                carry = next_carry
        previous = current
    for bit, literal in enumerate(previous):
        if literal is None:
            assert not ((k >> bit) & 1)
        else:
            clauses.append((literal,) if (k >> bit) & 1 else (-literal,))
    return clauses, nv


def satisfied(clauses, assignment):
    return all(any((literal > 0) == assignment[abs(literal)]
                   for literal in clause) for clause in clauses)


for n in range(1, 5):
    for k in range(n + 1):
        clauses, variables = build(n, k)
        auxiliary = range(n + 1, variables + 1)
        for inputs in product((False, True), repeat=n):
            extendable = False
            for aux in product((False, True), repeat=variables - n):
                assignment = {i + 1: value for i, value in enumerate(inputs)}
                assignment.update(dict(zip(auxiliary, aux)))
                if satisfied(clauses, assignment):
                    extendable = True
                    break
            assert extendable == (sum(inputs) == k), (n, k, inputs)

print("BINARY EXACT CARDINALITY ALL OK")
