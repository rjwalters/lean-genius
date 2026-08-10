#!/usr/bin/env python3
"""Exhaustively validate the deterministic modulo-three CNF primitive."""

from itertools import product


def clauses_for(inputs):
    next_var = len(inputs) + 1
    clauses = []

    def state():
        nonlocal next_var
        result = tuple(range(next_var, next_var + 3))
        next_var += 3
        clauses.append(result)
        clauses.extend((-result[i], -result[j])
                       for i in range(3) for j in range(i + 1, 3))
        return result

    previous = state()
    clauses.extend([(previous[0],), (-previous[1],), (-previous[2],)])
    for literal in range(1, len(inputs) + 1):
        current = state()
        for residue in range(3):
            clauses.append((-previous[residue], literal, current[residue]))
            clauses.append((-previous[residue], -literal,
                            current[(residue + 1) % 3]))
        previous = current
    clauses.append((previous[1],))
    return clauses, next_var


def satisfied(clause, values):
    return any(values[abs(literal)] == (literal >= 0) for literal in clause)


def main():
    # Input variables are indexed 1..n in this small independent model;
    # state variables follow.  Exhaust all auxiliary assignments and require
    # a unique extension exactly for inputs of cardinality 1 mod 3.
    for n in range(1, 5):
        for inputs in product((False, True), repeat=n):
            clauses, variable_count = clauses_for(inputs)
            extensions = 0
            for auxiliary in product((False, True),
                                     repeat=variable_count - n - 1):
                values = dict(enumerate((False,) + inputs + auxiliary))
                if all(satisfied(clause, values) for clause in clauses):
                    extensions += 1
            assert extensions == (1 if sum(inputs) % 3 == 1 else 0), \
                (n, inputs, extensions)
    print("MOD3 EQ ONE TESTS OK")


if __name__ == "__main__":
    main()
