#!/usr/bin/env python3
"""Exhaustively validate the forward sequential at-most-k primitive."""

from itertools import product


def encoding(n, k):
    clauses = []
    next_var = n + 1
    previous = [None] * (k + 1)
    for index, literal in enumerate(range(1, n + 1), 1):
        current = [None] * (k + 1)
        for threshold in range(1, min(index, k) + 1):
            current[threshold] = next_var
            next_var += 1
            if threshold == 1:
                clauses.append((-literal, current[1]))
            if previous[threshold] is not None:
                clauses.append((-previous[threshold], current[threshold]))
            if threshold >= 2 and previous[threshold - 1] is not None:
                clauses.append((-literal, -previous[threshold - 1],
                                current[threshold]))
        if previous[k] is not None:
            clauses.append((-literal, -previous[k]))
        previous = current
    return clauses, next_var


def satisfied(clause, values):
    return any(values[abs(literal)] == (literal > 0) for literal in clause)


def main():
    for n in range(1, 7):
        for k in range(1, min(n, 3) + 1):
            clauses, next_var = encoding(n, k)
            for inputs in product((False, True), repeat=n):
                extensions = 0
                for auxiliary in product((False, True),
                                         repeat=next_var - n - 1):
                    values = dict(enumerate((False,) + inputs + auxiliary))
                    if all(satisfied(clause, values) for clause in clauses):
                        extensions += 1
                assert (extensions > 0) == (sum(inputs) <= k), \
                    (n, k, inputs, extensions)
    print("CARD AT MOST TESTS OK")


if __name__ == "__main__":
    main()
