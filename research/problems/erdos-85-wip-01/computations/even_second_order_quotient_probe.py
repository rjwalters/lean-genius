#!/usr/bin/env python3
"""Probe the scalable even second-order quotient constraints.

For even degree d and N=d(d-1)+3, enumerate small-component solutions of

  Q 1 = d 1,
  Q^2 = (d-3) I + 1 r^T,
  r_i Q_ij = r_j Q_ji,

then apply the grouped target-length periodicity obstruction.  This is an
exploratory exact integer search, not a proof artifact.

The trace condition is optional.  In particular, ``trace(Q)=d`` must not be
imposed automatically when ``d-3`` is a square: the two rational roots
``±sqrt(d-3)`` can occur with unequal multiplicities.
"""

from functools import lru_cache
import argparse


def compositions(total, length, prefix=()):
    if length == 1:
        yield prefix + (total,)
        return
    for value in range(total + 1):
        yield from compositions(total - value, length - 1, prefix + (value,))


def partitions(total, length, lower=3, prefix=()):
    if length == 0:
        if total == 0:
            yield prefix
        return
    for value in range(lower, total // length + 1):
        yield from partitions(total - value, length - 1, value, prefix + (value,))


@lru_cache(None)
def rows(degree, length):
    return tuple(compositions(degree, length))


def row_domain(degree, lengths, i):
    ri = lengths[i]
    answer = []
    for row in rows(degree, len(lengths)):
        reverse = []
        for rj, qij in zip(lengths, row):
            if ri * qij % rj:
                break
            reverse.append(ri * qij // rj)
        else:
            if sum(a * b for a, b in zip(row, reverse)) == ri + degree - 3:
                answer.append(row)
    return answer


def periodic_ok(lengths, matrix):
    if any(lengths[i] * matrix[i][i] % 2 for i in range(len(lengths))):
        return False
    for i, ri in enumerate(lengths):
        for shift in range(2, ri - 1):
            if sum(matrix[i][j] for j, rj in enumerate(lengths)
                   if j != i and rj % ri == shift) > 1:
                return False
    return True


def quotients(degree, lengths, required_trace=None):
    size = len(lengths)
    domains = [row_domain(degree, lengths, i) for i in range(size)]
    if any(not domain for domain in domains):
        return
    order = sorted(range(size), key=lambda i: len(domains[i]))
    chosen = {}

    def search(position, trace):
        if position == size:
            if required_trace is not None and trace != required_trace:
                return
            matrix = tuple(chosen[i] for i in range(size))
            if all(sum(matrix[i][k] * matrix[k][j] for k in range(size))
                   == lengths[j]
                   for i in range(size) for j in range(size) if i != j):
                yield matrix
            return
        i = order[position]
        for row in domains[i]:
            next_trace = trace + row[i]
            if required_trace is not None and next_trace > required_trace:
                continue
            if any(lengths[i] * row[j] != lengths[j] * chosen[j][i]
                   for j in chosen):
                continue
            chosen[i] = row
            yield from search(position + 1, next_trace)
            del chosen[i]

    yield from search(0, 0)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("degree", type=int)
    parser.add_argument("--counts", type=int, nargs="+", default=[3, 5, 7])
    parser.add_argument(
        "--require-trace-degree",
        action="store_true",
        help=("impose trace(Q)=degree; justified only after a separate "
              "nonsquare/minimal-polynomial argument"),
    )
    args = parser.parse_args()
    total = args.degree * (args.degree - 1) + 3
    for count in args.counts:
        raw = surviving = 0
        examples = []
        for lengths in partitions(total, count):
            if sum(r % 2 == 0 for r in lengths) % 2:
                continue
            required_trace = args.degree if args.require_trace_degree else None
            for matrix in quotients(args.degree, lengths, required_trace):
                raw += 1
                if periodic_ok(lengths, matrix):
                    surviving += 1
                    if len(examples) < 3:
                        examples.append((lengths, matrix))
        print(args.degree, count, "raw", raw, "periodic", surviving)
        for example in examples:
            print(" ", example)


if __name__ == "__main__":
    main()
