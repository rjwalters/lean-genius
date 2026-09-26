#!/usr/bin/env python3
"""Choose cube-and-conquer split variables by unit-propagation lookahead (board goal #47).

For each candidate variable v, propagate v=1 and v=0 separately from the empty assignment and
record how many literals each branch forces (a conflict counts as "infinite"). A good split
variable forces many literals in BOTH branches; the occurrence-count heuristic failed on this
family because its top variables are 98% negative (one branch trivial, the other the whole
problem). Selection is greedy: the next variable maximizes min(forced(v=1), forced(v=0)) on
the formula as is, skipping variables already forced by any chosen literal. Output is a JSON
list consumed by cube_verdict.py --split-vars. Heuristic only; it cannot affect soundness.
SINGLE-SEAT (claude, 2026-09-26).
"""
from __future__ import annotations

import argparse
import collections
import json
from pathlib import Path
import sys
import time


def parse(path: Path):
    clauses = []
    for line in path.read_bytes().split(b"\n"):
        if not line or line[:1] in (b"c", b"p"):
            continue
        lits = [int(t) for t in line.split()]
        if lits[-1] != 0:
            raise ValueError("clause line without terminator")
        clauses.append(lits[:-1])
    return clauses


class Propagator:
    """Minimal unit propagation with per-clause unassigned counters (reset between probes)."""

    def __init__(self, clauses):
        self.clauses = clauses
        self.occ = collections.defaultdict(list)  # literal -> clause indices containing it
        for index, clause in enumerate(clauses):
            for lit in clause:
                self.occ[lit].append(index)
        self.nvars = max(abs(l) for c in clauses for l in c)

    def probe(self, assumptions):
        value = {}
        unassigned = [len(c) for c in self.clauses]
        satisfied = bytearray(len(self.clauses))
        queue = list(assumptions)
        forced = 0
        while queue:
            lit = queue.pop()
            var = abs(lit)
            if var in value:
                if value[var] != (lit > 0):
                    return float("inf"), value  # conflict
                continue
            value[var] = lit > 0
            forced += 1
            for index in self.occ.get(lit, ()):
                satisfied[index] = 1
            for index in self.occ.get(-lit, ()):
                if satisfied[index]:
                    continue
                unassigned[index] -= 1
                if unassigned[index] == 0:
                    return float("inf"), value
                if unassigned[index] == 1:
                    for other in self.clauses[index]:
                        if abs(other) not in value:
                            queue.append(other)
                            break
        return forced, value


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("cnf", type=Path)
    parser.add_argument("-k", type=int, default=6)
    parser.add_argument("--candidates", type=int, default=150, help="probe the N variables with the most balanced occurrence")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    started = time.time()
    clauses = parse(args.cnf)
    occ_pos = collections.Counter()
    occ_neg = collections.Counter()
    for clause in clauses:
        for lit in clause:
            (occ_pos if lit > 0 else occ_neg)[abs(lit)] += 1
    variables = sorted(set(occ_pos) | set(occ_neg), key=lambda v: -min(occ_pos[v], occ_neg[v]))
    candidates = variables[:args.candidates]
    prop = Propagator(clauses)
    # Baseline: literals already forced by the formula's unit clauses.
    base_forced, base_value = prop.probe([c[0] for c in clauses if len(c) == 1])
    scores = {}
    for v in candidates:
        if v in base_value:
            continue
        up, _ = prop.probe([v])
        down, _ = prop.probe([-v])
        scores[v] = (min(up, down), up * down if up != float("inf") and down != float("inf") else float("inf"), up, down)
    ranked = sorted(scores.items(), key=lambda kv: (-kv[1][0], -kv[1][1] if kv[1][1] != float("inf") else 0, kv[0]))
    chosen = []
    forced_by_chosen = set(base_value)
    for v, score in ranked:
        if v in forced_by_chosen:
            continue
        # Skip a candidate that any single chosen literal already decides.
        decided = False
        for c in chosen:
            for lit in (c, -c):
                _, val = prop.probe([lit])
                if v in val:
                    decided = True
                    break
            if decided:
                break
        if decided:
            continue
        chosen.append(v)
        if len(chosen) == args.k:
            break
    report = {"cnf": str(args.cnf), "k": args.k, "split_variables": chosen, "method": "unit-propagation lookahead, greedy max-min forced literals",
              "candidates_probed": len(scores), "baseline_forced": base_forced,
              "scores": {str(v): {"min": s[0] if s[0] != float("inf") else "conflict", "forced_true": s[2] if s[2] != float("inf") else "conflict",
                                  "forced_false": s[3] if s[3] != float("inf") else "conflict"} for v, s in ranked[:40]},
              "chosen_scores": {str(v): {"forced_true": scores[v][2] if scores[v][2] != float("inf") else "conflict",
                                         "forced_false": scores[v][3] if scores[v][3] != float("inf") else "conflict",
                                         "occ_pos": occ_pos[v], "occ_neg": occ_neg[v]} for v in chosen},
              "seconds": round(time.time() - started, 1)}
    args.output.write_text(json.dumps(report, indent=1) + "\n")
    print(json.dumps({k: report[k] for k in ("k", "split_variables", "candidates_probed", "baseline_forced", "chosen_scores", "seconds")}))
    return 0


if __name__ == "__main__":
    sys.exit(main())
