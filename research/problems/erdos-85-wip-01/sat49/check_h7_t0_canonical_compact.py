#!/usr/bin/env python3
"""Emit the canonical H7/T0 CNF with the repo's compact PySAT counter.

The graph variables, fixed support pattern, and global C4 clauses are exactly
those of ``check_h7_t0_canonical_completion.py``.  Only the auxiliary encoding
of each exact low-degree constraint changes: this uses the compact
Knuth/Healy sequential counter already implemented and proved satisfiable in
Lean by ``Erdos85SequentialCounterGenerator`` and
``Erdos85SequentialCounterReification``.  It is therefore both substantially
smaller and closer to the existing formal certificate infrastructure.
"""

from __future__ import annotations

import argparse
import hashlib
import subprocess
import tempfile
from pathlib import Path

import check_h7_t0_canonical_completion as canonical

EXPECTED_SHA256 = "8bc9b8f15b7f03194f39d208b2c0015e6039e0aac759ccfce0b6415724130eb0"


class CompactCnf(canonical.Cnf):
    def at_most_core(self, literals: list[int], bound: int) -> None:
        size = len(literals)
        assert 0 < bound and bound + 1 < size
        ids: dict[tuple[int, int], int] = {}

        def counter_id(row: int, column: int) -> int:
            key = (row, column)
            if key not in ids:
                ids[key] = self.variable()
            return ids[key]

        for column in range(size - bound):
            s0j = counter_id(0, column)
            self.add(-literals[column], s0j)
            for row in range(bound - 1):
                skj = counter_id(row, column)
                if column < size - bound - 1:
                    self.add(-skj, counter_id(row, column + 1))
                self.add(
                    -literals[column + row + 1],
                    -skj,
                    counter_id(row + 1, column),
                )
            stj = counter_id(bound - 1, column)
            if column < size - bound - 1:
                self.add(-stj, counter_id(bound - 1, column + 1))
            self.add(-literals[column + bound], -stj)

    def at_most(self, literals: list[int], bound: int) -> None:
        size = len(literals)
        assert 0 <= bound <= size
        if bound == 0:
            for literal in literals:
                self.add(-literal)
        elif bound + 1 == size:
            self.add(*(-literal for literal in literals))
        elif bound < size:
            self.at_most_core(literals, bound)

    def exactly(self, literals: list[int], target: int) -> None:
        # Matches `seqCounterEquals`: at-least (complemented at-most) first,
        # then at-most, with a fresh local counter-id map in each block.
        self.at_most([-literal for literal in literals], len(literals) - target)
        self.at_most(literals, target)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--solver", default="kissat")
    parser.add_argument("--time", type=int, default=1800)
    parser.add_argument("--keep-cnf", type=Path)
    parser.add_argument("--emit-only", action="store_true")
    args = parser.parse_args()

    cnf, edge_variables, c4_clauses = canonical.build_cnf(CompactCnf)
    assert len(edge_variables) == 861
    assert cnf.variable_count == 17633
    assert c4_clauses == 687260
    assert len(cnf.clauses) == 720804
    if args.keep_cnf:
        path = args.keep_cnf
        temporary = None
    else:
        temporary = tempfile.TemporaryDirectory(prefix="h7-canonical-compact-")
        path = Path(temporary.name) / "canonical-compact.cnf"
    cnf.write(path)
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    assert digest == EXPECTED_SHA256
    print(f"edge_variables={len(edge_variables)}")
    print(f"variables={cnf.variable_count}")
    print(f"clauses={len(cnf.clauses)}")
    print(f"degree_clauses={len(cnf.clauses) - c4_clauses}")
    print(f"c4_clauses={c4_clauses}")
    print(f"sha256={digest}")
    print(f"cnf={path}")
    if args.emit_only:
        if temporary is not None:
            temporary.cleanup()
        return
    completed = subprocess.run(
        [args.solver, "-q", f"--time={args.time}", str(path)],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    print(completed.stdout, end="")
    positive = canonical.parse_assignment(completed.stdout)
    if positive is not None:
        canonical.validate(edge_variables, positive)
        print("validated=SAT_GENUINE_H7_T0_GRAPH")
    elif "s UNSATISFIABLE" in completed.stdout:
        print("validated=UNSAT_CANONICAL_H7_T0_COMPACT_VERDICT_ONLY")
    else:
        print("validated=UNKNOWN")
    if temporary is not None:
        temporary.cleanup()


if __name__ == "__main__":
    main()
