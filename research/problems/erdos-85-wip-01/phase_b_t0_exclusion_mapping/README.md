# H5/T0 exclusion: exact frozen input scope

Both read-only checks identify exactly 43 frozen H5/T0 inputs. Each is the archived canonical T0 base with its recorded ordered two unit clauses, preserving duplicate units. SHA256, byte length, case ID and inventory source index all match. The base's 230 fixed support literals match the existing Lean T0 mask definition; its full clause count is 1,328,618 and prospective roots have 1,328,620 clauses.

check.py adapts the reviewed T1 mapping (2039), checks the variable-to-sign map independently of physical unit-clause order, and incrementally hashes the unchanged base with the new header and suffix. independent.py separately parses the Lean mask literal and reconstructs full prospective bytes for each root. Both produce the same 43-ID domain. An initial adapted mask-audit path was incorrect and failed before check.py produced a result; the final path points to q7_h5_t0_completion, and both checks now pass.

This links the T0 mathematical/finite-computation exclusion (review 2037, bank 3907641430308ebf9c42bebaa238a70a5baeaa29) to an explicit input scope. It does not establish CNF-to-graph soundness, create solver UNSAT receipts, prove a Lean theorem, or change the frozen inventory or dispatch configuration. Any operational treatment of these inputs needs its own reviewed evidence category.

Scripts use the existing shared worktree and archived base paths. Run both from this directory; only small JSON evidence is written. pins.json freezes source, output and explanation. Mapping review is pending.
