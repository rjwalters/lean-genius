# H3 triple-cell completion engine

The conditional engine, bridge and split theorem compile with only
`propext`, `Classical.choice` and `Quot.sound`. This does not yet exclude the
triple cell: successful search results remain explicit premises.

Source commit: `8484794c2a96f41f6aee799c193a56c47bf8e292`.
Cloud build: `20261008T101350-erdos85__h3-triple-formal-20261007-402758`, exit 0.
Engine, Bridge and Split were freshly built in 9.7, 5.1 and 3.9 seconds.
`conditional-build/AUDIT.json` binds their exact sources, objects and four
axiom reports to the successful job. The read-only auditor checked the
objects twice, including modification times within the job interval.
Raw log/spec/exit and exact source snapshots are retained alongside it.

## Adaptation

The source is adapted from the completed pair engine at
`dc7f78d47d7017dcb8da5cc4aa200f1432a0f5df`. Namespace and module names are
separate. The support layout changes to the actual canonical representative
`threeHighRepresentativeMasks 1`: vertex 3 has mask 7; singleton supports
are 4–10, 11–17 and 18–24; empty supports are 25–48. Each colour fibre still
has eight vertices. All range guards and their supporting lemmas use the
new boundary 25. The rest of the search and soundness argument is unchanged.

The bridge proves the mask/colour equality directly with `decide +kernel`,
then derives an engine model and compatibility from the existing relation
constraints. `threeHighCanonicalGraphCover_one` transports representative
exclusion to `OrderFortyNineTripleCellExcluded 3 1`.

The unsplit interface is `tripleSearch = true`; the split interface requires
`0 < m` and every `triplePart m r = true` for `r < m`. Fuels are 70/30/40.
Fuel exhaustion and a completed candidate return false, so false alone is
not a satisfiability certificate. Neither hash injectivity nor balanced
parts is required by the composition theorem.

## Bounded diagnostic

`Probe384R0.lean` requests just `triplePart 384 0 = true` via `native_decide`.
It is outside the library's automatic module glob. `run_probe.py` stages it
under the Lean project root, checks the three prerequisite source/object
hashes, and limits its Lean process group to 300 seconds. Only the existing
cloud builder is used. Results are pending; no full campaign is authorized
or launched by this experiment, and the prior census route is unchanged.
