# Current State

**Phase**: ACT (drift unblocked, axiom-side work resumes)
**Path**: full
**Since**: 2026-04-27 (BLOCKED), 2026-05-08 (UNBLOCKED — this PR)
**Last Updated**: 2026-05-08 (Iteration 7, researcher-11)
**Iteration**: 7

## Current Focus

**Drift unblocked**: the local `Orientation` collision with
`Mathlib.LinearAlgebra.Orientation` (which had become transitively in
scope as of Mathlib v4.26.0 and blocked iterations since 2026-04-27)
is resolved by wrapping all declarations in `namespace Erdos761`.
Two-line edit (`namespace Erdos761` after `open SimpleGraph`,
`end Erdos761` at file end). Inside the namespace, unqualified
`Orientation` resolves to `Erdos761.Orientation`; outside the file,
the local declaration is qualified as `Erdos761.Orientation` and
no longer collides with `Mathlib.LinearAlgebra.Orientation`.

**2 axioms remain** in `proofs/Proofs/Erdos761Problem.lean` (262 lines,
7 theorems, 6 defs, 0 sorries on origin/main post-this-PR):

1. `erdos_761_question1` (Erdős–Neumann-Lara) — must a graph with
   large chromatic number have large dichromatic number? OPEN.
2. `erdos_761_question2` (Erdős–Gimbel) — must a graph with large
   cochromatic number contain a subgraph with large dichromatic
   number? OPEN.

Both are genuinely open questions and remain as axioms.

## Iteration History

- **Iter 1–4** (2026-03–04, multiple PRs): bootstrap + axiom reductions
  + IsAcyclicColoring correction (PR #7309 etc.).
- **Iter 5** (2026-04-26, PR #12755 etc.): re-audit clean.
- **Iter 6** (2026-04-27, PR #13195): drift discovery — the local
  `Orientation` structure now collides with
  `Mathlib.LinearAlgebra.Orientation` after Mathlib's transitive
  import surface expanded. Documented blocker.
- **Iter 7** (2026-05-08, this PR, researcher-11): drift unblocked
  via `namespace Erdos761` wrapper. lineCount 258→262 (+4 for the
  `namespace`/`end` lines). theoremCount and axiomCount unchanged.
  Build pending.

## Active Approach (next sessions)

With the drift resolved, the deferred S6 research drafts can be
applied (per state.md prior recommendation):
- `dichrom_le_of_colorable`: generalize `bipartite_dichrom_le_two` to
  arbitrary k. Predicted ~15 lines.
- `cochrom_le_of_colorable`: similar generalization for
  cochromatic number. ~15 lines.

Both are independent of the open axioms `erdos_761_question1` and
`erdos_761_question2`.

## Blockers

None. The `Mathlib.LinearAlgebra.Orientation` drift is resolved as of
this PR (Iter 7).

## Next Action

**Iter 8**: prove `dichrom_le_of_colorable {k : ℕ} (h : G.Colorable k) :
G.dichromNumber ≤ k`. Generalizes `bipartite_dichrom_le_two`. Likely
~15 lines: any k-coloring of `G` extends to an acyclic coloring of any
orientation `O` (no monochromatic edge ⇒ no monochromatic cycle).

After Iter 8, **Iter 9** mirror lemma `cochrom_le_of_colorable`.

## Attempt Counts

- Total attempts: 7
- Current approach attempts: 1 (drift unblock, this PR)
- Approaches tried: drift discovery (Iter 6); namespace wrapper
  unblock (Iter 7).

## References

- `proofs/Proofs/Erdos761Problem.lean` — main file (262 lines, 7
  theorems, 6 defs, 2 axioms, 0 sorries).
- `src/data/proofs/erdos-761/meta.json` — gallery integration.
- Neumann-Lara 1982: "The dichromatic number of a digraph",
  *J. Combin. Theory Ser. B* 33.
- Erdős–Gimbel: cochromatic conjecture (open).
