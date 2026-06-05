# Current State

**Phase**: ACT (axiom-side work continues; structural lemmas extended)
**Path**: full
**Since**: 2026-04-27 (BLOCKED), 2026-05-08 (UNBLOCKED — Iter 7),
           2026-06-05 (Iter 8 — this PR)
**Last Updated**: 2026-06-05 (Iteration 8, researcher-1)
**Iteration**: 8

## Current Focus

**Iter 8 (this PR)**: Added the two structural lemmas predicted by
Iter 7's state.md as the next actions:

1. `dichrom_le_of_colorable (G : SimpleGraph V) {k : ℕ}
    (h : G.Colorable k) : G.dichromNumber ≤ k` — generalizes
    `bipartite_dichrom_le_two`. Direct application of
    `isAcyclicColoring_of_no_mono_edge` to any proper k-coloring,
    which has no monochromatic edges.
2. `cochrom_le_of_colorable (G : SimpleGraph V) {k : ℕ}
    (h : G.Colorable k) : G.cochromNumber ≤ k` — mirror lemma for
    the cochromatic side. Each color class of a proper k-coloring
    is an independent set, satisfying the `¬G.Adj` branch of
    `IsCochromatic`.

`bipartite_dichrom_le_two` was then refactored from a 7-line `by`
proof into a 1-line corollary of `dichrom_le_of_colorable`. No new
axioms, no sorries.

**2 axioms remain** in `proofs/Proofs/Erdos761Problem.lean` (283 lines,
8 theorems, 6 defs, 1 private lemma, 0 sorries on this PR):

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
  `Orientation` structure collides with
  `Mathlib.LinearAlgebra.Orientation` after Mathlib's transitive
  import surface expanded. Documented blocker.
- **Iter 7** (2026-05-08, researcher-11): drift partially unblocked
  via `namespace Erdos761` wrapper, BUT the file was never built
  (state.md said "Build pending"); the wrapper itself introduced a
  fresh dot-notation breakage on every `G.dichromNumber` /
  `G.cochromNumber` call.
- **Iter 8** (2026-06-05, researcher-1, this PR): (a) added
  `dichrom_le_of_colorable` + `cochrom_le_of_colorable` (the
  structural ℕ-valued χ-bounds); (b) simplified
  `bipartite_dichrom_le_two` to a corollary; (c) repaired the Iter-7
  wrapper by switching the two `SimpleGraph.X` defs to `_root_.`
  form; (d) repaired Mathlib 4.26 `Equiv.injective` drift at lines
  145 & 232 (`mt e.injective` → direct λ). lineCount 262 → 291.
  theoremCount 7 → 8. First successful Docker build since 2026-04-27.

## Active Approach (next sessions)

Both Iter 7 predictions (S6 research drafts) are now realized. Future
sessions should turn to:

- **Iter 9 candidate** — `dichrom_le_chromaticNumber` lifting the new
  `dichrom_le_of_colorable` bound to `G.chromaticNumber : ℕ∞`. This
  needs a `WithTop`-aware csInf manipulation. Roughly ~10 lines.
- Mirror `cochrom_le_chromaticNumber` similarly. ~10 lines.
- Optionally, a lemma `cochrom_le_dichrom_aux` or any sharp boundary
  result that connects `dichromNumber` to `cochromNumber` directly
  (currently we only have both ≤ |V|, both ≤ k for k-colorable, plus
  `dichrom_mono`). Anything that compares δ and ζ structurally would
  be new theory.

All three are independent of the two open axioms.

## Blockers

None.

## Next Action

**Iter 9**: lift `dichrom_le_of_colorable` to `G.chromaticNumber`
(Mathlib's `ℕ∞`-valued chromatic number). Look for an existing
Mathlib bridge `Colorable n ↔ chromaticNumber ≤ n` to keep the new
lemma short.

## Attempt Counts

- Total attempts: 8
- Current approach attempts: 1 (Iter 8 structural lemmas, this PR)
- Approaches tried: drift discovery (Iter 6); namespace wrapper
  unblock (Iter 7); structural χ-bounds (Iter 8).

## References

- `proofs/Proofs/Erdos761Problem.lean` — main file (283 lines, 8
  theorems, 6 defs, 1 private lemma, 2 axioms, 0 sorries).
- `src/data/proofs/erdos-761/meta.json` — gallery integration.
- Neumann-Lara 1982: "The dichromatic number of a digraph",
  *J. Combin. Theory Ser. B* 33.
- Erdős–Gimbel: cochromatic conjecture (open).
