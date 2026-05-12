# Current State

**Phase**: ACT (S3 closes the `k = 1` sanity check; `ramsey_existence` remains)
**Since**: 2026-05-12 (S3 ACT-B, researcher-11)
**Iteration**: 3
**Researcher**: researcher-11 (S3); researcher-9 (S2); researcher-8 (S1)

## Current Focus

Session 3 (S3 ACT-B, researcher-11, 2026-05-12): discharge the `k = 1`
pigeonhole sanity check `ramseyNumber 1 s t = s + t - 1`.

Output of this session (build pending; the local worktree shares the broken
`proofs/.lake` symlink per memory `feedback_researcher_lake_symlink_broken.md`):

* `proofs/Proofs/RamseyHypergraph.lean` — 147 → 304 lines, +157.
  New helper `isRamsey_one_iff (n s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) :
  IsRamsey n 1 s t ↔ s + t - 1 ≤ n` cleanly factors the result.
  - **Forward (⇐): `s + t - 1 ≤ n → IsRamsey n 1 s t`.** Pigeonhole. Let
    `F := univ.filter (χ {·} = false)`, `G := univ.filter (χ {·} = true)`.
    `Finset.filter_card_add_filter_neg_card_eq_card` gives
    `|F| + |G| = n`. Case `|F| ≥ s` extracts an `s`-clique via
    `Finset.exists_subset_card_eq`; otherwise `|G| ≥ t` extracts a
    `t`-clique.
  - **Reverse (⇒): `IsRamsey n 1 s t → s + t - 1 ≤ n`.** Contrapositive
    on `n ≤ s + t - 2`. Build the worst-case coloring with
    `a := min (s-1) n` `false`-singletons and the rest `true`. Two card
    bounds via the globally-injective `Fin.val : Fin n → ℕ`:
      - false-clique image ⊆ `Finset.range a` so `|S| ≤ a ≤ s - 1`.
      - true-clique image ⊆ `Finset.Ico a n` (card `n - a` via
        `Nat.card_Ico`) and case-split on `min` gives `n - a ≤ t - 1`.
* `ramseyNumber_one`: closed by `isRamsey_one_iff` plus
  `Nat.sInf` on the upward-closed set `{n | s + t - 1 ≤ n}`.
* `leanFile` counts (this file): lineCount 147 → 304, theoremCount 6 → 7,
  defCount 4 (unchanged), sorryCount 2 → 1, axiomCount 0 (unchanged).

## Prior Session Outputs (S2, researcher-9)

* `proofs/Proofs/RamseyHypergraph.lean` (147 lines): API surface
  (`kColoring`, `IsMonochromatic`, `IsRamsey`, `ramseyNumber`) +
  `isMonochromatic_of_card_lt`, `isMonochromatic_empty_zero`,
  `is_ramsey_zero_false`, `is_ramsey_zero_true`; `ramsey_existence` and
  `ramseyNumber_one` stated as sorries. PR #17909 merged.

## Prior Session Outputs (S1, researcher-8)

* `problem.md` — formal restatement of OQ-03 as three sub-goals.
* `knowledge.md` — literature survey + Mathlib API audit.

## Active Approach

Three-step Lean formalization plan (S2 → S4):

1. **S2 (ACT-A).** Define `RamseyK.IsRamsey n k s t` and
   `RamseyK.ramseyNumber k s t`. Prove the `k = 1` sanity check
   `ramseyNumber 1 s t = s + t - 1` via pigeonhole (~30 lines of Lean,
   no new Mathlib dependencies). State `ramsey_existence` as a sorry.
2. **S3 (ACT-B).** Discharge `ramsey_existence` via the two-layer
   neighborhood induction. Base case `k = 2` reuses
   `SimpleGraph.ramseyNumber`'s existence proof (or re-proves it inline
   using pigeonhole). Inductive step uses the "fix a vertex, induct on
   `(k-1)`-coloring of neighborhood" construction.
3. **S4 (ACT-C).** State `erdos_rado_upper` as `ramseyNumber k s s ≤
   tower (k-1) (c_k * s)`. Likely needs an explicit `c_k` (e.g.
   `c_k = 4 * (k-1)!`); the tower function can be defined via
   `Nat.iterate (2 ^ ·) (k-1) (c_k * s)` so no new tower API.
   Proof: follow the Erdős–Rado recursive bound
   `R_k(s,t) ≤ R_{k-1}(R_k(s-1,t), R_k(s,t-1)) + 1`, unwound.

S5+ would tackle the stepping-up lower bound (OQ-03c), but only after S4
lands. The lower bound is harder and may need its own sub-OQ.

## Blockers

None for S2 (definitions are straightforward Mathlib boilerplate).

For S3/S4: `Hypergraph` is not yet in Mathlib, so we work directly with
`Finset (Fin n)` filtered by `card = k` (`Finset.powersetCard`). This is
adequate but verbose.

## Next Action

**S4 ACT-C — Existence theorem `ramsey_existence` (OQ-03a).**

The standard Ramsey 1930 two-layer induction. Induct on `s + t` for fixed
`k`; the inductive step is the "neighborhood-tree" argument: fix any
vertex `v`, the `(k-1)`-restrictions of `k`-subsets through `v` give a
`(k-1)`-coloring on `[n] \ {v}`, then apply induction at uniformity `k-1`.

* Base case `k = 2`: reuse `SimpleGraph.ramseyNumber`-style proof (or
  re-prove inline using the `k = 1` pigeonhole now available as
  `ramseyNumber_one`).
* Inductive step `k ≥ 3`: the harder half; ~150–300 lines depending on
  how much Mathlib API is built up. Concretely, prove the recursive
  bound `IsRamsey (R_{k-1}(R_k(s-1,t), R_k(s,t-1)) + 1) k s t` and
  derive `∃ n, IsRamsey n k s t` from there.

S5 will state the Erdős–Rado tower upper bound `erdos_rado_upper`.

## Attempt Counts

- Total attempts: 3
- Current approach attempts: 3
- Approaches tried: 3 (literature survey + Lean API design; S2 scaffold;
  S3 `ramseyNumber_one` via pigeonhole iff helper)

## Outcome of S1

ORIENT complete. Three sub-goals (existence, Erdős–Rado upper, Erdős–Hajnal
lower) cleanly stated; Mathlib gaps identified; S2 ACT-A is unblocked.

## Outcome of S2

S2 SCAFFOLD landed (build pending). `RamseyHypergraph.lean` adds 4
definitions and 4 sorry-free supporting lemmas alongside 2 sorries
(`ramsey_existence`, `ramseyNumber_one`). The `IsMonochromatic`-of-too-small
helper and the `s=0` / `t=0` degenerate Ramsey base cases form the
foundation for S3's pigeonhole and inductive arguments. PR #17909 merged.

## Outcome of S3

S3 closed `ramseyNumber_one s t = s + t - 1` (the `k = 1` pigeonhole
sanity check), reducing the file's `sorryCount` 2 → 1. The proof
introduces a new helper `isRamsey_one_iff : IsRamsey n 1 s t ↔
s + t - 1 ≤ n` that factors the result cleanly. Forward direction uses
`Finset.filter_card_add_filter_neg_card_eq_card` plus
`Finset.exists_subset_card_eq` for the pigeonhole; reverse (contrapositive)
constructs the bad coloring with `min (s-1) n` `false`-singletons and
bounds the clique cards via `Finset.range`/`Finset.Ico` images of the
globally-injective `Fin.val`. `ramseyNumber 1 s t = s + t - 1` then
follows from the iff via `Nat.sInf` on the upward-closed set. Build
pending (worktree shares the broken `proofs/.lake` symlink).
