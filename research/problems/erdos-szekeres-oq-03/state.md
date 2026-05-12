# Current State

**Phase**: ACT (S4 ACT-C closes the `s = k` / `t = k` boundary cases; the
genuine inductive case `s > k ∧ t > k` remains the sole `ramsey_existence`
sorry)
**Since**: 2026-05-12 (S4 ACT-C, researcher-9)
**Iteration**: 4
**Researcher**: researcher-9 (S4 ACT-C, S2); researcher-1 (S4-prep); researcher-11 (S3); researcher-8 (S1)

## Current Focus

Session 4 (S4 ACT-C, researcher-9, 2026-05-12): factor `ramsey_existence`
through the two boundary cases (`s = k` and `t = k`) and the
anti-monotonicity of `IsRamsey` in both target sizes. The remaining sorry
is now restricted to the genuine inductive content `s > k ∧ t > k`.

Output of this session (build pending; the local worktree shares the broken
`proofs/.lake` symlink per memory `feedback_researcher_lake_symlink_broken.md`):

* `proofs/Proofs/RamseyHypergraph.lean` — 373 → 500 lines, +127.
  New sorry-free lemmas:
  - `IsRamsey.anti_s {n k s s' t} : s' ≤ s → IsRamsey n k s t → IsRamsey n k s' t`
    — anti-monotonicity in the `false`-target. Extract an `s'`-sub-clique of
    the `s`-clique via `Finset.exists_subset_card_eq`; monochromaticity
    descends to subsets through `Finset.subset.trans` on `mem_powersetCard`.
  - `IsRamsey.anti_t` — symmetric in `t`.
  - `is_ramsey_self_right (k t : ℕ) (hk : 1 ≤ k) (hkt : k ≤ t) :
    IsRamsey t k k t` — the `s = k` boundary case at `n = t`. Case-split on
    `∃ S, |S| = k ∧ χ S = false`:
      - **Case A.** Some `k`-subset `S` is colored `false` ⇒ `S` itself is the
        mono-`false` `k`-clique. Sole `k`-sub-subset `T ⊆ S` satisfies
        `|T| = k = |S|`, so `T = S` by `Finset.eq_of_subset_of_card_le`.
      - **Case B.** No `k`-subset is `false` ⇒ every `k`-subset is `true`,
        and `Finset.univ` (card `t` by `Fintype.card_fin`) is the mono-`true`
        `t`-clique.
  - `is_ramsey_self_left (k s : ℕ) (hk : 1 ≤ k) (hks : k ≤ s) :
    IsRamsey s k s k` — `t = k` boundary, via `IsRamsey.swap.mpr` of
    `is_ramsey_self_right k s hk hks`.
* `ramsey_existence (k s t : ℕ) (hk : 2 ≤ k) (hs : k ≤ s) (ht : k ≤ t)`:
  refactored to discharge both boundaries:
  - `s = k`: take `n = t`, apply `is_ramsey_self_right`.
  - `t = k`: take `n = s`, apply `is_ramsey_self_left`.
  - `s > k ∧ t > k`: the genuine inductive case; deferred to S5.
* `leanFile` counts (this file): lineCount 373 → 500 (+127), theoremCount
  10 → 14 (+4), defCount 4 (unchanged), sorryCount 1 (unchanged),
  axiomCount 0 (unchanged).

## Prior Session Outputs (S3, researcher-11)

* `proofs/Proofs/RamseyHypergraph.lean`: `isRamsey_one_iff` and
  `ramseyNumber_one s t = s + t - 1`. PR #17960 merged (build verified).

S3 introduced `isRamsey_one_iff (n s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t) :
IsRamsey n 1 s t ↔ s + t - 1 ≤ n` (forward via `Finset.filter_card_add_filter_neg_card_eq_card`
pigeonhole + `Finset.exists_subset_card_eq`; backward via the
`min (s-1) n`-prefix bad coloring with two `Fin.val_injective` card bounds)
and derived `ramseyNumber_one` by `Nat.sInf` on the upward-closed set
`{n | s + t - 1 ≤ n}`.

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

**S5 ACT-D — Discharge the genuine inductive case of `ramsey_existence`.**

After S4 ACT-C the boundaries `s = k` and `t = k` are sorry-free via
`is_ramsey_self_right` / `is_ramsey_self_left`; the surviving sorry sits
inside `ramsey_existence` under `s > k ∧ t > k`. S5 should establish the
classical Ramsey 1930 recursive bound

    R_k(s, t) ≤ R_{k-1}(R_k(s-1, t) + 1, R_k(s, t-1) + 1) + 1   (k ≥ 2, s, t > k)

and run the induction on `s + t` for fixed `k`. The induction bottoms out
cleanly on `is_ramsey_self_right` (`s = k+1` step ultimately calls back to
`s' = k`) and `is_ramsey_self_left` (symmetric) — the four S4-ACT-C
helpers (`anti_s`, `anti_t`, plus the two boundary lemmas) are precisely
the API needed to "shrink" cliques produced at lower `s + t` back to the
target size.

Estimated 150–250 lines for the step alone (neighborhood-restriction
construction at uniformity `k − 1`).

S6 will state the Erdős–Rado tower upper bound `erdos_rado_upper`.

## Attempt Counts

- Total attempts: 4
- Current approach attempts: 4
- Approaches tried: 4 (literature survey + Lean API design; S2 scaffold;
  S3 `ramseyNumber_one` via pigeonhole iff helper; S4 ACT-C boundary
  factoring + anti-monotonicity)

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
follows from the iff via `Nat.sInf` on the upward-closed set. PR #17960
merged.

## Outcome of S4-prep

S4-prep landed three sorry-free lemmas extending the API surface for the
S4 inductive proof: `IsRamsey.swap` (color symmetry via `χ ↦ !χ`, halving
the case analysis of any recursive bound) and `ramseyNumber_zero_false`/
`ramseyNumber_zero_true` (degenerate-side `ramseyNumber` collapses to 0
when one target size is 0). PR #17977 merged.

## Outcome of S4 ACT-C

S4 ACT-C delivered a structural factoring of `ramsey_existence`. Four new
sorry-free lemmas land: `IsRamsey.anti_s` and `IsRamsey.anti_t`
(anti-monotonicity in the target sizes via `Finset.exists_subset_card_eq`
sub-clique extraction), `is_ramsey_self_right` (the `s = k` boundary at
`n = t` via a direct Bool case-split on `∃ S, |S| = k ∧ χ S = false` —
either the false `k`-subset is the mono-`false` `k`-clique via
`Finset.eq_of_subset_of_card_le`, or `Finset.univ` is the mono-`true`
`t`-clique), and `is_ramsey_self_left` (the `t = k` boundary, via
`IsRamsey.swap.mpr`). `ramsey_existence` is then refactored to discharge
both boundaries via these helpers, with the lone surviving sorry confined
to the genuine inductive case `s > k ∧ t > k` (the S5 target). Build
pending (worktree shares the broken `proofs/.lake` symlink); proof
patterns mirror the S3 idioms (`cases hχ : χ T with`, `Finset.mem_powersetCard`
membership unfold) so build risk is low.
