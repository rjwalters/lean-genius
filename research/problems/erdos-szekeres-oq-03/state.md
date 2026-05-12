# Current State

**Phase**: ACT (S2 scaffold landed; existence + k=1 sanity check remain `sorry`)
**Since**: 2026-05-12 (S2 ACT-A scaffold, researcher-9)
**Iteration**: 2

## Current Focus

Session 2 (S2 ACT-A, researcher-9, 2026-05-12): create the
`RamseyHypergraph.lean` API surface and state the main existence theorem
(OQ-03a) as a `sorry`.

Output of this session:

* `proofs/Proofs/RamseyHypergraph.lean` (~147 lines, 2 sorries, 0 axioms).
  Definitions: `kColoring`, `IsMonochromatic`, `IsRamsey`, `ramseyNumber`
  (via `sInf`).
  Proved API lemmas: `isMonochromatic_of_card_lt` (subsets smaller than
  the uniformity have no `k`-subsets, hence are trivially monochromatic),
  `isMonochromatic_empty_zero`, `is_ramsey_zero_false`, `is_ramsey_zero_true`
  (degenerate `s=0` / `t=0` cases — the empty set is the witness).
  Two sorries:
  - `ramsey_existence` (the OQ-03a main theorem) — to be discharged in S3.
  - `ramseyNumber_one` (k=1 pigeonhole sanity check) — postponed to S3
    because the lower-bound construction (a coloring with `s-1`
    `false`-singletons and `t-1` `true`-singletons) takes more space than
    initially estimated.
* `proofs/Proofs.lean` regenerated to include the new file.

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

**S3 ACT-B.** Two parallel tasks (can be done in either order):

1. **Pigeonhole base case `ramseyNumber_one s t = s + t - 1`.**
   - Forward (`IsRamsey (s+t-1) 1 s t`): partition `Fin (s+t-1)` by
     `i ↦ χ {i}`; if `|filter (χ{·}=false)| ≥ s` use that as the s-clique,
     else (by pigeonhole) the complement gives a t-clique.
   - Backward (`¬ IsRamsey (s+t-2) 1 s t`): explicit coloring with the
     first `s-1` singletons `false` and the remaining `t-1` `true`.
   - Combine via `sInf_eq_iff` (or by showing both `sInf ≤ s+t-1` and
     `s+t-1 ≤ sInf`).
2. **Existence theorem `ramsey_existence` (OQ-03a).**
   The standard two-layer induction (Ramsey 1930). Induct on `s + t`
   for fixed `k`; the inductive step is the "neighborhood-tree" argument:
   fix any vertex `v`, the `(k-1)`-restrictions of `k`-subsets through
   `v` give a `(k-1)`-coloring on `[n] \ {v}`, then apply induction at
   uniformity `k-1`.
   - Base case `k = 2`: reuse `SimpleGraph.ramseyNumber` from Mathlib
     (or re-prove inline). 
   - Inductive step (k ≥ 3): the harder half; ~150-300 lines depending on
     how much Mathlib API is built up.

S4 will state the Erdős–Rado tower upper bound `erdos_rado_upper`.

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 2
- Approaches tried: 2 (literature survey + Lean API design; S2 scaffold)

## Outcome of S1

ORIENT complete. Three sub-goals (existence, Erdős–Rado upper, Erdős–Hajnal
lower) cleanly stated; Mathlib gaps identified; S2 ACT-A is unblocked.

## Outcome of S2

S2 SCAFFOLD landed (build pending). `RamseyHypergraph.lean` adds 4
definitions and 4 sorry-free supporting lemmas alongside 2 sorries
(`ramsey_existence`, `ramseyNumber_one`). The `IsMonochromatic`-of-too-small
helper and the `s=0` / `t=0` degenerate Ramsey base cases form the
foundation for S3's pigeonhole and inductive arguments.
