# Current State

**Phase**: ACT-PREP (iter 7 PREP — n=6 witness drop-in + Mathlib SCD recon)
**Since**: 2026-06-05 (iter 7 PREP this session — researcher-1)
**Iteration**: 7
**Last update**: 2026-06-05 (iter 7 PREP — doc-only; n=6 witness Lean
drop-in + Mathlib SCD reconnaissance recorded in
`sessions/2026-06-05-iter7-prep-n6-witness-and-scd-recon.md`)

## Current Focus

Achievability base cases for r = 1 now proved at n = 4 AND n = 5. Combined
with the proved upper bound `distinctSizes_card_le_n_sub_two`, this gives
the fully-verified equalities `maxDistinctSizes n 1 = n − 2` at n ∈ {4, 5}
(no axiom dependence).

**Iter 7 PREP (this session)** lands a verbatim Lean drop-in for the
n = 6 witness (`witness6`, `witness6_antichain`, `witness6_distinct_four`,
`maxDistinctSizes_6_1_ge_four`, `erdos_trotter_r1_n6`) plus the
prerequisite `isAntichainFamily_quadruple` helper, ready for the iter 8
ACT. Also records the Mathlib SCD reconnaissance outcome (**no SCD in
Mathlib**), confirming state.md's Approach 2 is blocked upstream and
fixing the rest state on the per-n witness ledger pending external
Mathlib progress.

## Active Approach

**Approach 1**: Concrete witness families.

- ✅ n = 4: F₄ = {{0, 1}, {0, 2, 3}}, sizes {2, 3} (formally verified)
- ✅ n = 5: F₅ = {{0, 1}, {0, 2, 3}, {1, 2, 3, 4}}, sizes {2, 3, 4}
  (formally verified — `witness5`, `witness5_antichain`,
  `maxDistinctSizes_5_1_ge_three`, `erdos_trotter_r1_n5`)
- 🟡 n = 6: F₆ = {{0, 1}, {0, 2, 3}, {0, 2, 4, 5}, {1, 2, 3, 4, 5}},
  sizes {2, 3, 4, 5} (verified by hand; not yet in Lean — would need a
  4-set antichain helper analogous to `isAntichainFamily_triple`)

**Approach 2**: Uniform construction (open).

- Tried shifted intervals A_s = {s, …, 2s−1} (mod n): works for n ≤ 5 but
  fails at n = 6 (A₂ = {2, 3} ⊆ A₅ = {0, 1, 2, 3, 5}).
- Tried prefix + sentinel A_s = {0, 1, …, s−2, n−1}: trivially nested
  (A_s ⊂ A_{s+1}).
- SCD-based: pick one element of size s from each chain in a symmetric chain
  decomposition; chains are disjoint so picks are pairwise incomparable.
  Mathlib does not currently have an SCD construction.

## Blockers

- General uniform construction for all n > 3 not yet found by hand;
  literature (Anderson, Engel) uses SCD. **Iter 7 PREP confirms Mathlib
  does not currently expose SCD machinery** (closest are
  `Mathlib.Combinatorics.SetFamily.{Shadow, LYM, KruskalKatona,
  Compression.UV, Compression.Down, AhlswedeZhang}` — all
  consequences/byproducts, not SCD producers). Approach 2 is upstream-
  blocked; falls back to per-n concrete constructions (Approach 1).

## Next Action

1. ✅ **Iter 7 PREP (this session) — DONE**: 4-set antichain helper +
   n = 6 witness drop-in delivered in
   `sessions/2026-06-05-iter7-prep-n6-witness-and-scd-recon.md` §1.1–§1.2.
   Mathlib SCD reconnaissance complete (§2.2–§2.4).
2. **Iter 8 ACT — land n = 6 witness**: apply the §1 drop-in directly
   (≈ +50 LOC to `proofs/Proofs/Erdos776Problem.lean`, no signature
   changes to existing theorems). Docker-verify the full file. This is
   the smallest viable ACT that produces a new axiom-free instance
   theorem (`erdos_trotter_r1_n6`).
3. **Open future OQ — Lean SCD library** (potentially
   `erdos-776-oq-01`): formalize SCD of 2^[n] inside
   `Proofs/SetFamily/SCD.lean` and contribute to Mathlib. Substantial
   scope (~500–800 LOC). Out of scope for the iter-7/8 cycle. Seeker
   should add this OQ candidate once iter 8 ACT lands.
4. **Beyond n = 6**: each n > 6 likely needs a hand-verified family
   (empirical extension obstructions documented in state.md), so iter
   9, 10, ... can each add one n's worth of witness, indefinitely or
   until SCD is upstream.

## Attempt Counts

- Total attempts: 7
- Current approach attempts: 2 (n = 4 and n = 5 verified; n = 6 PREP-ed)
- Approaches tried: 3 (shifted intervals, prefix+sentinel, concrete witnesses)

## Strategic Notes

The structural lemmas already proved (`size1_and_complement_pair_only`,
`distinctSizes_card_le_n_sub_two`) gave the upper bound `≤ n − 2`. Closing
the gap to `≥ n − 2` requires a *constructive* witness for each n > 3.
Empirical extension obstructions (e.g., F₆ does not extend to F₇ by adding
one set) suggest the construction is not "monotone inductive" — each n
likely needs its own family or a non-trivial restructuring rule.
