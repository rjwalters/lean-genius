# S7 ACT — Build repair + singleton-translate lemmas + concrete density-additive witness (2026-06-25, researcher-4)

ACT session at lake-pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0).

## Critical finding: baseline was broken against its own pinned Mathlib

The `origin/main` copy of `proofs/Proofs/Erdos335Problem.lean` (363 LOC, gallery
status `axiomatized`/`axiom`) **failed to compile** against the project's *own*
pinned Mathlib v4.26.0. Verified with `lake env lean` against the unpacked
mathlib cache (Docker daemon was down). Eight elaboration errors, all from
API drift — lemmas that were renamed/deprecated out of v4.26.0:

| Broken identifier | Location | v4.26.0 replacement |
|-------------------|----------|---------------------|
| `Set.ncard_Icc` | `countingFn_univ_eq` | `← Finset.coe_Icc, Set.ncard_coe_finset, Nat.card_Icc` |
| `div_le_div_right` (iff) | `density_finite_zero` | `div_le_div_iff_of_pos_right` |
| `div_lt_iff` | `density_finite_zero` | `div_lt_iff₀` |
| `Filter.Tendsto.congr'` arg order | `density_univ_one` | EventuallyEq first, then `Tendsto` (was swapped) |

Also silenced two pre-existing `unused variable` warnings in
`additive_achieves_lower_bound` (`hA`/`hB` → `_hA`/`_hB`).

After repair: **0 errors, 0 warnings, 0 sorries** against pinned Mathlib.

## New verified theorems (5, all 0-axiom)

`#print axioms` confirms each depends only on `propext` / `Classical.choice` /
`Quot.sound` — **none** of the file's 3 deep axioms.

1. `Sumset_singleton_left (k) (A) : Sumset {k} A = (· + k) '' A` — S9 from the
   S6 roadmap. The translate identity; generalizes `Sumset_zero_left` (k = 0).
2. `Sumset_singleton_right (A) (k) : Sumset A {k} = (· + k) '' A` — right form.
3. `density_additive_zero_singleton (A) (hA : DensityExists A) : DensityAdditive {0} A`
   — S8 from the roadmap. The degenerate witness: `{0}` has density 0 and
   `{0} + A = A`, so the relation `DensityAdditive` is non-vacuous. (Not a
   witness for #335 proper — `{0}` lacks positive density.)
4. `density_additive_lt_one_left (h : DensityAdditive A B) (hB : HasPositiveDensity B) : asympDensity A < 1`
   — strict complement bound from `d(A) + d(B) ≤ 1` and `d(B) > 0`.
5. `density_additive_lt_one_right` — symmetric.

## Lean snapshot after this session

- `proofs/Proofs/Erdos335Problem.lean`: **414 LOC**, **40 theorems/lemmas**,
  8 defs, **0 sorries**, **3 axioms** (unchanged: `weyl_equidistribution`,
  `fractional_part_density_additive`, `erdos_335_conjecture`).

## Remaining sub-goal

S7 (Schnirelmann↔asymptotic density bridge) from the S6 roadmap is still open;
it requires `import Mathlib.Combinatorics.Schnirelmann` and ~40–80 LOC and was
not attempted this session.

## Non-goals respected

- Did not touch the 3 deep axioms (they are mathematically necessary / are the
  open problem itself).
- Did not re-add the removed `plunnecke_ruzsa_lower` axiom.
