# Toolchain v4.31 Rename Map (Mechanic batch input)

**Epic:** #37508 · **Prep for:** #38064 (Mechanic batch: renames)
**Pins:** Lean `v4.26.0` / Mathlib `2df2f0150c27` → Lean `v4.31.0` / Mathlib `9a9483a92959`
**Generated:** 2026-07-11, from the in-flight full failure inventory (`proofs/spike-logs-full/`, 274 logs / 271 FAIL at snapshot time — inventory still running; re-harvest before closing #38064).

**Method.** Old→new pairs were extracted from three evidence sources, in decreasing strength:
1. **Compiler deprecation messages** in the failure logs (`` `X` has been deprecated: Use `Y` instead ``) — the new pin itself names the replacement.
2. **Deprecation `alias` lines** in the *old* pin's Mathlib source (aliases that were live at v4.26 and deleted by v4.31) — the alias target is the new name; target existence re-verified in the v4.31 source.
3. **Direct search of the v4.31 Mathlib source** (inside the running spike containers) for the renamed declaration.

A key discovery: **not every "Unknown constant" in the logs is a migration regression.** Several names (`Complex.abs`, `Real.sqrt_eq_iff_sq_eq`, `summable_of_summable_norm`, `IsPGroup.isSolvable`, …) are absent from the **old** pin's source too — those files were already broken before the bump (pre-existing failures, mostly Aristotle drafts / sorried files). They are listed separately in §4 so the Mechanic batch doesn't chase phantom renames.

"Affected files" = count of retained failure logs mentioning the name at snapshot time (cascades inflate this slightly: an error in an imported `Proofs/*.lean` appears in every dependent's log), with example files.

---

## 1. Confident renames (verified in v4.31 source or self-documented by the compiler)

### 1a. Galois / group theory cluster (largest, unblocks AbelRuffini family)

| Old name | New name | Evidence | Affected files |
|---|---|---|---|
| `IsSolvableByRad` | `solvableByRad` | deprecation msg in logs; **type changed**: `F → E → Prop` is now `IntermediateField F E` (membership `x ∈ solvableByRad F E`) — see §5 | 22 (AbelRuffini, AbelRuffiniGaloisExtensionsOQ02OQ01, …) |
| `solvableByRad.isSolvable'` | `isSolvable_gal_of_irreducible` | deprecation msg; namespace + argument order changed (dot notation must go) — see §5 | 22 (same cluster) |
| `alternatingGroup.isSimpleGroup_five` | `alternatingGroup.isSimpleGroup` | deprecation note in v4.31 `GroupTheory/SpecificGroups/Alternating.lean` (since 2026-04-28); A5-specific instance superseded by the general `Fin (n+5)` instance | 15–16 (AbelRuffini family) |
| `IsCyclic.commutative` | `IsCyclic.isMulCommutative` | deprecation msg; **`.comm` field projection breaks** (`IsMulCommutative` has no `comm` field) — see §5 | 4–5 |
| `commutative_of_cyclic_center_quotient` | `MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center` | deprecation msg | 2 |
| `nilpotent_of_mulEquiv` | `Group.nilpotent_of_mulEquiv` | deprecation msg | 2–4 |
| `nilpotent_of_surjective` | `Group.nilpotent_of_surjective` | deprecation msg | 2 |
| `isNilpotent_of_ker_le_center` | `Subgroup.isNilpotent_of_ker_le_center` | deprecation msg | 2 |

### 1b. Order / algebra basics

| Old name | New name | Evidence | Affected files |
|---|---|---|---|
| `le_or_lt` | `le_or_gt` | old-pin alias (2025-05-11); v4.31 `Order/Defs/LinearOrder.lean:100` | 16 (Erdos1050Problem, Erdos1062Problem, …) |
| `Ne.lt_or_lt` | `Ne.lt_or_gt` | old-pin alias (2025-06-07); v4.31 `Order/Basic.lean:337` | 1 |
| `lt_or_lt` | `gt_or_lt` | old-pin alias (2025-06-07) | 1 (invalid-field form) |
| `eq_or_gt_of_le` | `eq_or_lt_of_le'` | old-pin alias (2025-06-08); v4.31 has `eq_or_lt_of_le` + `to_dual eq_or_lt_of_le'` | (see `Nat.eq_or_gt_of_le` §2) |
| `div_le_div_iff` | `div_le_div_iff₀` | v4.31 `Algebra/Order/GroupWithZero/Basic.lean:1430` (same statement, `0 < b`, `0 < d`) | 5–9 |
| `div_lt_div_iff` | `div_lt_div_iff₀` | v4.31 ibid.:1463 | 2–8 |
| `pow_le_pow_right` | `pow_le_pow_right₀` | v4.31 ibid.:457 (`1 ≤ a → m ≤ n → a^m ≤ a^n`) | 3–5 |
| `pow_le_pow_left` | `pow_le_pow_left₀` | v4.31 ibid.:470 | 1 |
| `pow_lt_pow_left` | `pow_lt_pow_left₀` | v4.31 ibid.:546 | 1 |
| `one_lt_pow_of_one_lt_of_ne_zero` | `one_lt_pow₀` | v4.31 ibid.:443 (`1 < a → n ≠ 0 → 1 < a^n`) | 2–3 |
| `pow_eq_zero` | `eq_zero_of_pow_eq_zero` | old-pin alias (2025-10-14); v4.31 `Algebra/GroupWithZero/Basic.lean:195` (note: `[IsReduced R]` hypothesis) | 2 |
| `isUnit_of_mul_eq_one` | `IsUnit.of_mul_eq_one` | old-pin alias; v4.31 `Algebra/Group/Units/Defs.lean:392` (now needs `[IsDedekindFiniteMonoid M]`, satisfied by comm monoids) | 1 |
| `mul_le_mul_right'` | `_root_.mul_le_mul_left` | deprecation msg (left/right convention swap — check each use site!) | 1 |

### 1c. `not_mem` → `notMem` wave

All verified in v4.31 source (`Data/Set/Basic.lean`, `Data/Finset/*`); old pin carried the deprecated aliases.

| Old name | New name | Affected files |
|---|---|---|
| `Finset.card_insert_of_not_mem` | `Finset.card_insert_of_notMem` | 6 |
| `Finset.not_mem_empty` | `Finset.notMem_empty` | 2–3 |
| `Set.not_mem_empty` | `Set.notMem_empty` | 2 |
| `Finset.eq_empty_iff_forall_not_mem` | `Finset.eq_empty_iff_forall_notMem` | 3 |
| `Set.eq_empty_iff_forall_not_mem` | `Set.eq_empty_iff_forall_notMem` | 1 |
| `Finset.ne_univ_iff_exists_not_mem` | `Finset.ne_univ_iff_exists_notMem` | 1 |

Mechanic rule of thumb: any `*_not_mem*` unknown-constant failure → try `notMem` camelCase first.

### 1d. `diff` → `sdiff` wave (Set/measure)

All self-documented by deprecation messages in the logs:

| Old name | New name | Affected files |
|---|---|---|
| `Set.mem_diff` | `Set.mem_sdiff` | 3 |
| `Set.diff_empty` | `Set.sdiff_empty` | 2–4 |
| `MeasureTheory.measure_diff_null` | `MeasureTheory.measure_sdiff_null` | 3 |
| `Convex.mem_extremePoints_iff_mem_diff_convexHull_diff` | `Convex.mem_extremePoints_iff_mem_sdiff_convexHull_sdiff` | 2 |

### 1e. Analysis / measure theory

| Old name | New name | Evidence | Affected files |
|---|---|---|---|
| `Filter.eventually_of_forall` | `Filter.Eventually.of_forall` | v4.31 `Order/Filter/Basic.lean` (old alias deleted) | 3–4 |
| `continuous_finset_prod` | `continuous_finsetProd` | deprecation msg | 4 |
| `continuous_finset_sum` | `continuous_finsetSum` | deprecation msg | 1 |
| `MeasureTheory.integral_finset_sum` | `MeasureTheory.integral_finsetSum` | deprecation msg | 1 |
| `MeasureTheory.Integrable.bdd_mul'` | `MeasureTheory.Integrable.bdd_mul` | deprecation msg | 1 |
| `integral_mul_left` | `MeasureTheory.integral_const_mul` | old-pin alias; v4.31 `MeasureTheory/Integral/Bochner/Basic.lean:292` | 1 |
| `MeasureTheory.Lp.memℒp` | `MeasureTheory.Lp.memLp` | v4.31 `LpSpace/Basic.lean:183` (`Memℒp`→`MemLp` wave) | 1 |
| `Memℒp.of_bound` | `MemLp.of_bound` | v4.31 `LpSeminorm/Basic.lean:553` | 2 |
| `memℒp_two_iff_integrable_sq_norm` | `memLp_two_iff_integrable_sq_norm` | v4.31 `L2Space.lean:47` | 1 |
| `norm_sq_eq_inner` | `norm_sq_eq_re_inner` | old-pin alias `norm_sq_eq_inner'` → `norm_sq_eq_re_inner` (2025-04-22); unprimed form same target | 1 |
| `set_integral_const` | `setIntegral_const` | v4.31 `MeasureTheory/Integral/Bochner/Set.lean:527` (note RHS now `μ.real s • c`) | 1 |
| `set_integral_congr` | `setIntegral_congr_fun` | v4.31 ibid.:73 (`₀` variant for NullMeasurableSet) | 1 |
| `tsum_pos` | `Summable.tsum_pos` | v4.31 `Topology/Algebra/InfiniteSum/Order.lean:230` (`to_additive Summable.tsum_pos`) | 1 |

### 1f. Data / number theory / misc

| Old name | New name | Evidence | Affected files |
|---|---|---|---|
| `ZMod.natCast_zmod_eq_zero_iff_dvd` | `ZMod.natCast_eq_zero_iff` | old-pin alias (2025-06-30); v4.31 `Data/ZMod/Basic.lean:518` | 4–8 |
| `Matrix.smul_mulVec_assoc` | `Matrix.smul_mulVec` | old-pin alias (2025-08-14); v4.31 `Data/Matrix/Mul.lean:806` | 4 |
| `Finset.range_succ` | `Finset.range_add_one` | v4.31 `Data/Finset/Range.lean:79` (`succ`→`add_one` wave — expect siblings like `sum_range_succ` to follow the same pattern) | 2 |
| `Nat.Prime.multiplicity_choose` | `Nat.Prime.emultiplicity_choose` | v4.31 `Data/Nat/Multiplicity.lean:211` (`multiplicity`→`emultiplicity` refactor; result type is `ℕ∞`) | 1 |
| `Nat.Prime.multiplicity_choose'` | `Nat.Prime.emultiplicity_choose'` | v4.31 ibid.:192 | 1 |
| `Nat.dvd_sub'` | `Nat.dvd_sub` | Lean core rename (v4.26→v4.31): unconditional truncated-sub version took the unprimed name | 2–3 |
| `List.get?` | `List.getElem?` / `l[i]?` | Lean core: `List.get?` removed in v4.28+ | 3 |
| `Algebra.id.map_eq_id` | `Algebra.algebraMap_self` | v4.31 `Algebra/Algebra/Defs.lean:396` (`algebraMap R R = .id _`) | 1 |
| `AdjoinRoot.liftHom` | `AdjoinRoot.liftAlgHom` | v4.31 `RingTheory/AdjoinRoot.lean:307`; **signature changed** (now takes `i : R →ₐ[S] T`) — see §5 | 2 |
| `Polynomial.aeval_pow` | `map_pow` | `aeval` is an `AlgHom`; dedicated lemma gone, generic `map_pow` applies | 1 |
| `Finset.toSet` (`s.toSet`) | coercion `(↑s : Set α)` | `toSet` absent from v4.31 `Data/Finset/*`; coe API (`mem_coe`, `coe_inj`, …) is the only spelling | 9 (AmgmInequalityOQ02 + dependents) |
| `List.Chain'` | `List.IsChain` | deprecation msg | 2 |
| `Fin.coe_sub` | `Fin.val_sub` | deprecation msg | 2 |
| `Fin.coe_castSucc` | `Fin.val_castSucc` | deprecation msg | 1 |
| `Nat.twoPowSum_bitIndices` | `Nat.sum_map_two_pow_bitIndices` | deprecation msg | 2 |
| `Finset.toFinset_bitIndices_twoPowSum` | `Finset.toFinset_bitIndices_sum_two_pow` | deprecation msg | 2 |
| `Finset.filter_card_add_filter_neg_card_eq_card` | `Finset.card_filter_add_card_filter_not` | deprecation msg | 1 |
| `SimpleGraph.chromaticNumber_pos` | `SimpleGraph.Colorable.chromaticNumber_pos` | deprecation msg | 1 |
| `Set.ncard_image_of_injOn` | `Set.InjOn.ncard_image` | deprecation msg | 1 |
| `Real.geom_mean_eq_arith_mean_weighted_iff'` | `Real.geom_mean_eq_arith_mean_weighted_iff_of_pos'` | deprecation msg | 1 |

### 1g. Tactic-level deprecation (warning-only today, will break later)

| Old | New | Affected files |
|---|---|---|
| `push_neg` | `push Not` | 93 logs carry the warning (non-fatal; batch-fixable with sed but safe to defer) |

---

## 2. Needs verification (inferred — confirm against v4.31 before batch-applying)

| Old name | Proposed new name | Basis | Affected files |
|---|---|---|---|
| `Nat.eq_or_gt_of_le` | `Nat.eq_or_lt_of_le` (core) or `eq_or_lt_of_le'` | generic version's old-pin alias maps to `eq_or_lt_of_le'`; Nat-specific core lemma likely `Nat.eq_or_lt_of_le` | 1–4 |
| `Finset.sort_sorted` | `Finset.sortedLE_sort` | v4.31 has aliases `sort_sorted_lt := sortedLT_sort`, `sort_sorted_gt := sortedGT_sort` (2025-11-27); unsuffixed form assumed to follow pattern | 3 |
| `tsum_add` | `Summable.tsum_add` | same wave as `tsum_pos` (tsum lemmas moved into `Summable` namespace) | 1 |
| `tsum_eq_zero_add` | `Summable.tsum_eq_zero_add` | same wave | 1 |
| `Equiv.Perm.apply_inv_self` | `Equiv.apply_symm_apply` (via `Perm.inv_def`) | Perm-specific lemma absent from v4.31 (and old-pin grep only finds the `Isometry`/`MulAut` versions — may be partially pre-existing) | 3 |
| `Zsqrtd.mul_def` | none direct — use `Zsqrtd.mul_re` / `Zsqrtd.mul_im` + `Zsqrtd.ext` | `mul_def` absent v4.31 `NumberTheory/Zsqrtd/Basic.lean`; also absent old pin (may be pre-existing) | 5 (FundamentalArithmeticOQ02 + dependents) |
| `List.Sorted` (as a projection/type) | `List.SortedLE` / `SortedGE` / `SortedLT` / `SortedGT` | v4.31 `Data/List/Sort.lean:391-397`; **formulation changed** (Monotone `l.get` instead of Pairwise) — likely Doctor-tier | 2 |
| `SimpleGraph.cliqueFree` (lowercase, dot-notation) | `SimpleGraph.CliqueFree` | error is in project files; likely a project-local shim in a cascade-failed import — inspect Erdos1036OQ01's imports first | 2 |
| `Nat.coprime_iff_disjoint` | `Nat.Coprime`↔`Disjoint primeFactors` lemma (exact v4.31 name unresolved) | absent both pins under that spelling | 1 |
| `Nat.choose_two_middle` | unresolved | not found in v4.31 `Data/Nat/Choose/` | 1 |
| `MeasureTheory.Measure.restrict_prod_eq_prod_restrict` | unresolved (`Measure.prod_restrict`?) | not found in v4.31 `Constructions/Prod/Basic.lean` | 1 |
| `Finset.sum_sort` | unresolved (goal shape: `(s.sort ≤).sum = ∑ x ∈ s, x`) | absent both pins — possibly pre-existing | 1 |
| `integral_eq_sub_of_hasDerivAt` (+ `_of_le`, `hasDeriv_right`, `integral_hasDerivAt_right`) | names unchanged under `intervalIntegral.`, but **module moved**: `MeasureTheory.Integral.FundThmCalculus` → `MeasureTheory.Integral.IntervalIntegral.FundThmCalculus` | v4.31 file layout; fix imports / re-check `open intervalIntegral` | 4 |
| `summable_of_summable_norm` | `Summable.of_norm` | absent old pin (pre-existing?); proposed target standard in current Mathlib | 1 |
| `ciSup_empty` | `iSup_of_empty` / `Real.iSup_of_isEmpty` (?) | absent both pins under old spelling | 1 |
| `zero_rpow` | `Real.zero_rpow` / `NNReal.zero_rpow` (namespace qualification) | unqualified form absent both pins | 1 |
| `isBounded_iUnion` | `Bornology.isBounded_iUnion` (qualification) | exists old pin `Topology/Bornology/Basic.lean`; check v4.31 namespace | 1 |
| `PiLp.equiv_symm_apply` | `WithLp.equiv_symm_apply` family | `PiLp.equiv` → `WithLp.equiv` migration (old pin already `WithLp`) — may be pre-existing | 1 |
| `sigma_isMultiplicative` | `Nat.ArithmeticFunction.isMultiplicative_sigma` | probable qualification issue | 1 |
| `Group.IsSolvable` | `IsSolvable` | namespace | 1 |

---

## 3. Name unchanged — transitive-import losses (fix = add explicit import)

These constants **exist in v4.31 under the same name**; the failing files relied on transitive imports that the reorganized v4.31 import graph no longer provides. Mechanic fix: add the explicit `import` line.

| Constant | v4.31 defining module | Affected files |
|---|---|---|
| `Cardinal.mk_real` | `Mathlib.Analysis.Real.Cardinality` | 3 (AlgebraicNumbersCountableOQ02 family) |
| `Countable.exists_surjective_nat` → root-level `exists_surjective_nat` | `Mathlib.Data.Countable.Defs` (root namespace in both pins — also drop the `Countable.` prefix) | 3 |
| `Complex.finrank_real_complex` | moved from `Mathlib.LinearAlgebra.Complex.FiniteDimensional` (old) — locate v4.31 module and re-import | 2 |
| `ZMod.wilsons_lemma` | `Mathlib.NumberTheory.Wilson` (same in both pins — import-graph change upstream) | 1 |
| `Polynomial.Gal` | `Mathlib.FieldTheory.PolynomialGaloisGroup` (def present v4.31:55) | 2 (AngleTrisection family) |
| `Set.Countable.isGδ_compl` | `Mathlib.Topology.Separation.GDelta` (v4.31:41) | 2 |
| `is_const_of_deriv_eq_zero` | `Mathlib.Analysis.Calculus.MeanValue` (v4.31:751, `_root_`) | 1 |
| `Nat.nth`, `Nat.nth_count`, `Nat.nth_strictMono`, `Nat.nth_mem_of_infinite` | `Mathlib.Data.Nat.Nth` | 1 |
| `Real.rpow_le_rpow_of_exponent_le` | `Mathlib.Analysis.SpecialFunctions.Pow.Real` (v4.31:615) — failing use is unqualified; qualify or `open Real` | 1 |
| `Real.hasDerivAt_exp` | `Mathlib.Analysis.SpecialFunctions.ExpDeriv` (verify) | 1 |

---

## 4. Pre-existing failures — NOT migration renames (absent from the OLD pin too)

These names do not exist in Mathlib `2df2f0150c27` either; the files referencing them were already failing before the toolchain bump (mostly Aristotle drafts and sorried WIP files). **Exclude from the Mechanic rename batch**; route to the general repair backlog. Correct modern spellings noted where known.

| Old name | Modern equivalent | Affected files |
|---|---|---|
| `Complex.abs` | `norm` / `‖·‖` (`Complex.norm_*` lemma family; `Complex.abs` was removed from Mathlib before the old pin) | 11 direct + cascades (Erdos1039/1048 families; 27–28 error occurrences) |
| `Real.sqrt_eq_iff_sq_eq` | `Real.sqrt_eq_iff_mul_self_eq` / `Real.sqrt_eq_cases` family (verify) | 2 |
| `Real.exp_le_one_of_nonpos` | `Real.exp_le_one_iff` (verify) | 1 |
| `IsPGroup.isSolvable` | derive via `IsNilpotent.to_isSolvable` (`GroupTheory/Nilpotent.lean:1153`) | 2 |
| `Nat.factorial_le_factorial` | absent from both pins (`Data/Nat/Factorial/Basic.lean` has neither name nor `factorial_mono`); monotonicity is likely spelled `Nat.factorial_le_factorial` no more — resolve with `exact?` (unresolved) | 1 |
| `Polynomial.continuous_eval` | `Polynomial.continuous` / `p.continuous_aeval` (verify) | 1 |
| `intermediate_value_zero_of_neg_of_pos` | `intermediate_value_Icc` family | 1 |
| `inv_anti_of_pos` | `inv_le_inv_of_le` / `one_div` antitone family | 1 |
| `SubsemiringClass.coe_pow` | generic `map_pow` / push-cast | 1 |
| project-local names (`f_perfect_square`, `carleson_hunt_maximal`, `lambie_hanson_counterexample`, `FourthRoot2Degree4OQ02.*`, `Erdos1039.Complex.abs`, `FundamentalTheoremAlgebra.splits_over_complex`, `sqrt_k2_plus_1_lt_k_succ`, bare `p`/`q`/`N`/`s`/`hlt`) | cascade fallout from failed sibling `Proofs/*.lean` imports — resolve by fixing the imported file | — |

---

## 5. Renames with API/signature changes — flag for Doctor, not blind sed

1. **`IsSolvableByRad` → `solvableByRad`**: the replacement is an `IntermediateField F E`, not a predicate. `IsSolvableByRad F α` becomes `α ∈ solvableByRad F E`. Every use site needs rewriting, and `solvableByRad.isSolvable'` → `isSolvable_gal_of_irreducible` swaps argument roles (`Irreducible q` vs root hypothesis) — the logs show application-type-mismatch errors even after the rename.
2. **`IsCyclic.commutative` → `IsCyclic.isMulCommutative`**: returns `IsMulCommutative G`, which has **no `.comm` field** (8 invalid-field failures). Use `mul_comm` via the derived `CommMonoid`/`CommGroup` instance, or `.is_comm.comm` per the new structure layout (verify field name).
3. **`AdjoinRoot.liftHom` → `AdjoinRoot.liftAlgHom`**: now takes an `R →ₐ[S] T` argument instead of `(x : S) (aeval x f = 0)` directly; companion `.toRingHom` projections in the logs also break.
4. **`HasDerivAt` dot-notation breakage**: `(Polynomial.hasDerivAt p x).div`, `.const_mul` etc. fail with `HasFDerivAtFilter.div` not found — `HasDerivAt` now unfolds to `HasFDerivAtFilter` before dot-resolution. Qualify the lemma (`HasDerivAt.div _ _ _`) instead of dot notation. (3 invalid-field failures: `div`, `const_mul` ×2.)
5. **`List.Sorted` → `SortedLE`/`SortedGE`/`SortedLT`/`SortedGT`**: definition changed from `Pairwise r` to `Monotone l.get`; proofs about sortedness need adaptation, and `Finset.sort_sorted`-style lemmas follow the new naming (`sortedLE_sort`).
6. **`Equiv.Perm.IsThreeCycle.alternating_normalClosure`: REMOVED in v4.31 with no alias** (the A5-simplicity development was refactored away in favor of the general `alternatingGroup.isSimpleGroup`). The 2 affected files (AbelRuffiniGaloisExtensionsOQ03*) must derive `normalClosure = ⊤` from simplicity instead. Also note: dot notation `hg.alternating_normalClosure` on `hg : cycleType = {3}` no longer resolves through the `IsThreeCycle` unfolding.
7. **`setIntegral_const`**: RHS changed from `(μ s).toReal • c` to `μ.real s • c`.
8. **`push_neg` → `push Not`**: warning-only in v4.31, but slated for removal; 93 files emit it.

---

## Summary counts

- **Confident mappings (§1):** 48 pairs (incl. 6 notMem-wave + 4 sdiff-wave entries), of which 8 also need API-level attention (§5).
- **Needs verification (§2):** 19 entries.
- **Import-only fixes (§3):** 10 constants.
- **Pre-existing / out-of-scope (§4):** 10+ names + project-local cascade noise — keep out of the rename batch.
- **Top clusters by affected files:** AbelRuffini/Galois (`IsSolvableByRad`+`isSolvable'`+`isSimpleGroup_five`, ~22 files), `le_or_lt` (16), `Complex.abs` (11, pre-existing), `Finset.toSet` (9), `div_le_div_iff`/`div_lt_div_iff` (≈9), `ZMod.natCast_zmod_eq_zero_iff_dvd` (8).

**Unresolved (could not map):** `Nat.choose_two_middle`, `MeasureTheory.Measure.restrict_prod_eq_prod_restrict`, `Finset.sum_sort`, `Nat.factorial_le_factorial`, `ciSup_empty`, `Nat.coprime_iff_disjoint` — all single-file; resolve during the batch with `exact?`/loogle.

*Re-harvest procedure:* the inventory is still running; rerun the extraction one-liners in this file's git history (deprecation-pair grep + unknown-constant grep over `proofs/spike-logs-full/shard-*/**.log`) before finalizing #38064's batch list.
