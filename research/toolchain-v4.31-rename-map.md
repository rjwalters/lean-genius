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
| `solvableByRad.isSolvable'` | `isSolvable_gal_of_irreducible` | **Batch-1 correction:** the deprecated alias still exists in v4.31 (since 2026-02-28); the real breakage is the *hypothesis type* (`IsSolvableByRad F α` → `α ∈ solvableByRad F E`) and argument order (root-membership hypothesis first) — see §5 | 22 (same cluster) |
| `alternatingGroup.isSimpleGroup_five` | **NOT removed — import moved** to `Mathlib.GroupTheory.SpecificGroups.Alternating.Simple` | **Batch-1 correction:** the constant still exists in v4.31; the fix is adding the explicit import, not rewriting to the general `isSimpleGroup` | 15–16 (AbelRuffini family) |
| `IsCyclic.commutative` | `IsCyclic.isMulCommutative` | deprecation msg; **`.comm` field projection breaks** — **Batch-1 confirmed:** the projection is `.is_comm.comm` (`is_comm : Std.Commutative`) — see §5 | 4–5 |
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
| `div_le_div_right` | `div_le_div_iff_of_pos_right` | **Batch-1 correction:** NOT the ₀ form | ~5 |
| `div_lt_div_right` | `div_lt_div_iff_of_pos_right` | **Batch-1 correction:** NOT the ₀ form | ~5 |
| `abs_add` | `abs_add_le` | Batch-1 verified (v4.31 renamed the triangle inequality) | ~6 |
| `pi_lt_four` (unqualified) | `Real.pi_lt_four` | Batch-1 verified — needs `Real.` qualification | 1–2 |
| `tendsto_const_div_atTop_nhds_0_nat` | `tendsto_const_div_atTop_nhds_zero_nat` | Batch-1 verified | 1–2 |

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

## 6. New mechanical classes (discovered in Mechanic batch 1 — not renames, but scriptable)

1. **Orphaned consecutive doc-comments**: `/-- a -/ /-- b -/ decl` now hard-errors (`unexpected token '/--'; expected 'lemma'|'theorem'|…`). Fix: demote all but the last doc-comment before a declaration to regular `/- … -/` comments. Dozens of files (Erdos161/554/716/968, Erdos476OQ05, …). Python demotion script pattern proven in batch 1 (7 files, 5 green).
2. **Big-operator `in` syntax**: `∑ k in s, …` / `∏ k in s, …` now hard-errors (`unexpected token 'in'; expected '∈'`). Fix: `in` → `∈` **only inside big-operator binders** (never touch `Finset.sum`-applied terms or other ` in ` uses). Widespread (e.g. Erdos524Problem).
3. **`∃ (L : Type*) [Field L], …` instance binders inside `∃`** now parse errors. v4.31-accepted form: `∃ (L : Type*) (_ : Field L), …` with downstream `letI`/`haveI` to activate the instance (or restructure via a Σ-type). Blocks AbelRuffiniGaloisExtensionsOQ05 → AbelRuffiniOQ10.
4. **`decide`/`native_decide` maxRecDepth regressions** (TestApi203) — Doctor-class, needs `set_option maxRecDepth` or proof restructure.
5. **`native_decide` × `noncomputable` catch-22**: def needs `noncomputable` under v4.31 but is evaluated by `native_decide` (PicksTheoremOQ01OQ01OQ01, LagrangeFourSquaresOQ01OQ03, Erdos662Problem) — Doctor-class, needs computable reformulation.

### Batch-2 discoveries (unmasked after parse-error fixes; mostly Doctor-class)

- **`PartENat` is gone** from v4.31 (`multiplicity` refactor completed; use `ℕ∞`/`emultiplicity`). ChebyshevPNTBridgeOQ01 and siblings.
- **`Λ` is now a reserved/invalid identifier character** (`unexpected token 'Λ'; expected identifier`) — files defining von-Mangoldt-style notation `Λ` break (BoundedPrimeGapsOQ04).
- **`Irreducible.multiplicity_factorial`** removed (emultiplicity wave), **`Nat.log_lt`** renamed (verify: `Nat.log_lt_of_lt_pow`?), **`Nat.find_eq_iff`** dot-form drift (CollatzStructuredOQ03).

### Batch-3 resolutions of the batch-2 discoveries (grep-verified in v4.31 Mathlib source in-container)

- **`Nat.log_lt`** → `Nat.log_lt_iff_lt_pow (hb : 1 < b) (hy : y ≠ 0) : log b y < x ↔ y < b ^ x` (Data/Nat/Log.lean:107); the one-directional `Nat.log_lt_of_lt_pow (hy : y ≠ 0) : y < b ^ x → log b y < x` also exists (line 175). Signature change (extra `hb`) → semi-mechanical, per-site.
- **`Nat.find_eq_iff` still EXISTS** (`Mathlib/Data/Nat/Find.lean:85`) — the `Unknown constant Nat.find_eq_iff.mpr` residual is a transitive-import loss: add `import Mathlib.Data.Nat.Find` (→ §3).
- **`Nat.card_Icc` / `Finset.card_Icc` still EXIST** (`Mathlib/Order/Interval/Finset/Nat.lean:82` et al.) — import loss: add `import Mathlib.Order.Interval.Finset.Nat` (→ §3).
- **`Real.tendsto_log_nat_atTop` is GONE** (zero hits for `log_nat_atTop` in all of v4.31 Mathlib). Rebuild per-site as `Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop` (`tendsto_log_atTop` confirmed at Analysis/SpecialFunctions/Log/Basic.lean:350). Doctor-class (goal-shape dependent).
- **`Nat.one_lt_iff_ne_one`** and **`Nat.not_eq_zero_of_lt`**: zero hits in v4.31 Mathlib AND Batteries — removed (were core/Batteries lemmas). Both are omega-trivial: replace call sites with `omega` (or `Nat.pos_iff_ne_zero` variants). Semi-mechanical.
- **`Nat.Prime.multiplicity_choose`** → `Prime.emultiplicity_choose` / `Prime.emultiplicity_choose'` (confirmed used at NumberTheory/Padics/PadicVal/Basic.lean:621/631); ℕ∞-valued now — sites comparing to `PartENat` need the emultiplicity rework (Doctor-class).
- Verified-green big-op-only files flip immediately (BinomialTheorem, Erdos307Aristotle, Erdos524Problem, RandomizedMaxcutOQ02); most other bigop roots carry deeper signature/tactic drift.

### Batch-3 discoveries

- **Trailing orphaned doc-comment before `end`** (new mechanical class): a `/-- … -/` documenting commented-out code or serving as trailing prose, with no declaration following (next token is `end` or EOF), now hard-errors `unexpected token 'end'; expected 'lemma'`. Lean reports the error at the END of the orphaned doc block, which can be mid-line (col ≠ 0). Fix: demote to `/- … -/`. 22 files fixed in batch 3 (Erdos6/13/15/26/53/61/64/75/77/145/158/170/186/208/215/306/520/541/768/779/1174/1177 Problem).
- **Double set-binder `∀ x y ∈ S, …` no longer parses** (`unexpected token '∈'; expected ','`) — split into `∀ x ∈ S, ∀ y ∈ S, …` (Erdos174Problem). Sweepable pattern: `[∀∃] \w+ \w+ ∈`.
- **`Finset.card_Icc` → `Nat.card_Icc`** for ℕ-intervals (NOT an import loss — Erdos13Problem has `import Mathlib` and still errored; the ℕ lemma lives in `namespace Nat`, Order/Interval/Finset/Nat.lean:82). Confident rename.
- **Wave-E lesson:** fix ALL sites of a removed constant before re-verifying — Lean reports only the first few errors, so a file can hide more sites of the same class past the reported window (Erdos683Problem had 3 `Nat.one_lt_iff_ne_one` sites; diag showed 1).

### Batch-4 discoveries

- **BAD-IMPORT class (biggest mechanical class found): 294 not-yet-green FAIL files import Mathlib modules that no longer exist in v4.31** — these files hard-fail at import resolution (`bad import 'Mathlib.X'`) before any elaboration, so their earlier diag classes were masked/bulk-build artifacts. Top removed/renamed modules: `Algebra.BigOperators.Group.Finset` (49), `Data.Rat.Basic` (35), `Order.Filter.AtTopBot` (26), `Data.Real.Irrational` (22), `Analysis.Asymptotics.Asymptotics` (22), `Data.Set.Finite` (22), `NumberTheory.ArithmeticFunction` (19), `Topology.Instances.Real` (16), `Data.Complex.Exponential` (13), `GroupTheory.Subgroup.Basic` (7). Repair applied: drop bad import lines + prepend umbrella `import Mathlib` (wave H). Module existence list extractable from the packages volume: `docker run --rm -v lean-mathlib-packages-v431:/pkgs alpine sh -c "cd /pkgs/mathlib && find Mathlib -name '*.lean'"`.
- **`Nat.card` migration in group theory**: `alternatingGroup.nontrivial_of_three_le_card` and `Equiv.Perm.IsThreeCycle.alternating_normalClosure` (now deprecated → `alternatingGroup.isSimpleGroup`) take `Nat.card α`, not `Fintype.card α`. Bridge per-site: `(by simpa using h5)` for argument positions / `rw [Nat.card_eq_fintype_card]; omega` inside tactic args. Flipped AbelRuffiniGaloisExtensionsOQ03 + OQ03OQ01 green.
- **Subgroup/quotient `Fintype` synthesis loss**: `Fintype ↥H` / `Fintype (G ⧸ N)` no longer synthesize from `[Fintype G]` (decidability requirements). Fix: `haveI : Fintype ↥H := Fintype.ofFinite ↥H` (AbelRuffiniGaloisExtensionsOQ05).
- **`convert` → `convert!`**: proofs copied from Mathlib Archive (Wiedijk100Theorems/AbelRuffini.lean `degree_Phi`) drifted; upstream now uses `convert!`. When a project file is a copy of an Archive/Mathlib proof, diff against the v4.31 source first.
- **NEVER-COMPILED class (not migration drift)**: files with single-letter `Unknown identifier` errors (`ι`, `n`, `p`, `k`, `A`, `B`, `X`, `V`, `hp`, `d_2`, …) have free variables in *definition bodies* — `set_option autoImplicit true` does NOT fix them (0/11 flip rate in wave F; autoImplicit only binds signature-level frees). These files were landed unverified during ENOSPC eras and never compiled on v4.26 either. Doctor/rewrite tier, arguably out of migration scope.
- **Orphan doc-comment before mid-file `end`** also occurs (not just trailing-at-EOF): scanner must treat `end <Section>` mid-file as an orphan boundary (Hilbert22Uniformization had 5). Full nesting-aware scanner: `proofs/batch2/sweep_orphan_binder.py` (129 more files swept in wave F).
- **Double set-binder regex hits prose**: `[∀∃] \w+ \w+ ∈` matches inside doc comments/prose (BertrandsPostulateOQ03OQ04OQ01, PartitionTheoremOQ01) — do NOT blind-sweep; fix code sites by hand (5 sites: Erdos174Problem, Erdos339Problem ×2, Erdos434Problem, Erdos434Frobenius — the latter flipped green immediately).
- **`IsSolvable (ZMod n)` was never legal** (ZMod n has no multiplicative `Group` instance) — retype to `Multiplicative (ZMod n)` (AbelRuffiniGaloisExtensionsOQ05 `cyclic_group_realizable`).

### Batch-5 resolutions (grep-verified in v4.31 Mathlib source in-container)

Singleton unknown-const renames applied + verified in wave S (68 files edited):

| old | new | notes |
|---|---|---|
| `Nat.factors` | `Nat.primeFactorsList` | |
| `le_of_not_lt` | `le_of_not_gt` | same statement mod `>` notation |
| `Nat.eq_or_gt_of_le` | `Nat.eq_or_lt_of_le` | disjunct order/form identical |
| `Nat.primeFactors_nonempty h` | `Nat.nonempty_primeFactors.mpr h` | new form is iff `… ↔ 1 < n` (Data/Nat/PrimeFin.lean:88) |
| `Finset.card_Icc` | `Nat.card_Icc` | ℕ-intervals; confirmed again (batch-3 entry) |
| `div_le_iff`/`le_div_iff`/`lt_div_iff`/`div_lt_iff`/`div_lt_div_iff` | `…₀` | positivity-hypothesis family |
| `pow_lt_one`/`pow_le_pow_right` | `pow_lt_one₀`/`pow_le_pow_right₀` | bare (non-`Nat.`) forms only |
| `Multiset.toFinset_card_le_card` | `Multiset.toFinset_card_le` | Data/Finset/Card.lean:192 |
| `integral_mul_left` | `integral_const_mul` | Bochner/Basic.lean:292 |
| `Set.ncard_coe_Finset` | `Set.ncard_coe_finset` | case-only rename, Data/Set/Card.lean:681 |
| `Set.ncard_Icc` (ℕ) | `Set.ncard_Icc_nat` | no hypothesis arg anymore (simp lemma, Order/Interval/Set/Nat.lean:22) |
| `Nat.pow_dvd_pow_of_dvd` | `pow_dvd_pow_of_dvd` | root-level generic, same arg order |
| `Nat.one_lt_iff_ne_one.mp h` | `h.ne'` | for `h : 1 < n` |
| `Nat.coprime_self_add_one n` | `Nat.coprime_self_add_right.mpr (Nat.coprime_one_right n)` | no direct replacement lemma found |
| `Nat.divisors_prime` / `Nat.divisors_prime_eq` | `Nat.Prime.divisors` | `divisors p = {1, p}` (NumberTheory/Divisors.lean:416); `Nat.divisors_prime_pow` unchanged |
| `Finset.exists_smaller_set s i h` | `Finset.exists_subset_card_eq h` | s, i now implicit |
| `Nat.pos_pow_of_pos n h` | `Nat.pow_pos h` | or `positivity` in simp positions |
| `Nat.not_eq_zero_of_lt h` | `h.ne'` | for `h : a < b` gives `b ≠ 0` |
| `not_mem_erase` | `notMem_erase` | notMem wave (§1c) |
| `Complex.abs` | **compat shim** | removed from Mathlib (norm `‖·‖` everywhere). 14 affected files got `noncomputable def Complex.abs (z : ℂ) : ℝ := ‖z‖` + umbrella import; `Complex.abs_apply z` restorable as `Complex.norm_def z`; `Complex.sq_abs`→`Complex.sq_norm`, `Complex.abs_exp`→`Complex.norm_exp`, `Complex.abs.nonneg`→`norm_nonneg`, `Complex.abs.sum_le`→`norm_sum_le` |
| `atTop` / `EuclideanSpace` unknown-const | umbrella `import Mathlib` | contents moved out of the imported modules (Order.Filter.Basic / InnerProductSpace.Basic); §3 class |

Left unresolved for Doctor (#38065): `Nat.nth_prime_strictMono`/`nth_prime_zero`/`Nat.Prime.nthPrime` (v4.31 only has `Nat.nth_prime_zero_eq_two`-style numerals), `GeometricSeriesOQ03` (`Complex.abs_cpow_mul_exp_log_re` removed, needs proof rework), `ChebyshevPNTBridgeOQ01` (PartENat removal), `Nat.find`/`Fintype`/`Finset.univ`-style unknown-consts (likely deeper/never-compiled), `Real.*`/`Ordinal.*` singletons, project-local unknown names (`white_lower`, `fan_lower`, `halasz_theorem`, …).

## Summary counts

- **Confident mappings (§1):** 48 pairs (incl. 6 notMem-wave + 4 sdiff-wave entries), of which 8 also need API-level attention (§5).
- **Needs verification (§2):** 19 entries.
- **Import-only fixes (§3):** 10 constants.
- **Pre-existing / out-of-scope (§4):** 10+ names + project-local cascade noise — keep out of the rename batch.
- **Top clusters by affected files:** AbelRuffini/Galois (`IsSolvableByRad`+`isSolvable'`+`isSimpleGroup_five`, ~22 files), `le_or_lt` (16), `Complex.abs` (11, pre-existing), `Finset.toSet` (9), `div_le_div_iff`/`div_lt_div_iff` (≈9), `ZMod.natCast_zmod_eq_zero_iff_dvd` (8).

**Unresolved (could not map):** `Nat.choose_two_middle`, `MeasureTheory.Measure.restrict_prod_eq_prod_restrict`, `Finset.sum_sort`, `Nat.factorial_le_factorial`, `ciSup_empty`, `Nat.coprime_iff_disjoint` — all single-file; resolve during the batch with `exact?`/loogle.

*Re-harvest procedure:* the inventory is still running; rerun the extraction one-liners in this file's git history (deprecation-pair grep + unknown-constant grep over `proofs/spike-logs-full/shard-*/**.log`) before finalizing #38064's batch list.

## 7. Doctor-batch recipes (#38065, discovered 2026-07-12)

### 7a. Classical decidability loss (biggest instance-synth recipe)
Defs using `Finset.filter` / `Nat.find` / `if-then-else` / `Finset.sup` / graph
`degree`/`neighborFinset` over undecidable predicates no longer synthesize
`Decidable`/`DecidablePred`/`DecidableEq`/`Fintype` instances on v4.31.
**Recipe:** insert `open scoped Classical` after the import block
(`proofs/batch2/add_open_classical.py <modules.txt>`), then run the wave and feed
the diag through `proofs/batch2/fix_noncomputable.py <diag files>` — the classical
instances make flagged defs noncomputable, and the compiler names each def that
now needs the `noncomputable` keyword ("failed to compile definition / not
supported by code generator"). Two-pass; both scripts idempotent. Validated:
Erdos860/600/270/440/725/886/554/716 + ~140 swept.

### 7b. `Subgroup.normalizer` now takes `Set G`
`def normalizer (S : Set G) : Subgroup G` (Algebra/Group/Subgroup/Defs.lean:668) —
`H.normalizer` dot-notation on a `Subgroup` fails ("does not have a usable
parameter"). **Recipe:** `H.normalizer` → `Subgroup.normalizer H` (coercion is
automatic in argument position); wrap when projections follow:
`P.normalizer.index` → `(Subgroup.normalizer P).index`. Lemma names
(`mem_normalizer_iff`, `le_normalizer`, `normalizer_eq_top_iff`) unchanged.

### 7c. `SimpleGraph` fields are now `Std.Symm` / `Std.Irrefl` wrappers
`structure SimpleGraph … symm : Std.Symm Adj; loopless : Std.Irrefl Adj`.
- Use sites: `G.symm h` → `h.symm` (via `SimpleGraph.Adj.symm`, Basic.lean:169).
- Structure-instance sites: `symm x y h := …` → `symm.symm x y h := …`,
  `loopless x h := …` → `loopless.irrefl x h := …` (nested-field syntax, cf.
  Mathlib's own `supSet` instance).

### 7d. Misc verified renames/removals (Doctor batch)
| old | new | notes |
|---|---|---|
| `NormedSpace.exp 𝕂 x` | `NormedSpace.exp x` | 𝕂 parameter dropped; `exp_eq_tsum (𝔸 := _)` |
| `Equiv.Perm.apply_inv_self` | `Equiv.Perm.inv_def` + `Equiv.apply_symm_apply` | rw/simp chains; or `show … (Equiv.symm σ x) …` |
| `List.maximum?` | `List.max?` | |
| `List.bind` | `List.flatMap` | |
| `List.get? l n` | `l[n]?` | |
| `Nat.choose_three_right` | REMOVED | derive via `Nat.descFactorial_eq_factorial_mul_choose n 3` + `descFactorial_succ` rewrites (BirthdayProblemOQ01 pattern) |
| `Nat.totient_pos h` | `Nat.totient_pos.mpr h` | now an iff |
| `Set.ncard_biUnion` | `Set.Finite.ncard_biUnion` | RHS is now `∑ᶠ` (finsum) — proof rework, not a rename |
| `Set.piecewise_eq_of_not_mem` | `Set.piecewise_eq_of_notMem` | notMem wave |
| `proofIrrel` | `Subsingleton.elim` | |
| `Real.logb` unknown | umbrella `import Mathlib` | import loss |
| `tendsto_integral_of_dominated_convergence` unknown | umbrella `import Mathlib` | import loss (Integral.DominatedConvergence) |
| σ (divisor function) notation | `open scoped ArithmeticFunction.sigma` | moved to sub-locale (Misc.lean:147) |
| ω (Ordinal) notation | `open Ordinal` (+ `Ordinal.omega0`) | scoped notation, Basic.lean:813 |
| 𝓝 notation | `open scoped Topology` | |
| `IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ)` synth | UNRESOLVED | instance `[CharZero K]` exists (Cyclotomic/Basic.lean:702) yet synthesis fails in project files (InverseGalois, AngleTrisectionEmbedding) — needs in-container debugging |

### 7e. Parse/elaboration drift (Doctor batch)
- `λ` can no longer be a *binder/identifier name* (`(λ : ℝ)`) — rename to `lam`.
- `prefix`/`suffix` are reserved tokens — rename binders (`pre`/`suf`).
- doc-comment directly before `open … in def` hard-errors — move `open … in`
  above the doc-comment.
- doc-comment before `variable` hard-errors — demote to `/- … -/`.
- `{f x | x : T, p x}` set-builder comma form — use `{f x | (x : T) (_ : p x)}`.
- multi-line term continuation after `by <tac> …` at lower indent breaks —
  join lines or restructure.
- `decide` on `Nat.Prime` of 3-digit numbers hits maxRecDepth —
  `set_option maxRecDepth 40000`.
- `Set.ncard_le_ncard` autoparam `toFinite_tac` weaker — pass finiteness
  explicitly (`(Set.finite_Iio y).subset fun u hu => hu.1` pattern).
- `natDegree`-of-explicit-polynomial `norm_num` sets drift — `compute_degree!`.
- structure-field `where` defs with removed doc-comment support: `-/` inside
  docstring prose (`field-/module`) terminates the comment — spell `field/module`.

### 7f. Doctor increment-2 recipes (#38065, 2026-07-12)
| pattern | fix | notes |
|---|---|---|
| `G.symm h` use-site (SimpleGraph) | `G.adj_symm h` | arity-preserving; `SimpleGraph.adj_symm` Basic.lean:166 |
| `G.loopless v` use-site | `G.loopless.irrefl v` | `Std.Irrefl.irrefl : ∀ a, ¬r a a` explicit binder |
| `symm := fun/by …` structure field | `symm.symm := …` / `loopless.irrefl := …` | nested-field syntax; skip already-migrated `:= by constructor` lines |
| `<tac> made no progress` (simp/dsimp/field_simp/push_neg) | replace call with `skip` | semantics-preserving on v4.31 — state was unchanged; surfaces true downstream error when the call was a finisher (`batch2/dr7_noprogress.py`) |
| bulk `lake build` timeout in runner | chunked bulk (25 targets, `-j4`) + `pkill -9 lean` per chunk | orphaned lean children of a killed lake starve the sequential recheck (`batch2/runner4.sh`) |
| `Finset.card_Icc` (ℕ) | `Nat.card_Icc` | Order/Interval/Finset/Nat.lean:61 |
| `Finset.card_offDiag` | `Finset.offDiag_card` | |
| `Finset.eq_empty_of_forall_not_mem` | `…_notMem` | notMem wave, also `Set.` |
| `inv_le_inv_of_le` | `inv_anti₀` | same arg order (0 < b, b ≤ a) |
| `Int.natAbs_ofNat` | `Int.natAbs_natCast` | deprecated alias removed in core |
| `pow_lt_pow_right` | `pow_lt_pow_right₀` | ₀-family rename |
| `Nat.nth_prime_zero` | `Nat.nth_prime_zero_eq_two` | numeral forms only in v4.31 |
| `sigma_isMultiplicative` | `isMultiplicative_sigma` | ArithmeticFunction |
| `Nat.le_pow_iff_clog_le hb` | `← Nat.clog_le_iff_le_pow hb` (rw) / swap `.mp`↔`.mpr` (term) | iff sides swapped |
| `NormedSpace.exp_eq_tsum (𝔸 := _)` | add `(𝕂 := ℝ)` | 𝕂 now `variable (𝕂) in`-explicit with `[CharZero 𝕂]`; bare `NormedSpace.exp ℝ x` → `NormedSpace.exp x` |
| bare `exact Option.noConfusion` (goal `some _ ≠ none`) | `exact (Option.some_ne_none _)` | eta-form of noConfusion no longer elaborates; APPLIED form `Option.noConfusion h` still fine |
| `{ inferInstanceAs (CommRing R) with … }` instance literal | `where __ := inferInstanceAs (CommRing R)` | v4.31 structure-instance elaborator rejects `{ src with }` here ("expected structure" + `?m.1` metavars); ZsqrtdNegTwo EuclideanDomain pattern |
| `simpa [id, zero_sub] using (hasDerivAt_const p 1).sub (hasDerivAt_id p)` | `exact (hasDerivAt_id p).const_sub 1` | simp-normal-form drift on HasDerivAt algebra |
| `simpa using hdvd` after `Fintype.card_perm` rewrites | `simpa [Nat.factorial] using hdvd` | simp no longer evaluates `n !` numerals |
| "Invalid field `X`: environment does not contain `Finset.card`/`Finset.sum`/…" | umbrella `import Mathlib` | import-loss masquerading as dot-notation-drift |
| `xs.get! i` | `xs[i]!` | List.get! removed |

### 7g. Doctor increment-5 recipes (#38065, 2026-07-13)
| pattern | fix | notes |
|---|---|---|
| `IsSplittingField ℚ f.SplittingField f` / `Normal ℚ f.SplittingField` fail to synthesize | re-register ℚ-specialized local instances: `instance (f : ℚ[X]) : IsSplittingField ℚ f.SplittingField f := Polynomial.IsSplittingField.splittingField f` (and `Polynomial.SplittingField.instNormal f`) | same family as the cyclotomic `[CharZero K]` synthesis regression; explicit application works, synthesis does not |
| `IsAlgClosed ℂ` fails to synthesize | `import Mathlib.Analysis.Complex.Polynomial.Basic` (the FTA instance `Complex.isAlgClosed` is no longer transitively imported in curated-import files) | check the file's import list before adding compat instances |
| `AdjoinRoot.liftHom` unknown | `AdjoinRoot.liftAlgHom p (Algebra.ofId _ _) x h` | RingTheory/AdjoinRoot.lean:307 |
| `IsSolvableByRad F α` / `solvableByRad.isSolvable'` | `α ∈ solvableByRad F E` / `isSolvable_gal_of_irreducible` | FieldTheory/AbelRuffini.lean:332 |
| `List.mem_cons_self a l` applied | bare `List.mem_cons_self` | args now implicit |
| `Nat.coprime_two_left.mpr h` with `h : n % 2 = 1` | `Nat.coprime_two_left.mpr (Nat.odd_iff.mpr h)` | RHS is now `Odd n` |
| `(hcop.gcd_mul_left_cancel m).symm` type mismatch | drop `.symm` | v4.31 gives `gcd (k*m) n = gcd m n` directly |
| `termination_by a + b` on point-free `def f : ℕ → ℕ → ℕ \| a, b => …` | `termination_by a b => a + b` | match-arm names no longer in scope |
| cross-module use of `private theorem` | de-privatize in the defining file | v4.31 enforces module-scoped privacy (e.g. `ed_crt_sufficient`) |
| `rcases List.mem_cons.mp hp with rfl \| h` head-branch names | substitution direction flipped: the *cons-binder* name (`pair`) is eliminated, keep the element name (`p`) | "Unknown identifier" in head branch only |
| local `notation … " ≍ " …` ambiguous | add `(priority := high)` | `≍` is core `HEq` notation now |
| `Finset.eq_empty_of_forall_not_mem` | `Finset.eq_empty_of_forall_notMem` | notMem wave |
| `Nat.Prime.mod_four_ne_three_of_dvd_isSquare_neg_one` | `Nat.mod_four_ne_three_of_mem_primeFactors_of_isSquare_neg_one` | NumberTheory/SumTwoSquares.lean:95; takes `p ∈ n.primeFactors` |
| `Int.gcd_dvd_left`/`right` (bare `exact`) | apply explicitly: `Int.gcd_dvd_left a b` | implicits became explicit |
| `Int.dvd_gcd ha hb` (c : ℤ) | `Int.natAbs_dvd.mp (Int.natCast_dvd_natCast.mpr (Nat.dvd_gcd (Int.natAbs_dvd_natAbs.mpr ha) (Int.natAbs_dvd_natAbs.mpr hb)))` | signature drifted to NatCast'd divisor |
| `decide` on WF-recursive `def` value (e.g. `binaryGcdInt 12 18 = 6`) | rewrite to a kernel-reducible form first (`rw [binaryGcdInt_eq_intGcd]; decide`) | WF defs never kernel-reduce |
| `rw [h]` where `h : a = (a-b)+b` rewrites ALL `a` occurrences (incl. inside `a-b`) | `have h3 : … ∣ (a-b)+b := dvd_add h1 h2; rwa [Nat.sub_add_cancel hle] at h3` | v4.26 goals displayed `a+1`/`succ` uniformly, masking this |
| `simpa using Nat.size_pos.mpr h` expecting `1 ≤ n.size` | `have h1 : 0 < n.size := …; simp only [Nat.zero_div, Nat.size_zero]; omega` | simpa no longer bridges `0 <` ↝ `1 ≤` |
| `simpa only […] using isUnit_iff_ne_zero` (Finset.map units embedding) | `simp only […]` + `constructor` + `rintro ⟨u, rfl⟩; exact u.ne_zero` / `intro hx; exact ⟨Units.mk0 x hx, rfl⟩` | IsUnit ∃-unfold no longer defeq-matched |
| duplicate-decl fails after a hub starts compiling | check whether the "self-contained extraction" file re-declares content its (now-fixed) import provides; delete the duplicated block | SpernerGridCell vs SpernerGridBase |
| stale-diag zero-edit flips | RESIDUAL rows whose freshest diag attributes all errors to now-GREEN files: re-verify without edits | DR15b: 12/16 PASS |

### 7h. Doctor increment-5A recipes (type-mismatch class, #38065, 2026-07-13)

| pattern | fix | notes |
|---|---|---|
| `Real.rpow_add hx.ne'` | `Real.rpow_add hx` | arg is `0 < x` again, not `x ≠ 0` |
| `MvPolynomial.psum_eq_mul_esymm_sub_sum σ R 1 one_ne_zero` | `… one_pos` | hypothesis is now `0 < n` |
| element-form `le_add_left a b : a ≤ b + a` | `self_le_add_left a b` | `le_add_left` is now proof→proof |
| `add_le_add_right h c` elaborating to `c + a ≤ c + b` | `add_le_add h le_rfl` / `add_le_add le_rfl h` | Cardinal call sites |
| numeral dot-call `4.choose 2` | `(4).choose 2` / `Nat.choose 4 2` | "unexpected identifier after decimal point" |
| `f ∘ g` vs `fun y => f (g y)` after simp | add `Function.comp_def` to the simp set, or `simp only [Function.comp_def] at h; exact h` | Tendsto/HasDerivAt families; goal-side bare `def` name is defeq — plain `exact` often lands where `simpa` fails |
| `IsMulCommutative.toCommutative` missing | keep the `IsMulCommutative` value, use `.comm a b` directly | Std.Commutative middleman removed |
| `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le hε_pos` | pass `(Metric.ball_mem_nhds _ hε_pos)`; named `(ε := …)` args are gone | first arg is now `s ∈ 𝓝 t` |
| `Nat.choose_descFactorial` / `Nat.factorial_mul_descFactorial` | orientation/operand order changed — patch with `.symm` / `mul_comm`-rewrites per the found/expected types | ArithmeticSeries family |
| `rw [lemma]` where pattern has `?α - 1` vs concrete `r` | `have h := lemma … (r + 1); rw [add_sub_cancel_right] at h; rw [h]` | rw unification got stricter |
| `(2:ℝ) - 1` vs `1` inside proof-carrying dependent args | `have h := …; convert h using ‹n›; norm_num` | convert closes proof args by proof irrelevance |
| `simp [hf0] at hf; exact … hf` → "No goals to be solved" | drop the trailing `exact` — `simp at hf` now closes the goal | contradiction-closing simp |
| `content_dvd_coeff q` (polynomial arg) | `q.content_dvd_coeff n` | index arg is `ℕ` |
| `solvableByRad.isSolvable'` | `Polynomial.isSolvable_gal_of_irreducible` | deprecation warning names it; `IsSolvableByRad F x` → `x ∈ solvableByRad F E` |
### 7i. Doctor increment-5B recipes (#38065, 2026-07-13, proof-drift)

| pattern | fix | notes |
|---|---|---|
| `convert X using N` + trailing `ring`/`norm_num` | `convert X using N <;> (first \| rfl \| ring1 \| (push_cast; ring1) \| (field_simp; ring1) \| (norm_num; done))` | v4.31 convert surfaces instance-congruence goals (`instAddCommMonoid = ...`); rfl closes them. ~50 sites, Basel/Buffons/Circumference/GeometricSeries/Pythagorean families |
| `ring` / `norm_num` inside `first` | `ring1` / `(norm_num; done)` | v4.31 `ring` falls back to ring_nf and SUCCEEDS on progress without closing — commits the alternative, strands the goal |
| omega "counterexample may satisfy b >= 0" with beta-redex goals | `beta_reduce; omega` | v4.31 omega does not beta-reduce `(fun n => ...) i` |
| omega after `unfold f` with `f`-mentioning hypotheses | drop unfold, `le_trans` on folded spelling | goal/hypothesis atom split |
| "No goals to be solved" | delete the dead tactic (line or `; tail`) | 85 sites swept; single-pass bottom-up per diag only |
| `Odd.mod_cast_eq` | `Nat.odd_iff.mp` | removed |
| `Finset.eq_empty_of_forall_not_mem` | `..._notMem` | notMem wave (also Finset.card_insert_of_not_mem earlier) |
| `Finset.Ico_succ_right` | REMOVED — use `Nat.card_Icc` for card goals | only `Ico_succ_right_eq_insert_Ico` survives |
| `List.headI_mem_self`, `List.headI_take_one` | REMOVED — `cases l` + simp | |
| `List.get?` field-projection (`l.get? i`) | `l[i]?` | core removal, batch entry confirmed for dot-notation form |
| `set x := e` + `simp [defs]` / `cases x` | add `x` to the simp set (`simp [x, defs]`); avoid `cases` on set-vars | v4.31 set-vars are not unfolded by simp lemma sets alone (BallotProblemOQ01OQ04OQ01, partially repaired) |
| `(k := 1)`-style numeral instantiation + `simp only [h]` misses | add `Nat.cast_one`/`one_mul` to the simp set | cast-literal mismatch `-(1:N):Z` vs `-1` |
| `decide` on 3-digit `Nat.Prime` conjunctions | file-level `set_option maxRecDepth 100000` | SophieGermainOQ01 x15 |
| `decide` on bounded-forall prime facts | `intro n h1 h2; interval_cases n <;> norm_num` | Erdos1059OQ03 |
| `simp [catalan]; norm_num` numerals | `decide` | norm_num no longer evaluates `Nat.choose` residuals |
| D4/Fin-board `ext <;> simp <;> omega` case bashes | `revert s; fin_cases k <;> cases b <;> decide` | KnightsTourOblique + OQ02 |
| `G.symm h` (project-local SimpleGraph) | `G.adj_symm h` | confirms 7f, KnightsTourObliqueOQ02Reverse |
| `div_lt_div_right (h : 0 < c)` iff-form | `div_lt_div_iff_of_pos_right (h : 0 < c)` | confirms 1b correction |

**Infrastructure (5B):** virtiofs serves STALE (truncated) file content to running
containers after host edits on /Volumes/Stripe worktrees — `docker restart <c>`
before building (see STATUS.md "increment 5B verification-infrastructure notes";
also covers the runner5 false-mtime-FAIL pitfall).

### 7k. Doctor increment-6 recipes (#38065, 2026-07-13, instance-synth: cyclotomic cluster)

**ROOT CAUSE of the 48-row InverseGalois*/AngleTrisection* cyclotomic mystery**
(finally solved): `DivisionRing.toRatAlgebra : Algebra ℚ R` at default priority
wins `Algebra ℚ K` synthesis over the structure-canonical algebra instances
(`SplittingField.instAlgebra`, `CyclotomicField.instAlgebra`,
`IntermediateField.algebra'`, …). The chosen instance is defeq to the canonical
one only at **default transparency**, so every class keyed on the canonical
algebra (`Normal`, `IsSplittingField`, `IsGalois`, `IsCyclotomicExtension`,
quotient `Mul`/`Group`, `Module.Free`) fails to synthesize while explicit
application succeeds — the exact "instance exists yet synth fails, explicit
application works" symptom flagged unresolved since increment 1.

| pattern | fix | notes |
|---|---|---|
| `Normal/IsSplittingField/IsGalois/IsCyclotomicExtension ℚ …` synth fails, explicit application works | `attribute [instance 10] DivisionRing.toRatAlgebra` after imports | THE cyclotomic-cluster root fix; demotes the ℚ-algebra instance below structure-canonical ones. Flipped 4/10 roots outright |
| `Module.Free ℚ ↥F` / big cyclotomic tower `(deterministic) timeout at typeclass (20000 heartbeats)` | `set_option synthInstance.maxHeartbeats 80000` (file-level) | pairs with the demotion; InverseGaloisD4/D4OQ02 |
| `H.Normal` / `Mul (Gal(…) ⧸ H)` synth fails after demotion, `H : Subgroup (…).Gal` | re-register at the `≃ₐ` spelling: `haveI : @Subgroup.Normal (L ≃ₐ[ℚ] L) AlgEquiv.aut H := ‹H.Normal›` | `Polynomial.Gal` = `SplittingField ≃ₐ[ℚ] SplittingField` via `deriving Group`; the two group spellings are not reducibly-equal keys |
| redundant `haveI := fK; haveI := aK; …` re-registering `obtain`ed class hypotheses | **delete them** | obtained class hypotheses are already local instances; re-registering via `haveI :=` creates divergent instance keys that break downstream synthesis (InverseGaloisOQ03) |
| `solvableByRad.isSolvable' hirr hα h` (deprecated inductive `IsSolvableByRad`) | membership bridge: `induction h` → `α ∈ solvableByRad F E`, then `isSolvable_gal_of_irreducible hmem hirr hα` (hyps `clear`ed before induction; arg order is membership-first) | AbelRuffini `isSolvable'` alias reordered args |
| `open scoped` element commutator: `⁅a,b⁆` `failed to synthesize Bracket G G` | `open scoped commutatorElement` | `commutatorElement` is now a scoped instance (Algebra/Group/Commutator.lean) |
| `s3/s4 solvable` via `decide`/`native_decide` on `derivedSeries … = ⊥` | group-theoretic proof: sign-kernel `solvable_of_ker_le_range` + `alternatingGroup.kleinFour` API + prime-card `isCyclic_of_prime_card` helper | v4.31 lost the `Decidable (derivedSeries … = ⊥)` instances |
| `FaithfulSMul (subgroup) (F)` on a `MulSemiringAction.compHom … subtype` action | pin the SMul key: `@FaithfulSMul _ _ (altAction n).toDistribMulAction.toMulAction.toSMul where …` | subgroup-restriction SMul is defeq but not reducibly to the header's synthesized one |
| `simpa using hdvd` after `Fintype.card_perm` (goal `_ ∣ 24`, hdvd `_ ∣ 4!`) | `simpa [Nat.factorial] using hdvd` | confirms 7f; norm_num/simp no longer evaluates `n!` |
| `convert X using 1` leaves an associativity gap (`a*(b*c*d) ∈ P` vs `a*b*c*d ∈ P`) | `have h : a*b*c*d = a*(b*c*d) := by group; rw [h]; exact X` | v4.31 convert stricter; InverseGaloisA5/AbelRuffiniOQ04OQ01 |
| `commutator_eq_bot_iff_center_eq_top.mp` — Unknown constant | route via `Subgroup.commutator_eq_bot_iff_le_centralizer.mp` + `mem_centralizer_iff` | lemma absent from pinned oleans |
| `Subgroup.index_mul_card` on `Fintype.card` goal | `rw [← Nat.card_eq_fintype_card, …, Subgroup.index_mul_card]` | lemma is now `Nat.card`-stated |
| `DihedralGroup.noConfusion hx` motive-inference failure | `simp only [DihedralGroup.one_def, reduceCtorEq] at hx` | bare `noConfusion` can't infer motive |
| `dirichletUnitTheorem.w₀ K` (explicit K) | drop K — `w₀` binder is now implicit (`variable {K}`) | Kronecker/Stark |
| well-founded `def f` no longer `rfl`-transparent (`halvings 0 = 0 := rfl` fails) | equation lemmas: `by simp [f]` for base, `by conv_lhs => rw [f]` for step | AngleTrisectionOQ03OQ02 |
| Decidable-**valued** `theorem foo : Decidable P` "not a proposition" | change `theorem` → `def` | Decidable instances/definitions must be `def` |
| `Nat.log_pow (h : 1 < b)` "expected `log 2 (2^k)=k`, got `∀ x, …`" | pass the explicit exponent: `Nat.log_pow h k` | |
| `set x := e … rw [hx_def]`/`simp only [hx_def]` "no occurrence" (set-vars) | prove membership by term-level `Finset.mem_filter.mpr ⟨…⟩`; `rw [hS_def]` right before an `ext`; add the set-var to the simp set | v4.31 set-vars opaque to simp/rw lemma sets (confirms 5B) |
| `natDegree` of explicit polynomial via `norm_num [natDegree_*]` | `compute_degree!` | confirms 7e |
| leftover `T_k(cos)` transfer ℚ→ℝ→ℂ hits `whnf` heartbeat blowup | stay in ℂ: `Chebyshev.aeval_T` + `Complex.ofReal_cos` + `Chebyshev.T_complex_cos` | AngleTrisectionOQ02OQ03OQ01 |
| `ring` treats `x^(k+1)`, `x^(k+2)` as independent zpow atoms | rewrite all to the single atom `x^(k:ℤ)` via `zpow_add_one₀` first, then `field_simp; ring` | |

**All ℚ-field-extension gallery files** (Galois theory, cyclotomic, splitting
fields, number fields) should carry `attribute [instance 10] DivisionRing.toRatAlgebra`
after imports on v4.31 — this is the single highest-yield instance-synth fix.

### 7j. Doctor increment-7 recipes (#38065, 2026-07-13, tm+pd remainder)

| pattern | fix | notes |
|---|---|---|
| `Finset.single_le_sum` + `mem_range.mpr` proof via `Nat.lt_succ_of_le` | pass `(f := fun j => ...)` explicitly | `range r.succ` vs `range (r+1)` unification no longer resolves the sum metavar (BinomialTheoremOQ04) |
| `X.trans (by simp ...)` where X's implicits come from the trans result | `have h : <explicit type> := by simp ...; exact X.trans h` | by-blocks now elaborate before trans metavars are solved — "Fintype ?m stuck" / "simp made no progress" (Erdos1161) |
| `Nat.sum_digits_lt` | REMOVED — `rw [Nat.digits_def' hb hn]; have := Nat.digit_sum_le b (n/b); simp only [List.sum_cons]; omega` | strict digit-sum bound gone; only `Nat.digit_sum_le` survives |
| nlinarith on `g * lcm = X * g * g` cancellations | `Nat.eq_of_mul_eq_mul_left hpos (by rw [h]; ring)` + `Nat.le_mul_of_pos_right` | var-product cancellation loss (ChineseRemainderNonCoprimeOQ01) |
| `decide` on `Squarefree <numeral>` | `(by norm_num : Nat.Prime p).squarefree` (or factor via primes) | instDecidablePredSquarefree runs WF `minSqFac` — never kernel-reduces |
| `(Nat.modEq_iff_dvd' h).mpr hdvd` expected `a ≡ 1` | append `.symm` | orientation now `1 ≡ a [MOD p]` (Erdos820Aristotle) |
| `∀ k ≥ 1, (1:ℚ) + 1/k ∈ S` binder | annotate `∀ k : ℕ, k ≥ 1 → ...` | ℕ/ℚ binder-inference drift, ∃/∀-bounded form (Erdos419; same family as 5A's ℕ/ℝ finding) |
| `simp [h1]` with `h1 : x ∈ ({a} : Set α)` | `simp only [Set.mem_singleton_iff] at h1; simp [h1]` | membership hypotheses no longer usable directly as simp rewrites |
| `modByMonic_add_div p hq` | `modByMonic_add_div p q` | Monic hypothesis dropped, pass the divisor polynomial (batch15) |
| `n ! - 1` | `(n !) - 1` | `! -` juxtaposition now parses as `n (!-1)` (batch15, CramersRule) |
| `theorem foo : Decidable P := ...` | `def foo ...` | theorems may not return non-Prop data (batch24, KonigsbergOQ04) |
| `Σ x, P x` with P : Prop | `Σ' x, P x` | Sigma over Prop rejected (batch24) |
| dot-notation `X.baz` for cross-namespace `def Foo.Bar.baz` | declare as `_root_.Foo.Bar.baz` or qualify | v4.31 dot-notation no longer resolves cross-namespace defs (batch24, Konigsberg) |
| `Nat.card_eq_fintypeCard` | `Nat.card_eq_fintype_card` | snake_case — batch08's Lagrange patch failed on the camelCase guess |
| `SimpleGraph.Walk.rotate w` | `d.rotate w hwd` (vertex-membership arg now explicit) | batch24 Splice |
| `List.prod_ne_zero h` | now takes `0 ∉ l` | batch24 Kummer |
| kabstract/rw proof-irrelevance loss (patterns with proof args / set-vars) | refold via `rw [show lhs = rhs from rfl]`, defeq-recast `have h' : <folded> := h`; never `simp at h` when other hyps depend on h — copy first | batch15 Ballot family |
| statement repairs (operator policy 2026-07-13) | fix false statements to intended-true form; never vacuous, never sorry | see STATUS.md increment-7 statement-repairs table (7 files) |

### 7l. Doctor increment-9 recipes (#38065, 2026-07-13, rewrite-drift + tm/pd remainder)

| v4.31 symptom | fix | source |
|---|---|---|
| `rw [h]` fails to find pattern hidden in a **let-bound structure literal's projections** (`cfg.d` with `cfg := {d := t, …}`) | `subst h` (or `simp only [structField]`) to reduce projections BEFORE rewriting | CevasTheorem |
| `2 * ?m / 2` (Nat.mul_div_cancel_left) no longer matches after `pow_succ` | use `pow_succ'` (gives `a * a^k`, not `a^k * a`) | AngleTrisectionOQ02OQ03Ext, CollatzCyclesOQ04 |
| `Nat.totient_pos (h)` — now an Iff | `Nat.totient_pos.mpr h` | AngleTrisection/Erdos417/EulerTotient family |
| `List.scanl` no longer unfolds under simp/rw (defined via `scanlM`) | `List.scanl_cons` / `List.scanl_nil` | Erdos1054 |
| `ring`/`rpow_natCast` no longer bridge `π^(2:ℝ)` (rpow) ↔ `π^2` (npow) | insert targeted `π^(k:ℝ) = π^k` conversions; keep `show (2:ℝ)=…` rewrites TARGETED (a blanket one also hits the `2` in `1/2`) | BuffonsNeedle |
| SimpleGraph field-assignment `symm.symm :=` / `loopless.irrefl :=` invalid | plain `symm :=` / `loopless :=` | Erdos1018 |
| `nth_rewrite 1 [← Nat.mod_add_div …]` picks wrong occurrence | `conv_lhs => rw [← …]` | QuadraticReciprocityAlgorithmOQ03M2 |
| `theorem` whose conclusion is a **function type** (data, not Prop) rejected | change keyword to `def` | Erdos688 sieve_duality |
| `→` now binds tighter than `↔` in a mixed `∀ n, P → Q ↔ R` statement | parenthesize the intended grouping `∀ n, P → (Q ↔ R)` | Erdos207 |
### 7l. Doctor increment-8 recipes (#38065, 2026-07-13, unknown-const class)

**Meta-finding:** the umbrella `import Mathlib` backfill from earlier increments
already ran — a zero-edit re-verify of all 347 unknown-const rows flipped only 1.
The rest are TRUE removals/renames (Mathlib) or project-local name drift.

| unknown-const | v4.31 replacement | notes |
|---|---|---|
| `le_of_not_le` | `le_of_not_ge` | identical sig `¬a≤b → b≤a` (Order/Defs/LinearOrder) |
| `summable_of_summable_norm` | `Summable.of_norm` | |
| `NormedRing.summable_geometric_of_norm_lt_one T h` | `summable_geometric_of_norm_lt_one h` (ROOT ns, but `x` explicit) | moved to root + `HasSummableGeomSeries` |
| `NormedRing.tsum_geometric_of_norm_lt_one T h` | `tsum_geometric_of_norm_lt_one h` | ROOT ns, `ξ` IMPLICIT — DROP the explicit arg |
| `Nat.catalan` | `catalan` | moved to root (Combinatorics/Enumerative/Catalan/Basic) |
| `Nat.succ_mul_catalan_eq n` | `succ_mul_catalan_eq_centralBinom n` | renamed w/ `_centralBinom` suffix; `(n+1)*catalan n = centralBinom n` |
| `Nat.numDerangements` | `numDerangements` | moved to root (Combinatorics/Derangements/Finite) |
| `Nat.Even` / `Nat.Odd` | `Even` / `Odd` (root typeclass, `@Even (α:=ℕ)` for #check) | |
| `finrank` (bare) | `Module.finrank` | bare finrank moved into Module ns; ×9 rows (most also have other errors) |
| `Function.id` | `id` | (bare `id`) |
| `HasSubset.Subset.rfl` | `subset_rfl` | `HasSubset.Subset.trans` → `subset_trans`/`Subset.trans` |
| `Finsupp.not_mem_support_iff` | `Finsupp.notMem_support_iff` | notMem wave (also `DFinsupp.`) |
| `Finset.erase_eq_of_not_mem` | `Finset.erase_eq_of_notMem` | notMem wave |
| `Finset.insert_subset.mpr` | `Finset.insert_subset_iff.mpr` | bare `Finset.insert_subset` (direct-application form) still exists — only the iff `.mpr` moved |
| `Finset.sum_card_fiberwise_eq_card` | `Finset.card_eq_sum_card_fiberwise` | name reversed |
| `Finset.exists_lt_card_fiber_of_nsmul_lt_card` | `Fintype.exists_lt_card_fiber_of_nsmul_lt_card` | in `namespace Fintype`, not `Finset` |
| `Nat.div_mul_cancel_of_dvd h` | `Nat.mul_div_cancel' h` | `gcd * (n/gcd) = n` shape (`a * (b/a) = b`) |
| `Nat.pow_lt_pow_left_iff h` | `Nat.pow_lt_pow_iff_right h` | `a^m < a^n ↔ m<n` given `1<a` |
| `Nat.one_lt_iff_ne_one` (on ℕ) | fails synth as generic `one_lt_iff_ne_one` (IsBotOne) — use ℕ-direct: `not_le.mp h` for `1<n` from `¬n≤1` | |
| `SimpleGraph.not_adj_bot u v` | `(SimpleGraph.bot_adj u v).mp` (`Adj → False` = `¬Adj`) | `bot_adj v w : (⊥).Adj v w ↔ False` |
| `SimpleGraph.mem_neighborFinset.mpr h` | `by rw [SimpleGraph.mem_neighborFinset]; exact h` (dot-form `G.mem_neighborFinset a` mis-resolves `G` as explicit `w` arg → Function.mpr error) | `mem_neighborFinset (w:V)` — only `w` explicit |
| `SimpleGraph.adj_mk` (in `simp only [graphDef, adj_mk]`) | drop it — `simp only [graphDef]` already unfolds the `where`-built `.Adj` field | |
| `measurableSet_generateFrom` | `MeasurableSpace.measurableSet_generateFrom` | in `namespace MeasurableSpace` |
| `pow_eq_zero h` (`a^2=0 → a=0`) | `(pow_eq_zero_iff two_ne_zero).mp h` | bare `pow_eq_zero` gone |
| `Real.sqrt_eq_iff_sq_eq` (as norm_num/simp lemma) | drop it (norm_num closes without); or `Real.sqrt_sq`/`Real.sqrt_eq_iff_eq_sq` for the direct spelling | orientation changed |
| `summable_pow_div_factorial` | `Real.summable_pow_div_factorial` | namespace |
| `hasSum_compl_iff` | `hasSum_iff_hasSum_compl` | renamed |
| `Dvd.dvd.symm` (REMOVED bogus alias) | STATEMENT REPAIR — dvd isn't symmetric; the proof was wrong. Fix the term, don't rename | Erdos1196 (see STATUS.md inc-8 repair) |

**Triage rule that worked:** classify each unknown-const row by whether its OWN
file has errors OTHER than the unknown-const. Pure-uc rows (0 other own errors)
flip from the rename alone; MIXED rows (uc + rewrite/omega/simp drift) need the
full per-file repair and belong to the type-mismatch/proof-drift passes — a
speculative rename there won't flip the row, so revert it (keep the tree clean).

### 7m. Doctor increment-10 recipes (#38065, 2026-07-13, tm/pd + mixed remainder)

**Meta-finding:** zero-edit re-verify of all 792 type-mismatch(223)+proof-drift(246)
+unknown-const(323) RESIDUAL rows flipped 0 — the dependency backfill already
ran (matches inc-8). 706 are own-only (self-contained), 86 dep-masked, only 13
distinct dep hubs (BallotProblemOQ03OQ02 ×7, SpernerSimplicialInstance ×5,
BallotProblemOQ01OQ02OQ01 ×4).

| pattern | fix | notes |
|---|---|---|
| `Finset.map ⟨(· + 1), by omega⟩` / `by intro; omega` map-injectivity | `by intro a b h; simpa using h` | omega no longer beta-reduces `(· + 1) a` — the injectivity hyp `(·+1) a = (·+1) b` is an unreduced redex omega abstracts to opaque atoms (Erdos534/702). HIGH-FREQ. |
| injective `(fun _ _ h => by omega)` for `fun k => a + k*d` | `intro x y h; simp only [add_right_inj] at h; exact Nat.eq_of_mul_eq_mul_right hd h` | omega can't cancel the `k*d` var-product; need explicit mult-cancel with `d>0` in scope (Erdos71) |
| `simp only [Nat.succ_eq_add_one] at *` before omega | when induction gives `Nat.succ k` but hyps use `k+1` | atom split blocks omega (Erdos342 ulamSeq_ge) |
| `by omega` proving False from `Finset.le_sup … : id n ≤ M` + `M < n` | `by simp only [id_eq]; omega` | `id n` is an opaque atom ≠ `n` for omega (Erdos28) |
| decimal-literal `norm_num` regression: `0.247 - 0.22936 = 0.01764` leaves `⊢ … = 1764e-5` | ascribe `:ℝ` + `norm_num [show (0.247:ℝ)=247/1000 from by norm_num, …]` per literal | norm_num reduces the RHS to scientific `OfScientific` form but won't close the equation; `norm_num1` also fails without the denominator rewrites (Erdos232) |
| `field_simp` leaves `Real.pi = √Real.pi ^ 2`, `ring` fails | `rw [Real.sq_sqrt Real.pi_pos.le]` | sqrt² needs the explicit lemma, not ring (Erdos1124) |
| `simp [h_2]` leaves `4 / 2^2 = 1` (ℚ) | append `norm_num` | simp no longer finishes rational numerals (Erdos336) |
| `simp only [Fin.prod_univ_two]` won't fire on `∏ i : Fin p.degree, …` (structure-projection degree) | `show ∏ i : Fin 2, (z - ![…] i) = …; simp [Fin.prod_univ_two]` (delete now-dead `ring`) | `p.degree` doesn't reduce to the literal `2` for simp-lemma matching; a `show` forces it. `rw [Fin.prod_univ_two]` ALSO fails ("pattern `∏ i, ?f i` not found") — use non-`only` `simp` (Erdos1040) |
| anonymous `‹h > 0›` binder in an `axiom`/def statement "assumption failed ⊢ h>0" | name the binder: `∀ h:ℝ, ∀ hh:h>0, …` and reference `hh` | v4.31 anonymous-hypothesis resolution changed inside `∀ h, h>0 → …` (Erdos173) |
| after binder rename, `push_neg` yields `∀ T', … → ¬…` but hyp is `¬∃ T', … ∧ …` | wrap: `fun T' hc hm => hNotMono ⟨T', hc, hm⟩` | v4.31 push_neg normal-form differs from the stored `¬∃` (Erdos173) |
| `nlinarith` can't use a `d ≥ 3` (ℕ) fact over ℝ | add `have h3 : (3:ℝ) ≤ d := by exact_mod_cast hd` to the hint list | the ℕ hypothesis isn't auto-cast into nlinarith's real hint pool (Erdos1083) |
| `interval_cases k` "could not find upper bound" for `p^k = N` | derive `p ∣ N` (→ `p ≤ N`) and `k ≤ log_p N` (via `2^(K+1) > N`) as explicit `have`s FIRST, then `interval_cases p <;> interval_cases k <;> revert … <;> decide` | v4.31 interval_cases won't infer a bound from a `pow` equation (Erdos435 ¬IsPrimePower 6) |
| `Real.log_nonneg (by norm_num)` needs `1 ≤ ↑n + 2` with variable `n` | `by have := Nat.cast_nonneg (α:=ℝ) n; push_cast; linarith` | norm_num can't discharge a cast-variable bound (Erdos605 decreasing_by) |
| missing `have hkd_pos : 0 < k^d` present in a sibling theorem | re-add via `pow_pos _hk d` | migration dropped the `have`; the underscore-named `_hk : 0 < k` still usable (Erdos681) |

**Statement repairs (operator policy):**
| file | declaration | repair |
|---|---|---|
| Erdos450Problem | `hasDivisorIn_succ` | hypothesis `1 ≤ n` → `2 ≤ n`: at n=1 the witness d=n+1=2 fails `d < 2n = 2`; the true statement needs n≥2 |
| Erdos542Problem | `chen_bound_value` | RHS `2927/4620` numerically wrong → `4699/4620` (1/3+1/4+1/5+1/7+1/11 = (1540+1155+924+660+420)/4620) |

### 7n. Doctor increment-12 recipes (#38065, 2026-07-13, parse-error + sig/elab/dot drift)

**Meta-finding:** zero-edit re-verify of all 197 parse/signature/elab/dot rows
flipped 1 (backfill already ran, matches inc-8/9/10). Parse fix is
NECESSARY-BUT-NOT-SUFFICIENT on many rows — unblocking the parser surfaces a
deeper type-mismatch / instance-synth / omega error underneath that belongs to
another class. Only sole-blocker parse rows flip; revert the rest to keep the
tree clean (the parse edit is correct but the row can't go GREEN yet).

| v4.31 parse symptom | fix | notes |
|---|---|---|
| `/-- doc -/` immediately before `open/omit/unseal/set_option/variable … in <decl>` — `unexpected token '<mod>'; expected 'lemma'` | move the `<mod> … in` line ABOVE the doc-comment's opening `/--` | confirms 7e; sweep script `batch2/sweep_modifier_in.py` handles all sites per file (balance-counts the doc block, reinserts above the opener). Erdos345/Maschke/Minkowski(×2)/Feuerbach(×2)/Erdos666 |
| `/-- doc -/` before a NON-decl (`#check`, `variable`, `/-!`) — `unexpected token 'X'; expected 'lemma'` | demote the orphan `/--` to `/-` | Hilbert9Reciprocity, StirlingFormula, DirichletsTheorem (×2 #check), Erdos577 (before `variable`) |
| `(r λ : ℝ)` / `λ_target` / `λ'` / `x*` binder — reserved char in identifier | rename to `lam` / `lam_target` / `lamp` / `xstar` (code lines only — leave prose `λ` in `--`/`/- -/` comments) | py block-comment-aware sweep; AreaOfCircle/Erdos642/474/515/1167, Brouwer |
| `abbrev ℝ² := …` / `abbrev ℤ√neg2 := …` — reserved char STARTING a decl name (`ℝ`, `ℤ√`) | rename the decl throughout the file (`ℝ²`→`EuclidPlane`, `ℤ√neg2`→`Zneg2`) | whole-file token sed; Erdos97 (17×), BezoutIdentity (26×) — but both had deeper own errors, did not flip |
| set-builder `{f x \| x : T, p x}` where the image `f x` is a PROJECTION (`S.card`) | rewrite to explicit comprehension `{k \| ∃ x : T, p x ∧ f x = k}` — the `{img \| (x)(_ : p)}` binder form FAILS with "invalid binder name `S.card`, it must be atomic" | Erdos535 flipped; Erdos801/256/1115/1086 had deeper own errors |
| set-builder subtype form `{f S \| S : T // p S}` | same explicit-comprehension rewrite | `//` no longer parses in set-builder; Erdos1086 |
| `∀ a b c d ∈ A, …` multi-binder-with-`∈` | split: `∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, …` | confirms Batch-3; Erdos795Aristotle flipped |
| `a : ℝ; b : ℝ; c : ℝ` — `;`-separated fields on one structure-field line | split each field to its own line (`;` no longer separates struct fields) | LawOfCosinesOQ03OQ02 (had deeper `rw … at t.proj` error, didn't flip) |
| nested `/-` literal inside a `/- … -/` block comment | remove/reword the literal `/-` (block comments nest — an inner `/-` needs an extra `-/`) → "unterminated comment" at EOF | SumOfOddsStatementOnly flipped |
| `theorem foo (…) : := by sorry` with the intended type on the NEXT line | move the type up: `theorem foo (…) :\n    <type> := by sorry` (statement repair — see STATUS.md) | Erdos220ProblemProvable flipped (3 sites) |
| `symm := by constructor; intro …; cases h <;> (…) <|> (…)` SimpleGraph field | rewrite as a plain multi-line `by`: `constructor; intro i j h; rcases h with h\|h; · exact Or.inr h; · exact Or.inl h` (avoid `<;>`/`<|>` precedence in the field) | Erdos552 (loopless field then hit proof-drift `simp` no-progress, didn't flip) |
| `∆` (symmetric difference) — `expected token` | `open scoped symmDiff` after imports (notation is now `scoped[symmDiff]`) | Erdos431 flipped; Erdos1123 hit deeper `Set.symmDiff_comm` unknown |
| `p \| q` where `\|` means divides | `p ∣ q` (`∣` U+2223, not ASCII pipe) | Erdos490Aristotle (had deeper omega drift, didn't flip) |
| `∂` measure-integral / `⟪_,_⟫` inner-product notation — `expected token` | `open MeasureTheory` / `open scoped RealInnerProductSpace` (notation-scope loss, §7d family) | EgorovTheorem, LebesgueMeasureOQ03 (deeper, not swept) |

### 7o. Doctor increment-13 recipes (#38065, 2026-07-13, type-mismatch + proof-drift + rewrite-drift remainder)

| v4.31 symptom | fix | source |
|---|---|---|
| `iSup_le`/`iSup₂_le` on `⨆ z, ⨆ _, (f z : ℝ) ≤ a` → "typeclass instance problem is stuck" | `Real.iSup_le (fun i => …) (0 ≤ a)`, nested for double sups — ℝ is conditionally complete, not a `CompleteLattice`, so `iSup_le` doesn't apply | Erdos230ProblemAristotle |
| Fin-bound `by omega` inside `∃ a b, P ∧ Q ⟨…, proof-needing-P⟩` — omega can't see the conjunct `P` at binder position | rewrite to dependent existential `∃ a b, ∃ hP : P, Q ⟨…, hP⟩` (same logical content) | Erdos532; also `Nat.mod_lt _ i.pos` for `Fin cycle.length` (Erdos883) |
| `rw [h]` "motive is not type correct" where `h`'s LHS/RHS appears in a dependent type (`D : Decomposition S t x`, `σ : Perm (Fin 5)`) | rewrite the OTHER operand first (`rw [← map_sum]; exact congrArg f h`), or `have := lemma; rwa [order_fact] at this` — never `rw` a literal that also indexes a `Fin n`/structure param | ShapleyFolkmanOQ01, InverseGaloisF20OQ02 |
| `Option.noConfusion h` (`h : none = some _`) motive-inference failure | `exact absurd h (by simp)` | SpernerNDimOQ06, PNPBarriersSound (sibling of §7k Dihedral noConfusion) |
| `simpa using (hasDerivAt_cos x).neg` — `-cos` elaborated via wrong module instance (`RCLike.toInnerProductSpaceReal.toModule` vs `Semiring.toModule`) | build the `HasDerivAt` with the explicit derivative value: `have h0 : HasDerivAt (fun x => -f x) (-(-f' x)) x := (hasDerivAt … ).neg; rwa [neg_neg] at h0` | TaylorTheoremOQ03OQ02 |
| `taylor_mean_remainder_lagrange_iteratedDeriv hx` — first arg was `0 < x`, now `x₀ ≠ x`; result set is `uIcc`/`uIoo` not `Icc`/`Ioo` | pass `hx.ne` (for `x₀=0`: `0 ≠ x`), and bridge `Set.uIcc 0 x = Icc 0 x` via `Set.uIcc_of_le hx.le` + `uIoo` via `min/max_eq` | TaylorTheoremOQ03OQ01 |
| `Subgroup.normalizer (P : Subgroup G)` — now takes `Set G` | `Subgroup.normalizer ((P : Subgroup G) : Set G)` (`normalizer_eq_top_iff` still Subgroup-Normal-valued) | SylowTheoremOQ02OQ01Nilpotent (confirms §7b) |
| `mul_lt_mul_of_pos_left _ hd` on goal `d * e < d` (no `* 1` on RHS) | `mul_lt_of_lt_one_right hd` (needs `e < 1`); then `rw [exp_lt_one_iff, neg_lt_zero]` for `exp(neg) < 1` | YangMills2DOQ01 |
| `Nat.fib 3` / `Nat.totient` literals no longer reduce under `simpa` (mono-lemma gives `fib 3 ≤ fib m`, want `2 ≤ fib m`) | `have h3 : Nat.fib 3 = 2 := by decide; rwa [h3] at this` | FibonacciIdentitiesOQ02 (×2), Erdos821 (`constructor <;> decide` for totient) |
| exhaustive `Fin N` `def … | ⟨0,_⟩ => … | ⟨N-1,_⟩ => …` → "Missing cases: Fin.mk (…N…)" | add out-of-range arm `| ⟨n + N, h⟩ => absurd h (by omega)` | Erdos758Problem |
| `Nat.find ⟨witness, by trivial⟩` where the predicate is a metavariable (`?m (Fintype.card V)`) or the witness makes the pred FALSE | annotate the predicate `Nat.find (p := fun k => ∃ …) ⟨…⟩` AND supply a genuinely-true witness (constant coloring isn't proper — use `Fintype.equivFin V` injective); add `open Classical in` for `DecidablePred` | Erdos760Problem (chromaticNumber), Erdos774 (n+1 card bound) |
| anonymous `‹_›` proof inside a set-builder conjunction `{s | ∃ S, (∀ n∈S, n∈A ∧ c ⟨n,‹_›⟩=…) ∧ …}` | thread via dependent existential `∃ hn : n ∈ A, c ⟨n, hn⟩ = …` | Erdos54Problem (sibling of §7m Erdos173 anon-binder) |
| `rw [hinter, hPin]` where `hPin : P = foo P` re-substitutes P inside `foo` (self-referential nesting) | rewrite backward `rw [hinter, ← hPin]` to collapse `foo P → P` | FeuerbachsTheoremOQ04TangentLine |
| conditionally-completed `positivity` fails on `1 + x^2 ≠ 0` (needs strict, gets ≠0) | `have : (0:ℝ) < 1 + x^2 := by positivity; exact this.ne'` | LeibnizPiOQ03 |
| `mean_value_inequality hh hC` fails to unify `deriv (f-g)` with the supplied value `deriv f - deriv g` | apply the underlying Mathlib lemma directly with an explicit `(f' := fun y => deriv f y - deriv g y)`: `norm_image_sub_le_of_norm_deriv_le_segment' (f' := …) hh hC` | MeanValueTheoremOQ03 |
| `Complex.norm_le_norm_of_mapsTo_ball_self hd hmaps …` — `hmaps` now needs `MapsTo f ball closedBall` | `hmaps.mono_right Metric.ball_subset_closedBall` | Hilbert22OQ01OQ03Pseudohyperbolic |
| `(conj U M).charpoly` vs `charpoly_units_conj` giving `(↑U*M*(↑U)⁻¹)` and `↑U⁻¹`/`(↑U)⁻¹` mismatch | `rw [conj_apply, Matrix.coe_units_inv U]` (unit-inv-cast → matrix-inv-of-cast) | CramersRuleOQ05OQ02 |
| `flip Inc x y` opaque after `Finset.sum_comm` | add `Function.flip_def` to the `simp only` set | IncidenceCauchySchwarzDual |
| `(Equiv.symm 1)` / `(iso (iso.symm v))` not simplified | `Equiv.Perm.one_symm` (qualified!) / `RelIso.apply_symm_apply` | FourSquareDistributionOQ01, SpernerTuckerEndpointTransport |
| omega counterexample missing a product/mod atom: `syl(m+1)-1 = product`, `product = t+t` unlinked; `syl m.succ` vs `syl (m+1)` split | `rw [ht] at hsub` (substitute product) + `simp only [Nat.succ_eq_add_one]` before omega | SylvesterSequenceOQ01OQ03 (confirms §7m succ split) |
| `Nat.card_Icc`/`Nat.card_range` needed before omega for `card (Icc 1 (sqrt n)) ≤ sqrt n` | `rw [Nat.card_Icc]; omega` | Erdos1060Problem |
| `Int.ModEq` goal `¬ (r+1) ≡ r [ZMOD m]` where omega can't model `% m` (variable modulus) | case-split `Nat.lt_or_ge (r+1) m`, prove each `(r+1)%m` value via `Int.emod_eq_of_lt`/`Int.emod_self` | Erdos8OQ02 |

**Meta-finding (confirms inc-8/9/10/12):** the dependency backfill already ran —
these are genuine per-file v4.31 repairs. The 76 single-own-error files across
type-mismatch/proof-drift/rewrite-drift are the highest-confidence one-edit bucket;
~40 flipped cleanly this session. Virtiofs truncation ("unexpected end of input",
`Unknown identifier CramersRuleOQ0`) recurs on /Volumes/Stripe worktrees after host
edits — `docker restart dr23` before rebuild.
### 7o. Doctor increment-11 recipes (#38065, 2026-07-13, instance-synth: rpow/graph/list/totality)

**Meta-finding:** the `instance-synth` class is NOT one root cause — it is a
grab-bag. The dominant *first* synth failure buckets across the Erdős rows:
rpow import-loss (`HPow ℝ ℝ`/`HPow ℕ ℝ`), graph `Fintype (G.neighborSet v)`/
`Fintype G.edgeSet`, and classical `DecidablePred`. But most files carry
**downstream cascade errors** revealed only once the synth failure is cleared,
so the true fix per file is: apply the mechanical synth fix FIRST, then repair
the exposed cascade (type-mismatch / proof-drift / statement bug). Zero rows
flipped on synth-fix alone; every GREEN needed 1–8 follow-up edits.

| pattern | fix | notes |
|---|---|---|
| `(n:ℝ)^(1/2:ℝ)` etc `failed to synthesize HPow ℝ ℝ ?m` in curated-import file | `import Mathlib.Analysis.SpecialFunctions.Pow.Real` | rpow import-loss; ONLY helps curated-import files — an `import Mathlib` umbrella file failing `HPow ℝ ℝ` is a genuine metavar, not this |
| `n^(1+c)` with bare `n:ℕ`, exponent `ℝ` → `HPow ℕ ℝ ?m` | coerce base `(n:ℝ)^(1+c)`; ascribe negative/fractional literal exponents `(-7/4 : ℝ)` (`Neg ℕ` synth failure otherwise) | Erdos808 |
| `Fintype ↑(G.neighborSet v)` / `Fintype ↑G.edgeSet` / `G.degree`/`edgeFinset` synth | `open scoped Classical` after imports; then two-pass `fix_noncomputable.py` for the flagged `def`s (§7a) | works only for FINITE carriers (`SimpleGraph (Fin n)`/`[Fintype V]`); over `SimpleGraph ℕ` the count is genuinely ill-typed (statement bug) |
| `H.degree v` still `Fintype ↑(H.neighborSet v)` after classical | add `[DecidableRel H.Adj]` to the def's binders | classical `propDecidable` is not registered as `DecidableRel`; explicit instance arg pins it (Erdos146 MaxDegreeOneSide) |
| `def OrderingPattern k := Equiv.Perm (Fin k)` then `pattern i` "Function expected"/`Fintype` synth fail | `abbrev` instead of `def` | a `def` wrapper hides the `Perm` FunLike/`Fintype` instances; `abbrev` keeps them transparent (Erdos415) |
| `⟨k - 1 - i.val, by omega⟩ : Fin k` / `(i+1)%m` bound `by omega` "counterexample" | `by have := i.isLt; omega` / `Nat.mod_lt _ (by omega)` | v4.31 omega does not pull `Fin` bounds from `i` automatically |
| anonymous `∀ i, i < len → … .get ⟨i, by omega⟩` inner `by omega` can't see the `→` hyp | name it: `∀ i, (hi : i < len) → … .get ⟨i, hi⟩` and use `hi` (+ `Nat.mod_lt _ (by omega)` for the `%`) | the anonymous hypothesis is not in the metavariable context of the index proof (Erdos767/584) |
| `List.head!` / `List.getLast!` "failed to synthesize Inhabited (Fin n)" | rewrite to `Option`-valued `head?`/`getLast?`: `∃ a ∈ l.head?, ∃ b ∈ l.getLast?, …` | `Fin n` is not `Inhabited` for `n=0`; the bang-forms need it (Erdos584 IsCycle) |
| `cycle.get? i` field | `cycle[i]?` | confirms core `List.get?` removal (Erdos767) |
| `⟦(a, b)⟧ : Sym2 W` quotient-mk notation | `s(a, b)` | v4.31 Sym2 element spelling (Erdos565) |
| `Subset.rfl` / `mem_singleton` "Ambiguous term" (Set vs Finset) | qualify `Finset.Subset.rfl` / `Finset.mem_singleton` | `open scoped Classical` (or Set+Finset opens) surfaces both interpretations (Erdos777) |
| `G.IsBipartite` / `G.IsCycle n` "environment does not contain SimpleGraph.IsBipartite/IsCycle" | `G.Colorable 2` (needs `import …SimpleGraph.Coloring`); a length-`n` cycle → `∃ v (w : G.Walk v v), w.IsCycle ∧ w.length = n` | not Mathlib API; project-local pseudo-fields (Erdos146/630) |
| `G.Walk V V` (carrier type as vertex args) | `⨅ (v : V) (c : G.Walk v v) …` | `Walk` is vertex-indexed; girth quantifies base vertex (Erdos548) |
| `def Foo : Prop := … Type* …` then reused in another def "universe level metavariables …{?u}" | pin the internal quantifier to `Type` (or `Type 0`) | a `Type*` quantifier inside a `Prop` def leaves an uninferable universe when applied in a *second* def body; self-contained uses are fine (Erdos628 TihanyForPair/548 ErdosSosConjecture) |
| `def foo : Prop := … k …` "Unknown identifier k" | add the missing binder `∀ (k : ℕ), …` at the front | v4.31 will not autobound an implicit inside a `def : Prop` body (Erdos548 ErdosSosConjecture) |
| `theorem foo : sorry := by sorry` "type … is not a proposition" | give the statement a real proposition (∃-witness form of the illustrated claim, or the intended inequality) — never `True` (vacuous) | v4.31 rejects a `sorry` in *type* position; v4.26 defaulted it to `Prop` (Erdos612 path/cycle/bipartite/moore) |
| `Finset.inf'`/`min'`/`max'` "failed to synthesize `univ.Nonempty`"/`Nonempty V` | make total: `max'`→`(Finset.univ.image f).sup id`; `min'`→`(…).min.getD 0`; or `inf'` over a family with a conditional witness → `(family.image f).min.getD 0` | v4.31 needs the nonempty witness for *every* parameter; an `∅`-witness that only lies in the family for some hypothesis (`0 ≤ C`) is not universally valid — switch to a total `min/sup`-based def with the empty→0 convention (Erdos613/612/784) |
| `0 : Fin k` "failed to synthesize OfNat (Fin k) 0" | add `[NeZero k]` to the def | the numeral needs a nonempty carrier (Erdos147 minDegree) |
| `native_decide` "depends on 'F'/'largestPrimeFactor', which is 'noncomputable'" | DROP a *spurious* `noncomputable` — `Finset.max'`/`primeFactors` ARE computable | defensively-added `noncomputable` breaks the compiler-eval path native_decide needs; if the body is genuinely computable, remove the keyword (Erdos368) |
| `x |>.card ≥ k` "has type ℕ but expected Prop" | parenthesise: `(x).card ≥ k` | the `|>.card ≥ k` pipe mis-associates on v4.31 (Erdos415 phi_collisions) |
| `⟨X, L_little_o_x, X⟩` third slot "has type NamedProp but expected ∀ε>0,…" (defeq fold) | annotate the target `∀ ε > 0` binder as `∀ ε : ℝ, ε > 0 →` to match the named def | ℕ/ℝ binder-inference drift makes the unfolded target's `ε` a different type than the named lemma's `ε:ℝ` (Erdos437) |
| `struct SimpleGraph … where symm := by constructor; …` | nested-field `symm.symm := by …` / `loopless.irrefl := by …` (drop `constructor`); watch And-component order (`⟨h.1, h.2⟩` not `⟨h.2, h.1⟩` after the intro flips) | confirms §7c; Erdos548/548Aristotle/146/637 |
| `G.symm h` / `G.loopless v` use-site (project SimpleGraph) | `G.adj_symm h` / `G.loopless.irrefl v` | confirms §7f (Erdos637/548) |

**Statement repairs (operator policy):**
| file | declaration | repair |
|---|---|---|
| Erdos1024Problem | `exists_independent` | added hypothesis `(hne : ∅ ∉ H)` — the empty set is independent iff H has no empty edge (else `∅ ⊆ ∅` is a contained edge) |
| Erdos437Problem | `erdos_437_summary` | `∀ ε > 0` binders annotated `∀ ε : ℝ, ε > 0 →` (were ℕ-inferred) to match `erdos437Conjecture` |
| Erdos630Problem | `bipartite_iff_no_odd_cycle` | `G.IsCycle n` (not API) → `∃ v (w : G.Walk v v), w.IsCycle ∧ w.length = n` |
| Erdos548Problem | `ErdosSosConjecture` | added missing `∀ (k : ℕ)` binder; `girth` over `G.Walk v v` not `G.Walk V V` |
| Erdos808Problem | `SumProductConjecture` | `A.image (fun p => p.1 + p.2)` over `A : Finset ℕ` (elements aren't pairs) → `(A ×ˢ A).image …` |
| Erdos415Problem | `Question3_NaturalMostLikely` | `Finset.univ.filter` over `m : ℕ` (needs `Fintype ℕ`) → `(Finset.range (n+1)).filter` |
| Erdos612Problem | `path/cycle/bipartite/moore` | `sorry`-typed statements replaced with real ∃-graph / Moore-bound propositions |
| Erdos777Problem | `full_comparable` | `Or.inr hA` (base ⊆ A) was wrong for `hA : A ⊆ base` → `Or.inl hA` |

### 7p. Doctor increment-15 recipes (#38065, 2026-07-13, tm/pd/rewrite + unknown-const-mixed)

| v4.31 symptom | fix | source |
|---|---|---|
| `theorem foo` used at line N but *defined* at line M > N in the same file → "Unknown identifier `foo`" | move the lemma above its first use (no hoisting in v4.31); **delete the orphaned doc-comment** left where it was, else "unexpected `/-!` … expected 'lemma'" | Erdos731Problem (choose_succ_gt_central) |
| term-mode `(by norm_num)` proving `0 < 3` in a **type-ascription argument slot** → "unknown tactic" | `by decide` | SpernerSimplicialInstanceOQ05 |
| `Nat.cast_sub h : ↑(a-1) = ↑a - ↑1` but goal wants `↑a - 1` (literal) | chase with `Nat.cast_one`: `rw [Nat.cast_sub h, Nat.cast_one]` | NewtonInductiveStepOQ01 |
| `ext x` on `s = ∅` (Finset/Set) leaves an `Iff`, so `intro`/`introN` fails | `simp only [Finset.notMem_empty, iff_false]` before `intro` (note `not_mem`→`notMem` rename) | SzemerediCoreOQ01 |
| `attribute [local instance] Real.fact_zero_lt_one` — constant removed | `local instance : Fact ((0:ℝ) < 1) := ⟨one_pos⟩` | DirichletApproximationOQ02 |
| `MeasureTheory.Measure.prod_mono h1 h2` removed | local lemma: `Measure.le_iff.mpr (fun s hs => by rw [Measure.prod_apply hs, Measure.prod_apply hs]; exact (lintegral_mono (fun x => hν (Prod.mk x ⁻¹' s))).trans (lintegral_mono' hμ le_rfl))` | GreensTheoremOQ01OQ01OQ03 |
| `show ((i:ℕ) : Fin (m+1)) = i` for `ZMod (m+1) = Fin (m+1)` round-trip no longer elaborates | `ZMod.natCast_rightInverse (n := m+1) i` (pin the modulus) | BoundedPrimeGapsOQ04OQ01 |
| `padicValNat.factorial_le_factorial hp hmn` removed | `rw [← Nat.factorization_def _ hp, ← Nat.factorization_def _ hp]; exact (Nat.factorization_le_iff_dvd (factorial_ne_zero _) (factorial_ne_zero _)).mpr (Nat.factorial_dvd_factorial hmn) p` | Erdos912Problem |
| omega treats `Nat.count Nat.Prime k` and `Nat.count (fun p => Nat.Prime p) k` (from `Nat.lt_nth_iff_count_lt.mp`) as **distinct atoms** (eta) | `simp only [show (fun p => Nat.Prime p) = Nat.Prime from rfl]` before `omega` — general eta-atom bridge | Erdos853Problem |
| `apply add_le_add_left` fails on goal `a + b ≤ a + c` — now unifies as right-mono `?b+?a ≤ ?c+?a` | `gcongr a + ?_` | Erdos572Problem |
| `Nat.card_le_one` removed | `rcases isEmpty_or_nonempty X with h|h; · simp; · exact (Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => Subsingleton.elim a b⟩, h⟩).le` | MinkowskiTheoremOQ03 |
| `colorable_of_isEmpty _ 0` removed | `SimpleGraph.colorable_zero_iff.mpr ‹_›` (needs an `IsEmpty V` instance in scope) | Erdos736Problem |
| `G.loopless a hG` "Function expected at G.loopless" (now `Std.Irrefl G.Adj`) | `G.loopless.irrefl a hG` (confirms §7f) | Erdos736Problem |
| a `def … := ∀ (C : Type*) …` reused in a hypothesis AND a goal gives them **different universe metavars** (`@h C` universe mismatch u_2 vs u_3) | pin both uses to one explicit universe: `theorem foo.{u} … : IsKChoosable.{_, u} … → IsKChoosable.{_, u} …`; do NOT change the parent def if it is already GREEN | Erdos631ProblemAristotle |
| no-op `dsimp only` (no lemmas) → "made no progress" | delete it | SpernerSimplicialInstanceOQ04 |
| `Option.noConfusion h` (`h : none = some _`) as a **structure field value** motive failure | `absurd h (by simp)` (confirms §7o) | SpernerSimplicialInstance |
| `mem_cons_self x xs` "Function expected" | `mem_cons_self` (now nullary, both args implicit) | NewtonInductiveStepOQ02 |
| `Nat.eq_or_gt_of_le h` removed (want `a = b ∨ a < b`) | `h.eq_or_lt` (`LE.le.eq_or_lt`) | NewtonInductiveStepOQ02 |
| `getLast?.getD 0` residual after `primeFactorsList_pow` | `rw [List.getLast?_replicate]; simp [k ≠ 0]` | Erdos649Problem |
| `rcases (h : k%3 = 0 ∨ …) with rfl | …` "subst failed, k%3 not a variable" | `rcases … with h|h|h <;> rw [h] <;> decide` (can't subst a `%`) | Erdos649Problem |
| `dif_pos (by omega : a*b > 1)` with `a,b ≥ 2` (nonlinear) | `by nlinarith` | Erdos932Problem |

**Meta-finding:** for a single-error DR20a file whose error points at a SHARED
root module (e.g. 6 rows all citing `SpernerSimplicialInstance.lean:1018`), the
root fix flips only the rows with no own errors; the rest were **dep-masked** and
surface their real per-file errors once the root compiles — build each dependent
separately. The eta-atom omega split and the anonymous-`∀ i, (hi : …) →` binder
naming (§7o) are the two most frequently-recurring proof-drift shapes this session.
### 7p. Doctor increment-14 recipes (#38065, 2026-07-13, structured classes + instance-synth tail)

**Meta-finding:** the dependency backfill already ran (zero-edit re-verify of 171
structured rows flipped 0; of 178 synth rows flipped 5 stale dep-flips). Parse /
synth fix is NECESSARY-BUT-NOT-SUFFICIENT on the majority — unblocking surfaces a
deeper tm/pd class underneath; only sole-blocker rows flip. High-confidence
one-edit fixes = the SINGLE-own-error-line rows (19 of the 178 synth rows).

| v4.31 symptom | fix | notes |
|---|---|---|
| set-builder `{f x \| x : T, p x}` with image `f x` a PROJECTION/app | `{k \| ∃ x : T, p x ∧ f x = k}` (also `//` subtype form) | confirms §7n; Erdos256/801/1086/1115 |
| `\|f z\|` where `f z : ℂ` — `failed to synthesize Lattice ℂ` | `Complex.abs (f z)` (the file's compat shim), NOT the lattice `\|·\|` | Erdos256/1115 (both carry a `def Complex.abs := ‖·‖` shim) |
| `⟪e₁, e₂⟫_ℝ` (with `_𝕜` suffix) `expected token` | `open scoped InnerProductSpace` (NOT `RealInnerProductSpace` — that gives the *un-suffixed* `⟪x,y⟫`) | scoped[InnerProductSpace] for `⟪·,·⟫_𝕜`; LebesgueMeasureOQ03 |
| `inner_self_eq_norm_mul_norm` "stuck InnerProductSpace ?m H" over ℝ | `real_inner_self_eq_norm_mul_norm` (𝕜 pinned) | the general form leaves 𝕜 metavar |
| `∫ x, f x ∂μ` notation `expected token` | `import Mathlib.MeasureTheory.Integral.Bochner.Basic` | top-level `notation3`, not scoped — curated-import files miss it despite `open MeasureTheory`. `Integral.SetIntegral`→`Integral.Bochner.Set` |
| `ℝ≥0∞` `expected token` in curated-import file | `open scoped ENNReal` | notation-scope loss |
| `Finset.min'`/`max'` "Nonempty univ" over a possibly-empty carrier | `(image f).min.getD 0` totality (empty→0 convention) | §7o; Erdos577/914; the old `⟨(image).choose …, choose_mem⟩` nonempty-witness construction is also broken (`Finset.Nonempty.image` sig drift) |
| `Nat.totient_prime hp` (was `hp.totient`) | root `Nat.totient_prime hp : φ p = p-1` | `Irreducible.totient`/`Nat.Prime.totient` gone |
| `(x : ℝ).toNat` — `Real.toNat` gone | `⌊(x : ℝ)⌋₊` (Nat.floor) + mark the def `noncomputable` | Erdos718/718 |
| project `G.edist`/`G.dist` (SimpleGraph) `Invalid field dist` | `import Mathlib.Combinatorics.SimpleGraph.Metric`; `G.dist : ℕ`, `G.edist : ℕ∞` — coerce `(G.dist u v : ℕ∞)` for a `⊤`-fallback def | Erdos742 |
| SimpleGraph structure fields `symm x y h :=` / `symm.symm :=` / `loopless.irrefl :=` | `symm := ⟨fun _ _ h => …⟩` / `loopless := ⟨fun _ h => …⟩` (fields are now `Std.Symm Adj` / `Std.Irrefl Adj`, take explicit binders inside `⟨⟩`); use-sites `G.adj_symm` / `G.loopless.irrefl` | Erdos508/582/742 |
| `Nat.find (G.colorable_of_fintype)` (Colorable, not ∃) | `Nat.find (⟨_, G.colorable_of_fintype⟩ : ∃ n, G.Colorable n)`; `Colorable_of_fintype`→lowercase `colorable_of_fintype` | Erdos917 |
| `Finset.Pairwise` field removed | `(↑S : Set α).Pairwise` | TestApi783 |
| `List.enum` removed | `List.zipIdx` — **swaps tuple order** `(idx, elem)`→`(elem, idx)`, so `⟨i, a⟩`→`⟨a, i⟩` | TestApi342 |
| `σ` (ArithmeticFunction.sigma) `Function expected` | `open scoped ArithmeticFunction.sigma` (scope split off `ArithmeticFunction`) | TestApi826 |
| `MetrizableSpace X` `Function expected` | `TopologicalSpace.MetrizableSpace X` (+ `import …Topology.Metrizable.Basic`) | Erdos909 |
| `IsBounded s` `Function expected` (umbrella file) | `Bornology.IsBounded s` | Erdos1048 |
| `EuclideanSpace`/`chromaticNumber` etc `Function expected` (curated imports) | the metavar name is an unimported constant — add the import (`…InnerProductSpace.EuclideanDist`, `…SimpleGraph.Coloring.Vertex`) | Erdos508/626; `chromaticNumber` is now `G.chromaticNumber : ℕ∞`, coerce comparands `(k:ℕ∞)` |
| `zero_le α` (Ordinal) / `zero_le X` (ENNReal) `Function expected at zero_le` | `bot_le` (Ordinal) / `pos_iff_ne_zero.mpr h` (ENNReal `0 < X` from `X ≠ 0`) — the ambient `zero_le` became nullary `0 ≤ ?m` | Cantor…/CauchySchwarz… |
| `/-!` module-docstring BEFORE the `import` block — `invalid 'import' command` | change the leading `/-!`→`/-` (module docstrings are commands, cannot precede imports) | Erdos287/FundamentalTheoremCalculusLebesgueOQ04/PtolemysTheoremOQ01Incomplete01 |
| `List.Sorted r` (general relation) | `l.SortedLT` / `l.SortedLE` (split by relation; the polymorphic `Sorted` is gone) | Erdos287/FundamentalArithmetic |
| `def foo : Prop := … ∀ (V : Type*) …` "contains universe level metavariables" | pin the internal quantifier `Type*`→`Type`; also pin an internal `∃ (C : Type*)` and any `Cardinal`/axiom return type to `Cardinal.{0}` | §7o; Erdos72/593/737/833 |
| ambiguous `foo` (`_root_.foo` vs `Ns.foo`) after v4.31 added a namespaced sibling | qualify to the intended one; when both typecheck-fail, the ambiguity often masks a real bug — replace with a direct proof (`ne_of_gt hn` on `n>1` → `by omega`) | Erdos824; `lowerCentralSeries` group→subgroup rework DEFERRED (39 sites) |
| `isCyclic_of_prime_card rfl` "Fact (Nat.Prime (Fintype.card G))" | lemma is now `Nat.card`-stated: `haveI : Fact (Nat.Prime (Fintype.card G)) := ⟨hp⟩; isCyclic_of_prime_card (p := Fintype.card G) (Nat.card_eq_fintype_card (α := G))` | LagrangeTheorem |
| `f.eval (m + 1)` with `m : ℕ`, `f : Polynomial ℤ` — `HAdd ℕ ℕ ℤ` | cast the arg `((m : ℤ) + 1)` | Erdos976 |
| `Nat.card (A ∩ B)` (A B : Set) — `Inter Type` | coerce to Type: `Nat.card ↑(A ∩ B)` | Erdos237 |
| `{s(a,b)}` Sym2 singleton in an `insert … {…}` chain — `Singleton (Sym2 V) ?m` (Set vs Finset) | annotate the innermost singleton `({s(a,b)} : Finset (Sym2 V))` — pins the whole chain | Erdos1009 |
| `(dif_neg h).ge` — `typeclass instance problem is stuck Preorder ?m` | `rw [dif_neg h]` (reduces `0 ≤ 0` and closes by rfl) | Erdos103 |
| `s.sum` (`s : Finset`) without the function — `AddCommMonoid ?m` stuck | `s.sum id` | Erdos862 |
| `Finset.card_filter_le _ _` metavars stuck (`DecidablePred ?m`) | `open scoped Classical` + `le_trans (Finset.card_filter_le Finset.univ _) (by simp [Finset.card_univ])` | Erdos990 |
| `List.get_mem seed 0 h0` — index sig changed | `List.get_mem seed ⟨0, h0⟩` (single `Fin` index arg) | Erdos472; `List.getElem_mem h` for the `seed[i]` form |
| `OfNat (Fin k) 0` in a def using `fun _ => 0 : α → Fin k` | add `[NeZero k]` (statement repair — `α → Fin 0` doesn't exist for nonempty α) | Erdos1022OQ01 (DEFERRED: multi-site cascade), Erdos734 (`haveI : NeZero n := ⟨by omega⟩` local from `n≥2`) |

### 7q. Doctor increment-16 recipes (#38065, 2026-07-13, structured classes + instance-synth tail)

**Meta-finding:** the instance-synth class is a dead end for the §7o one-import
rpow fix — a full scan of all 160 synth targets found ZERO curated-import
`HPow ℝ ℝ`/`HPow ℕ ℝ` candidates; every synth file is an `import Mathlib`
umbrella where the HPow failure is a genuine metavar. `open scoped Classical`
synth-fixes are necessary-but-not-sufficient on every attempted file (surfaces
deeper tm/pd/`//`/`SimpleGraph.mk` underneath). The reliable multiplier is
**dep-cascade**: fix a primary dep and its dependents auto-flip once the
sibling olean builds. +14 GREEN this increment, all from parse/elab/dot/sig
sole-blocker rows + 2 cascade flips.

| v4.31 symptom | fix | notes |
|---|---|---|
| Finset `.toSet` field — "environment does not contain `Finset.toSet`" | `(↑X : Set (elemType))` coercion (annotate the element type, e.g. `Set (Finset (Fin (n+1)))`) | AmgmInequalityOQ02Defs — resolves the inc-14 DEFERRED `.toSet` cascade |
| custom `notation:65 A " + " B => …` shadows `+`, so a def's `match` arm `\| n + 1 =>` misparses as the notation ("Invalid pattern: Expected a constructor") | use `\| Nat.succ n =>` in the match arm | Erdos337 — the redefined `+` captures the numeral-successor pattern |
| `⨆ (a b : T) (hab : P), …` multi-name binder group — "unexpected identifier; expected ')'" | split names: `⨆ (a : T) (b : T) (_ : P), …` | Erdos987; then `noncomputable` (Real.instSupSet) |
| set-builder `{expr \| True}` (a constant expression with trivial binder) | `{k \| k = expr}` | Erdos575; the `\| True` value-set form no longer parses |
| set-builder `{f z \| (z, w) ∈ S ×ˢ S}` (image app + pattern binder) | `{d \| ∃ z ∈ S, ∃ w ∈ S, f z = d}` explicit comprehension | Erdos1046 (confirms §7n) |
| `Finset.OrdConnected` field ("environment does not contain `Finset.OrdConnected`") | `(↑J : Set _).OrdConnected` — `OrdConnected` is Set-only | Erdos357 |
| `#{k \| p k}` set-cardinality notation — "unexpected token '#'; expected term" | `Nat.card {k \| p k}` | Erdos357 (×2) |
| `∀ a b c d ∈ A, …` multi-binder-with-`∈` | `∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, …` | Erdos328/795 (confirms §7n; both also needed a 2nd fix: `open scoped Classical`+noncomputable / `Real.toNat`→`⌊·⌋₊`) |
| SimpleGraph `symm.symm := <pf>` / `loopless.irrefl := <pf>` field (`:=` form) | `symm := ⟨<pf>⟩` / `loopless := ⟨<pf>⟩` (also multi-binder `symm.symm v w := by …` → `symm := ⟨fun v w => by …⟩`); use-sites `G.symm h`→`G.adj_symm h`, `G.loopless v h`→`G.loopless.irrefl v h` | SzemerediCounting FLIPPED; Erdos1031/1175/576/582/637Aristotle/RothTriangleRemoval have deeper own errors (edge_mem_edgeSet/degree_lt_card renames, Quot.toType, DecidableRel arg-name, RothTheorem dep) — field fix ready, did not flip (confirms §7p) |

### 7r. Doctor increment-17 recipes (#38065, 2026-07-13, structured remainder + deep-rework clusters)

**Cluster clears:** ThreeSubgroupsLemma `lowerCentralSeries` (39-site, #38612 item 3)
CLEARED; GeneralizeProofs vendored-block 1/3; SimpleGraph-field cluster 3/6 + RothTheorem dep.

| symptom (v4.31) | fix | notes / files |
|---|---|---|
| `lowerCentralSeries G n` "Ambiguous term" / "Unknown identifier G" (`open Subgroup`) | `Subgroup.lowerCentralSeries (⊤ : Subgroup G) n` | `lowerCentralSeries` redefined to take a `Subgroup S` (LCS of a subgroup in the ambient group); the group's series is `S = ⊤`. `Subgroup.` prefix kills the _root_-vs-Subgroup open-ambiguity. `_zero`/`_antitone`/`_succ` are now S-methods (antitone takes S explicit THEN the `a ≤ b` proof). ThreeSubgroupsLemmaOQ0101/OQ01OQ01 |
| vendored `namespace …GeneralizeProofs` referencing `Mathlib.Tactic.GeneralizeProofs` ("unknown namespace") | delete the whole vendored block; `generalize_proofs` falls back to the standard tactic (moved to `Batteries.Tactic.GeneralizeProofs`, still re-exported by Mathlib) | AmgmInequalityOQ02Aristotle FLIPPED; Erdos643/LawsOfLargeNumbers had deep own errors (sorry+timeouts / rename+aesop) — reverted. Aristotle exporter sometimes wraps the file's real `import`+tactic defs inside the header doc-comment code fence (`/- … ```lean import Mathlib … ``` … -/`) → they're commented out; re-declare them as real code (Erdos643) |
| `Cardinal.toType` "Invalid field `toType`/`Quot.toType`" | `Cardinal.out` (`c.out`) | Erdos1175 |
| `Cardinal.IsLimit` "Invalid field `IsLimit`/`Quot.IsLimit`" | `Order.IsSuccLimit c` (dot `c.IsLimit` → prefix `Order.IsSuccLimit c`) | Erdos739 |
| `Cardinal.aleph0_lt_aleph 1` "Function expected" | `Cardinal.aleph0_lt_aleph.mpr one_pos` — it is now an iff `ℵ₀ < ℵ_o ↔ 0 < o` | Erdos1175 |
| `Polynomial.modByMonic_add_div f hm` "Application type mismatch (hm : …Monic expected R[X])" | `modByMonic_add_div f <divisorPoly>` — signature is now `(p q : R[X]) : p %ₘ q + q*(p /ₘ q) = p`; pass the DIVISOR polynomial, not the Monic proof | CayleyHamiltonOQ01/OQ02 |
| `Finset.sort_sorted (· ≤ ·)` "environment does not contain" | `Finset.pairwise_sort` (gives `List.Pairwise r`; `List.Sorted r = Pairwise r`); drop `List.Sorted`/`mem_product` from any following `simp` (`List.pairwise_cons` for cons) | Erdos884 |
| `Finset.sum_eq_add_sum_diff_singleton (h : a∈s) f` "Unknown constant" | reconstruct locally: `∑ x∈s, f x = f a + ∑ x∈s\{a}, f x := by rw [← Finset.erase_eq, Finset.add_sum_erase s f h]` | RothTheorem (3 sites); the upstream lemma was removed |
| `SimpleGraph.degree_lt_card v` "environment does not contain" | `G.degree_lt_card_verts v` | Erdos637Aristotle |
| `G.edge_mem_edgeSet` "environment does not contain" | `G.mem_edgeSet` | Erdos582 |
| `Fintype`/`DecidableEq`/`DecidableRel` synth "failed to synthesize" on a wrapper `def` (`def T := Fin k → Bool`) | change `def T` → `abbrev T` (v4.31 instance resolution no longer unfolds `def`); a graph over it needs an explicit `instance : DecidableRel (graph k).Adj` | Erdos576 |
| named-instance application `foo (DecidableRel := Classical.decRel _)` "Invalid argument name" | `letI := Classical.decRel (α := V) (G : SimpleGraph V).Adj` before the goal (instance args are anonymous) | Erdos637Aristotle |
| `simp`/`convert … using 2` proof closes/nests differently: 3-field `⟨v, mem, pf⟩` → 2-field, `mem_product` unused, `convert` depth off | drop the extra field / use `Finset.mem_image.mpr ⟨x, Finset.mk_mem_product ha ha, pf⟩` / replace `convert` with explicit `Finset.filter_congr` | Erdos637Aristotle/539/576 |
| `simp [lemmas]; omega` "No goals to be solved" | drop the trailing `; omega` — simp now self-closes | Erdos324 |
| curated-import file: `norm_num`/`Real.log`/`Real.sqrt` "unknown tactic"/"Function expected" | add the missing import (`Mathlib.Tactic.NormNum`, `…SpecialFunctions.Log.Basic`, `…Sqrt`); or replace the tactic with a lemma (`one_pos` etc.) | Erdos582/91/1175 |
| universe metavar in a `Prop`-valued def ("Failed to infer universe levels" / "contains universe level metavariables") | pin internal `∀/∃ (V : Type*)`→`Type`, `κ/μ : Cardinal`→`Cardinal.{0}`, axiom/def `Cardinal` returns, and matching `variable {V : Type}` | Erdos1031/1175/474/739. **NOT pinnable** when a `Set.Iio kappa` subtype forces `Type 1` vs `α : Type 0` (Erdos598 — genuine design issue, deferred) |
| `λ'` / `∀ λ : T` binder — `λ` is a reserved token ("unexpected token 'λ'") | rename the binder (`μ`, `μ'`) | Erdos1175/474 |
| `@axiom W _ _ G` over-applied — axiom's section `[Fintype]`/`[DecidableEq]` no longer auto-included when its body doesn't use them | drop the extra `_` (or use the non-`@` `axiom G` form) | Erdos84 |
| `Nat.find ⟨…⟩` "expected type could not be determined" | give the predicate explicitly `Nat.find (p := fun m => …)` + `haveI : DecidablePred _ := Classical.decPred _` + a full-arity witness | Erdos91 |
| `∆` symmDiff "expected token" | `open scoped symmDiff` (notation is `scoped[symmDiff]`) — but this only fixes the parse; a Setoid built on it may then hit `symmDiff_comm` rename + real transitivity obligations | Erdos1123 (reverted — transitivity is a real theorem) |
| Mathlib now defines root-level `Hypergraph` (`Mathlib.Combinatorics.Hypergraph.Basic`) → "already been declared" | namespace-wrap the project file's own declarations | Erdos1020 (namespace fix ready but 10+ deeper errors — reverted) |

### 7s. Doctor increment-19 recipes (#38065, 2026-07-13, structured remainder: parse/sig/elab/dot)

**+28 GREEN.** Classes worked: parse-error, elab-drift, dot-notation-drift, plus mixed
free-flips. Per-class residual: parse-error 52→49, signature-drift 21→20, elab-drift
26→23, dot-notation-drift 12→5.

| symptom (v4.31) | fix | notes / files |
|---|---|---|
| `IsMulCommutative.comm a b` "environment does not contain `IsMulCommutative.comm`" | `.is_comm.comm a b` (`IsMulCommutative` is now a Prop-class wrapping `Std.Commutative`; the equation is `.is_comm.comm`). If a `have : Std.Commutative …` was annotated from `.quotient_commutative_iff_commutator_le.mpr`, change the annotation to `IsMulCommutative _` (the `.mpr` now returns `IsMulCommutative`, not `Std.Commutative`) | AbelRuffiniOQ06OQ01/OQ06OQ01OQ03 |
| `List.Sorted` "environment does not contain `List.Sorted`" (as a field `l.Sorted (· ≤ ·)`) | `l.SortedLE` — `Nat.primeFactorsList_sorted` etc. now return `.SortedLE`; `List.Sorted` removed (was `Pairwise`) | FundamentalArithmetic |
| `Nat.Composite` "environment does not contain" | removed upstream; express faithfully as `¬ Nat.Prime n ∧ 2 ≤ n` (decidable, `by decide`) | TestApi1059 |
| `native_decide` "failed to synthesize `Decidable (myDef …)`" when the Prop is a bounded `∀ … ∈ Finset …` behind a `def` | `by unfold myDef; native_decide` — v4.31 native_decide no longer auto-unfolds the `def` to reach the concrete `DecidablePred`; also DROP any `open scoped Classical` (its noncomputable `propDecidable` breaks native_decide) | TestApi1141 / Erdos483 (partial) |
| `HasDerivAt.div`/`.div` "Invalid field `div` … `HasFDerivAtFilter.div`" OR "Unknown constant `HasDerivAt.div`" | it EXISTS but lives in `Mathlib.Analysis.Calculus.Deriv.Inv` — a narrow-import file must ADD that import; then call `_root_.HasDerivAt.div` (dot-notation picks the wrong `HasFDerivAtFilter` namespace) | AbelRuffiniOQ09 |
| `unfold myDef` "failed to unfold" after `convert … using n` | use `simp only [myDef, …]`; if `convert` spawns spurious instance-equality goals (`instAddCommGroup = …`), avoid `convert` entirely — prove the value equation `rw`-ready with an explicit `have hveq : lhs = rhs := by …; ring` then `rw [hveq]; exact h` | AbelRuffiniOQ09 |
| `notation:_ α " →ₒ (" β … ` "invalid atom" | a `(` (or other bracket) embedded inside a notation token string is now rejected — SPLIT into separate quoted atoms: `" →ₒ " "(" β ", " …` | Erdos590 |
| `Ordinal.IsLimit` field `(ω^ω).IsLimit` "Invalid field `IsLimit`/`Quot.IsLimit`" | `Order.IsSuccLimit (ω^ω)` (prefix form) | Erdos590 |
| `Ordinal.isLimit_opow_left h hpos` "Unknown constant" | `Ordinal.isSuccLimit_opow_left (h : IsSuccLimit a) (hb : b ≠ 0)` — note 2nd arg is `b ≠ 0` (`omega0_pos.ne'`), not `0 < b`; `Ordinal.omega0_isLimit` → `Ordinal.isSuccLimit_omega0` | Erdos590 |
| `Ordinal.opow_lt_opow_right h1 hlt` "Unknown constant" | `Ordinal.opow_lt_opow_iff_right (h : 1 < a)` — now an IFF `a^b < a^c ↔ b < c`; use as `rw […]` or `.mpr`. For a nat exponent first `rw [show ω^n = ω^(n:Ordinal) from (Ordinal.opow_natCast ω n).symm]` | Erdos590 |
| `Ordinal.one_lt_opow` "could not unify" | now an IFF `1 < a^b ↔ 1 < a ∧ b ≠ 0` → `.mpr ⟨one_lt_a, b_ne_zero⟩` | Erdos590 |
| identifier containing `²` (superscript two), e.g. `abbrev ℝ²` "unexpected token 'ℝ'/'²'; expected identifier" | `²` is no longer a valid identifier character — RENAME to a plain ASCII/greek identifier (`RealPlane`) and replace all usages | Erdos97 |
| `ConvexIndep id (↑A)` "Unknown identifier `ConvexIndep`" | `ConvexIndependent 𝕜 (p : ι → E)` — now takes an EXPLICIT scalar field + an indexing map; wrap as a local `def ConvexIndepSet (A : Finset E) : Prop := ConvexIndependent ℝ (fun x : (A : Set E) => (x : E))` and replace call-sites | Erdos97 |
| `induction p using Polynomial.induction_on' with \| h_add … \| h_monomial …` "Invalid alternative name `h_add`: Expected `add` or `monomial`" | rename alternatives `h_add`→`add`, `h_monomial`→`monomial` (case tags lost their `h_` prefix); a trailing `congr 1; simp` may now over-solve → fold into one `simp only [… , Complex.conj_ofReal]` | DescartesRuleOfSignsOQ01OQ01 |
| `ext` "No applicable extensionality theorem found" on a `ℂ` equality goal | `apply Complex.ext` (generic `ext` no longer fires on `ℂ`) | DescartesRuleOfSignsOQ01OQ01 |
| `push_neg; rfl` "rfl failed: `p → ¬q` not defeq `¬p ∨ ¬q`" | `push_neg` now yields the `→` form, not `∨` → replace `rfl` with `tauto` | CantorsTheoremOQ01OQ01 |
| `simp_all` in a `fin_cases i <;> fin_cases j <;> simp_all` closes MORE cases → remaining bullet count changes; a leftover goal is `¬q = p` but `hpq : ¬p = q` and `hpq.symm` fails (`Function.symm`) | drop the now-empty bullets; prove `¬q = p` via `fun h => hpq h.symm` (`hpq` is `p = q → False`) | Erdos375 |
| `SimpleGraph.Iso.refl _` "don't know how to synthesize implicit `G`" / "Function expected" | `SimpleGraph.Iso.refl` (NO explicit arg — it now takes only the implicit `{G}`, driven by the expected type) | Erdos1036OQ01OQ01 |
| `def f … := let mut … / for … in … do …` "unexpected token 'mut'" (imperative body outside a `do`) | wrap the body: `:= Id.run do  let mut …  … return result`; convert bare `if … then x` tails to `return x` | TestApi423 |

**Skipped as deep/multi-class (documented for later pass):** Erdos807 (placeholder `True` conjecture makes the "refutation" vacuously false — pre-existing modeling defect, not a v4.31 drift); Erdos910/910Provable (ambiguous `aleph` + universe metavars + `Continuous.prod_mk` removed); Erdos483 (namespace-wrap CLEARS the `schurNumber` `[_root_.schurNumber, SchursTheorem.schurNumber]` ambiguity — via `import Proofs.SchursTheorem` + `open SchursTheorem` + own root `schurNumber` — but 6+ residual native_decide-synth/tm/omega errors remain); FTCLebesgueOQ04 & PtolemysTheoremOQ01Incomplete01 (imports-after-docstring is a 1-line move, but each has 10+ residual removed-const/rewrite/linarith errors); SchroederBernsteinOQ01 & many category files (`HasForget` removed → `ConcreteCategory C FC` overhaul, 21 sites); Ballot cluster (`condCount`/`Probability.CondCount.lean` removed entirely → conditional-probability reconstruction, #38612 item 1); Derangements/BuffonsNeedle (removed helper lemmas `derangements_div_factorial`, `factorial_cast_pos`); Erdos766 (SimpleGraph.mk now 3-field + `{ f x | x : T // p x }` set-builder-with-predicate parse change + odd `⟨G, hG⟩`-as-Graph constructs).

**Namespace-wrap recipe (reusable):** for a file whose OWN root-level `def foo` now collides (`[_root_.foo, OtherNS.foo]`) because it `open OtherNS` (a `Proofs.*` import that also defines `foo`) — insert `namespace ThisFile` right after the `open` and `end ThisFile` at EOF. Unqualified references then resolve to the current-namespace `foo` (current namespace wins over `open`ed), clearing all the ambiguity errors at once.
