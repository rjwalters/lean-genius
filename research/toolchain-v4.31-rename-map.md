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

### 7r. Doctor increment-18 recipes (#38065, 2026-07-13, tm/pd/rewrite + mixed)

**Meta-finding:** the DR20a single-error diag is STALE — most of its 792 blocks
were re-shuffled or already dep-flipped by inc-13/15/16; re-verify fresh before
editing. The RESIDUAL rows are genuine multi-error files (typically 3–8 interlocking
errors each). Pre-filter with `grep -c sorry <file>` and error count: a file with
`sorry` is `formalized` and CANNOT go GREEN (Erdos370/391/402). Highest-yield
targets = 1–2 fresh-error files. +17 GREEN this increment.

| v4.31 symptom | fix | source |
|---|---|---|
| `field_simp` now CLOSES the goal, leaving a trailing `ring`/`ring_nf` as "No goals to be solved" | delete the trailing tactic (recurs ~everywhere: AreaOfCircle, Erdos310/355) | AreaOfCircleOQ01OQ02OQ01 (×3) |
| `convert h using 1; ring` where h is a `HasDerivAt … .const_mul` — ring_nf "made no progress" (convert unified the function, left a commuted deriv-value goal it won't touch) | supply the value explicitly: `have hval : <goal-value> = <h-value> := by ring; rw [hval]; exact h` | AreaOfCircleOQ01OQ02OQ01 |
| `(↑(n+2))/2` cast does NOT auto-simplify to `↑n/2+1` under `push_cast`; a `have hcast : (↑n+2)/2 = ↑n/2+1` rewrites BOTH the exponent and the inner `Γ((↑n+2)/2+1)` occurrence, leaving `Γ(↑n/2+1+1)` | one `rw [hcast]` then `Gamma_add_one` on the `+1+1` (do NOT also write a `hcast2` for `(↑n+2)/2+1` — hcast1 already consumed it) | AreaOfCircleOQ01OQ02OQ01OQ01 |
| `div_le_div_of_le_left` REMOVED (`a/b ≤ a/c` given `c ≤ b`, both pos) | `gcongr` (leaves ONE side-goal `denom ≤ denom` or `0 < denom`; check count before adding bullets — `gcongr <;> [tac]` guesses wrong) | AreaOfCircleOQ01OQ02OQ01OQ01OQ01 |
| `Even`/`Odd` destructure `⟨k, rfl⟩` yields `k + k` NOT `2 * k` (omega/rw pattern `2*k` fails) | `rw [show k + k = 2 * k from by ring]` after the destructure, or state helper facts over `k+k` | AreaOfCircleOQ01OQ02OQ01OQ01OQ01, Erdos44 (heq atoms) |
| `Cardinal.aleph0_lt_aleph` is now an **Iff** `ℵ₀ < ℵ_ o ↔ 0 < o`, not a function-of-`o` — "Function expected" when applied to an arg | `(Cardinal.aleph0_lt_aleph (o := 1)).mpr (by norm_num)` | Erdos1170Problem |
| `simp [has3AP]`/`use a, d` reshuffles an existential-witness goal so the trailing constructor chain misaligns | replace the whole tactic block with a single `refine ⟨a, d, proof₁, ⟨k, by norm_num⟩, …⟩` anonymous constructor | Erdos199Problem |
| `Multiset.mem_toFinset.mp (by simp [hx])` — the simp path to `x ∈ s.val.toFinset` from `x ∈ s.val` broke | `by simpa using hx` (Finset.mem_val); `s.sum id = ∑ x∈s, x` bridged by `simpa [id] using hsum` | Erdos338Problem |
| calc with a `>` step then a redundant `≥` step yields `>` overall but the field/target expects `≥` ("'calc' expression has type _ > _ but is expected _ ≥ _") | drop the calc, use `nlinarith`/`linarith` with an explicit `α*N ≥ (1/2)*N` bridge; a `(0:ℚ).den`/`Rat.den 0` residual after `Finset.sum_empty` needs an explicit `unitFractionSum ∅ = 0` rewrite (omega treats `Rat.den` as an atom) | Erdos310Problem |
| `norm_num` no longer evaluates `Nat.choose` literals (`⊢ 6 ≤ Nat.choose 4 2`) | `decide` (confirms §7k) | Erdos503Problem |
| after `Nat.succ`/`induction k`, the goal carries `k + 1 + 1` but a lemma/hyp is stated with `k + 2` → `rw [filter_congr h]` "pattern not found" | `simp only [show k + 1 + 1 = k + 2 from rfl]` to align the goal before the rw | Erdos1000Problem |
| goal `1.27 < 4/π` — `div_lt_iff₀` "pattern `?/π < ?` not found" (the division is on the RHS) | `lt_div_iff₀` (RHS division); then `1.27*π<4` needs a TIGHTER π bound than `pi_lt_d2` (3.15 gives 1.27·3.15=4.0005 > 4) — use `Real.pi_lt_d4` (π<3.1416) | Erdos33Problem |
| `fin_cases hm <;> first \| exact ⟨…, by simp, …⟩ \| …` — an inner `by simp` now leaves `⊢ False` (partial progress) instead of failing, so `first` does NOT backtrack → phantom "unsolved goals ⊢ False" ×(cases−1) all on ONE line | replace with positional bullets `·` per `fin_cases` goal | Erdos403Problem |
| `tsum_geometric_of_lt_one h1 h2` passed inside `simp_rw [...]` leaves the ratio `r` a metavar ("⊢ 0 ≤ ?m") | split it out to a standalone `rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]` AFTER `simp_rw [h1, tsum_mul_left]`; `1/2^(n+1)=(1/2)*(1/2)^n` via `div_pow, one_pow, pow_succ` | Erdos355Problem |
| `fin_cases i <;> fin_cases j <;> simp_all` then positional bullets — simp_all collapses to fewer goals (order flipped, `¬p=q` → `¬q=p`) → "No goals"/type-mismatch on the bullets | fold the symmetry into the simp set: `simp_all [hpq, hpq.symm, Ne.symm]`, drop the bullets | Erdos375Problem |
| `Finset.prod_insert` places the NEW element FIRST (`(m+n+1) * ∏…`), so an `ih` keyed on `∏… * m!` no longer matches after `mul_comm`/`mul_assoc` | explicit `rw [show ((m+n+1)*∏…)*m! = (∏…*m!)*(m+n+1) from by ring, ih, …]` | Erdos388Problem |
| `Nat.mem_divisors` over-unfolds under `simp` to `(d∣n ∧ ¬n=0) ∧ …` — `(Nat.mem_divisors.mp h).1` then fails (h is already the conjunction) | access by nesting depth: `h.1` / `h.1.1`; `card_le_card_of_injOn` maps into `↑(Icc …)` (Set coe) so use `Finset.coe_Icc, Set.mem_Icc` not `Finset.mem_Icc`; `Nat.lt_succ_sqrt'` is now `n < n.sqrt.succ ^ 2` (`rwa [Nat.succ_eq_add_one, sq]`); `(fun d => n/d) dᵢ` eta → `simp only [] at heq` | Erdos414Problem |
| malformed `Nat.one_le_pow k 2 _ \|>.trans_lt (by omega) \|>.le` proving `2^k ≥ 2` where k may be 0 (unprovable) | prove via monotonicity on the genuinely-≥1 exponent: `calc 2 = 2^1 := by norm_num; _ ≤ 2^d := Nat.pow_le_pow_right (by norm_num) hd'`; `heq.symm ▸` cast failures → explicit `rw [heq, …] at h` | Erdos44Problem |

**Verification note:** the earlier full bulk re-verify (runner3, 190-file shards)
is too slow on `import Mathlib` umbrellas (~15-20s each even warm). Once the base
cache is built, a per-file `lake build Proofs.X` is the fast fix-verify loop.
`docker restart dr28` before each rebuild to dodge virtiofs staleness on
/Volumes/Stripe worktrees (confirms 5B).
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

### §7s Doctor increment 20 recipes (tm/pd/rewrite + mixed, 2026-07-13)

| symptom | fix | files |
|---|---|---|
| `rw [pow_add]` / `rw [pow_mul]` fail to unify against `ℤˣ` (`Units Int`) `Monoid.npow` (rewrite metavar stalls, though `exact pow_add _ _ _` works term-mode) | drive via `calc` + TERM-mode `pow_add _ _ _`/`pow_mul _ _ _`; `congrArg (·^k) h` for `(-1:ℤˣ)^2=1 (by decide)` | QuadraticReciprocityAlgorithmOQ03M2 |
| `convert x using 1` on a value/HasDerivAt goal surfaces an instance-congruence goal FIRST (`instAddCommGroup = …toAddCommGroup`), blocking the value `rw`/`nlinarith` | value-first: `have hval : <goal> := by …; rw [hval]; exact x` (sidestep convert; `using 2` does NOT reliably skip it) | BallotProblemOQ02OQ03, BuffonsNeedleOQ01OQ01OQ04OQ01Beta, ArsinhLogFormula…, Erdos1049Aristotle |
| `Subgroup.card_subgroup_dvd_card` / `card_eq_card_quotient_mul_card_subgroup` return `Nat.card` (was `Fintype.card`) | `simpa only [Nat.card_eq_fintype_card] using …` + drop the now-wrong `.symm` | LagrangeTheoremOQ05 |
| `Subgroup.Normal.quotient_commutative_iff_commutator_le` yields `IsMulCommutative` (was `Std.Commutative (·*·)`) | `haveI : IsMulCommutative …`; comm proof via `h.is_comm.comm a b` (NOT `h.comm`) | AbelRuffiniOQ06OQ01 |
| `MonoidAlgebra.single` no longer unfolds to `Finsupp.single` → `rw [Finsupp.single_eq_single_iff]` fails | retype: `have hg2 : (Finsupp.single a b : …) = Finsupp.single c d := hg; rw [Finsupp.single_eq_single_iff] at hg2`; `Multiplicative.ofAdd_eq_one` is bare `ofAdd_eq_one` (`↔ x=0`) | MaschkeModularCounterexampleOQ01 |
| `Submodule.map_span` needs a `LinearMap`; a `LinearEquiv` coercion doesn't match | `Submodule.span_image_linearEquiv` then `Submodule.map_eq_top_iff` | CayleyHamiltonCyclicVectorAllFieldsOQ03Bridge |
| `AffineIndependent.fintype_card_le_finrank_succ` → `card_le_finrank_succ`, now over `finrank (vectorSpan …)` not `finrank E` | bridge `Submodule.finrank_le _` before omega | ShapleyFolkmanAristotle |
| `Multiset.coe_sum` → `Multiset.sum_coe` | rename | Erdos338Aristotle |
| `Nat.Coprime.divisors_mul` now yields a `Finset.map` form | use `Nat.Coprime.card_divisors_mul` for the card | Erdos1049Aristotle |
| `IsInteger` (bare) → `IsLocalization.IsInteger` | namespace-qualify | FactorRemainderTheoremOQ02 |
| `div_eq_div_iff` denominator `ne` args must match the goal EXACTLY (stricter unify) | pass the denominators that actually appear (swapped hA↔ha) | LawOfCosinesOQ01OQ01OQ01 |
| `Nat.fib k` no longer simp-reduces to a literal; `0<b` ↮ `1≤b` under simpa | `rw [show Nat.fib 3 = 2 from rfl]`; `omega` | GCDAlgorithmOQ01OQ03OQ01 |
| `theorem` on `Fintype …` (Sort, not Prop) rejected | `noncomputable def`; `IsPrincipalIdealRing (𝓞 ℚ)` via `IsPrincipalIdealRing.of_surjective (Rat.ringOfIntegersEquiv).symm.toRingHom …surjective` | MinkowskiFundamentalTheoremOQ02 |
| `Quaternion.normSq (p*q)` rewrite (`map_mul normSq`) no longer type-checks on anonymous-constructor product | `simp only [Quaternion.normSq_def', QuaternionAlgebra.mk_mul_mk]; ring` | LagrangeFourSquaresOQ05 |
| narrow-import file: `(6:ℚ)/2=3` leaves `⊢ 6/2=3` (norm_num ℚ-division extension not imported) | `import Mathlib.Tactic.NormNum.DivMod` (+ `Data.Rat.Cast.Defs`) | Erdos812Problem |
| `field_simp` no longer self-finishes cast normalization inside a `∑` | `field_simp; push_cast; ring` (both split_ifs branches) | Erdos25Abel |
| `det_fin_three` simp leaves numeric residual `2-1-1=0` | append `ring` | PappusTheoremOQ02 |
| AddAction→MulAction: `Multiplicative.ofAdd r • c = c ↔ r +ᵥ c = c` closes by `rfl`; `∑ ZMod n` vs `∑ Multiplicative (ZMod n)` domain | `rfl`; re-index via `Equiv.sum_comp Multiplicative.ofAdd` | BurnsideCountingOQ03OQ03 |
| `field_simp` matches denominators up to SYNTACTIC order only | supply commuted `1-e+e*d ≠ 0` haves via `rw [mul_comm]; exact …` | CevasTheoremOQ01OQ03 (denominators fixed; ring identity deferred) |

**Meta**: single/two-own-error triage off the warm cache is the fast finder — build all sorry-free my-class candidates in ONE `lake build`, `grep -oE '^error: Proofs/…\.lean' | uniq -c | sort -n`; single-error rows are highest-confidence. Files with `grep -w sorry` are formalized and CANNOT go GREEN (pre-filter them: 100 of 469 my-class rows). Statement-repair a genuinely false numeric claim to the intended-true value (Cevas `1/10`→`25/252`), never weaken.
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

---

## §7t Doctor increment 21 recipes (parse/sig/elab/dot structured remainder, #38065, +12 GREEN)

| Symptom | Fix | Examples |
|---|---|---|
| binder/type `x : … | y` "unexpected token ':='/'|'" | ASCII `|` is no longer `∣` (divides) in these positions → use `∣` | Erdos490Aristotle |
| `G.loopless u h` "Function expected at G.loopless (has type Std.Irrefl …Adj)" | `.loopless` is a bundled `Std.Irrefl` now → `G.loopless.irrefl u h` | Erdos79Incomplete01 |
| `[TopologicalGroup G]` "invalid binder annotation, type is not a class instance" | class renamed → `[IsTopologicalGroup G]` | Hilbert5LieGroups |
| `{ inferInstanceAs (P X) with … }` "inferInstanceAs failed, expected type contains metavariables" | bind first: `let _i : P X := inferInstanceAs (P X)` then `{ _i with … }` | ZsqrtdNegTwoOQ03 |
| `omit [Cls X] in` before decl "cannot omit referenced section variable inst✝" | body actually uses the instance → delete the `omit … in` line | LittleWedderburnOQ01OQ02 |
| `haveI := hInst` after `obtain` "synthesized instance not defeq to inferred (this✝ vs hInst)" | apply the lemma with explicit `@lemma _ … hInst₁ hInst₂ …` (don't re-`haveI`) | InverseGaloisA5OQ02 |
| docstring `/-- … -/` before `open … in` / `omit … in` "unexpected token open/omit; expected lemma" | put `open/omit … in` FIRST, then docstring, then decl | Erdos345Problem, MaschkeTheoremOQ01 |
| orphan `/-- … -/` (no following declaration) "unexpected token '/-!'/…; expected lemma" | change `/--` → `/-` (plain comment) | StirlingFormula |
| structure fields `a : ℝ; b : ℝ; c : ℝ` on one line "unexpected token ';'" | one field per line | LawOfCosinesOQ03OQ02 |
| `simp/rw/rwa […] at <axiom | t.field | proj>` "Unexpected term …; expected single reference to variable" | materialize first: `have h := <term>; simp […] at h` | Erdos345Problem (axioms), LawOfCosinesOQ03OQ02 (`t.law_sines`) |
| `def Foo := V →ₗ[R] W` then `f x` "Function expected at f" | v4.31 won't unfold plain `def` in app position → `abbrev Foo := …` | Hilbert20BoundaryValue |
| `Nat.find`/DecidablePred synthesis fails in theorems using a `Prop`-body predicate | add `open scoped Classical` at namespace top | Erdos345Problem |
| `Cardinal.aleph 0 < Cardinal.aleph 1` "failed to infer universe levels" | pin `(Cardinal.aleph 0 : Cardinal.{0})` | DenumerabilityRationalsOQ01 |
| `Polynomial.modByMonic_add_div p hMonic` "Application type mismatch" | now `(p q : R[X])` — pass the DIVISOR poly, not the Monic proof: `modByMonic_add_div p (X - C a)` | FactorRemainderTheorem (same as inc-17 CayleyHamilton) |
| `pow_one m` where `m = m^1` expected | `(pow_one m).symm` | Erdos345Problem |

**A namespaced `def _root_.T.method` recipe (dot-notation across imports):** when a child file
inside `namespace Child` defines `def T.method` for a type `T` imported from a parent, dot-notation
`x.method` (x : T, T at root) now FAILS to find `Child.T.method` — declare it as
`def _root_.T.method` so it lands in T's own namespace. (Cleared 4 errors in Erdos1006OQ01OQ02;
that file's residual is a separate LT/Preorder instance-diamond — deferred.)

**Virtiofs truncation FALSE-POSITIVES (re-confirmed):** apparent `Invalid name after 'end':
Expected X, but found X-truncated` or `Unknown identifier <name>-truncated` at EOF → the mount
truncated the file mid-read. `docker restart dr31`, rebuild, verify by exit code (hit 4× this
increment: ZsqrtdNegTwoOQ03, DenumerabilityRationalsOQ01, Erdos79Incomplete01, FactorRemainderTheorem).

## §7u Doctor increment 23 recipes (tm/pd/rewrite + mixed, #38065, +N GREEN)

Gaussian-integral / area-of-circle cluster (integration-by-parts + rpow + ENNReal):

| symptom (v4.31) | fix | files |
|---|---|---|
| `integral_mul_deriv_eq_deriv_mul` rejects `∀ x, HasDerivAt …` hyps ("expected `∀ x ∈ tsupport …`") | wrap: `(fun x _ => hu x) (fun x _ => hv x)` — the two deriv hyps are now tsupport-restricted | AreaOfCircleOQ07OQ05OQ01, OQ07OQ05 |
| `simpa using (hasDerivAt_pow n x).neg` fails: `.neg` prints `-fun x => x^n` (fn-negation), won't unify with goal `HasDerivAt (fun y => -y^n) …` | typed intermediate: `have h : HasDerivAt (fun y => -y^n) (-(↑n * x^(n-1))) x := (hasDerivAt_pow n x).neg; simpa using h` (defeq forced at the `have`) | OQ07OQ05OQ01, OQ07OQ05 |
| `simpa using hasDerivAt_id x` → AddCommGroup-instance mismatch | `fun x => hasDerivAt_id x` (direct term; `id ≡ fun y => y`) | OQ07OQ05 |
| `hasDerivAt_integral_of_dominated_loc_of_deriv_le (ε := r) … (h : 0<ε)` — signature lost `ε`; now `s ∈ nhds x₀` (a `Set`) | replace `(ε := 1) … one_pos` with `(Metric.ball_mem_nhds x₀ one_pos)`; `∀ x s _` ∀-hyps line up with `∀ x ∈ s` | AreaOfCircleOQ05OQ03OQ05 |
| `hr.le` where `hr : 0 ≤ r` → `Real.le.le` unknown-field | use `hr` directly; derived nonneg (`0 ≤ r^2`) → `by positivity` | AreaOfCircleOQ02, OQ02OQ01 |
| `Real.rpow_mul pi_nonneg.le` → same `.le`-projection error | `Real.rpow_mul pi_nonneg` (takes `0 ≤ x` directly) | AreaOfCircleOQ02OQ01 |
| `Gamma_add_one` leaves an un-normalized cast arg inside `Gamma (…)`, so `field_simp` can't unify the two Gamma calls | `rw [show ((n-2:ℕ):ℝ)/2 + 1 = (n:ℝ)/2 from by push_cast [Nat.cast_sub hn]; ring]` first | AreaOfCircleOQ02 |
| combine `ENNReal.ofReal((2r)^2 * π)` with a leading numeral | `rw [show (2*r)^2*π = 4*(r^2*π) by ring, ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤4), ENNReal.ofReal_ofNat]` | AreaOfCircleOQ02 |

General proof-drift (Cantor nested-interval / countability cluster):

| symptom | fix | files |
|---|---|---|
| `exists_surjective_nat α ⟨0⟩` — "Function expected" | `exists_surjective_nat α` (Nonempty/Countable are instances now) | AlgebraicNumbersCountableOQ02OQ02 |
| `simp [h1, h2]; linarith` → "No goals to be solved" (simp self-closed) | drop trailing `linarith` | AlgNumbers OQ02OQ02 |
| `apply csSup_le ⟨…⟩` → anon-ctor "expected type could not be determined" | `refine csSup_le ⟨…⟩ ?_` + `rintro x ⟨m, hm⟩` | AlgNumbers OQ02OQ02 |
| `abs_of_nonneg` on `dist (a n) (a (n+1))` fails (a strictly incr → inner is negative): `Real.dist_eq x y = |x - y|` in that order | `rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (…)]` | AlgNumbers OQ02OQ02OQ01 |
| no-op `dsimp only` → "made no progress" | delete the line | AreaOfCircleOQ07OQ05OQ02 |
| `convert x using 1; ring` "made no progress" (metavar stall, confirms §7s) | `have hval : lhs = rhs := by ring; rw [hval]; exact x` | OQ07OQ05OQ01, OQ07OQ05, OQ05OQ03OQ05 |

### §7u continued — increment 23 waves DR33f-m

| symptom (v4.31) | fix | files |
|---|---|---|
| `Polynomial.content_dvd_coeff q n` "type mismatch: q : ℤ[X] expected ℕ" — polynomial arg is now `{p}`-implicit, only `(n)` explicit | `content_dvd_coeff (p := q) n`; but for `IsPrimitive`'s `hr : C r ∣ p` use `(C_dvd_iff_dvd_coeff r p).mp hr n` for `r ∣ p.coeff n` | AngleTrisectionCos20GalOQ03OQ01 |
| `unfold abbrevName` "failed to unfold" (abbrev, not def) | `simp only [abbrevName]` | AngleTrisectionCos20GalOQ03OQ01 |
| `linarith` over a bare `CommRing` (no order) | `sub_eq_zero.mp (key.trans hrhs)` for `a = b` from `a - b = 0` | AngleTrisectionCos20GalOQ03OQ01 |
| `rw [pow_succ]` no longer rewrites `(1+a)^(m+1)` inside a subsequent `nlinarith` goal | drop the `rw`, pass `pow_succ (1+a) m` as an `nlinarith` hint | BernoulliInequalityOQ01OQ02 |
| casting `↑(n*(n-1)/2)` (Nat division) — `push_cast` can't split the `/2` | `Nat.cast_choose_two` (`↑(a.choose 2) = ↑a*(↑a-1)/2`) | BernoulliInequalityOQ01OQ02 |
| `Nat.primeFactors_mul` yields `∪` (not `insert`) | `Finset.sup_union` (not `sup_insert`) | BorsukUlamOQ02OQ01OQ01OQ02OQ03 |
| `not_le_of_lt` removed | `not_le.mpr h` | BorsukUlamOQ02OQ01OQ01OQ02OQ03 |
| `intro ⟨h⟩` / `rintro ⟨h⟩` on a hyp that is a `<` (= `Nat.le (succ ..)`, multi-ctor) fails "more than one constructor" | `intro h` (it's a plain `<`, not a 1-field structure) | BorsukUlamOQ02OQ01OQ01OQ02OQ03 |
| a 1-field `abbrev`/`def P := IsUnit …` shadows `IsUnit.mul` — `hM.mul hN` resolves to `P.mul` (recursion) | `simp only [P, …] at *` to expose the underlying `IsUnit` before `.mul` | BezoutIdentityOQ04OQ01OQ01 |
| matrix `snf.D ⟨0, by omega⟩ ⟨1, _⟩` accesses fail to fold with `set`-vars after a `simp` normalizes indices `⟨0,_⟩ → (0 : Fin n)` (OfNat) | restate ALL index accesses (haves, `set`, `congr_fun`) with `(0 : Fin n)` OfNat literals — mixing `⟨0,_⟩` and OfNat breaks `linear_combination` folding | BezoutIdentityOQ04OQ01OQ01 |
| `minpoly_gen`/`minpoly_cbrt3` `rw` "did not find pattern" though visibly present — instance mismatch on the `AdjoinSimple`/`Algebra` instance; `minpoly_gen` also needs `F α` explicit now | `rw [show minpoly ℚ (AdjoinSimple.gen ℚ α) = minpoly ℚ α from minpoly_gen ℚ α, …]` forces the instance to unify | CubeRoot3IrrationalOQ03OQ03 |
| `convert hd using 1` surfaces an instance-congruence goal FIRST (`instAddCommGroup = NormedDivisionRing…toAddCommGroup`) — §7s (recurred) | value-first: `have hval : <goal-value> = <hd-value> := by …; rw [hval]; exact hd` | BuffonsNeedleOQ01OQ01OQ04OQ01OQ01OQ01 |
| `mk_Iio_ordinal` now ambiguous | qualify `Ordinal.mk_Iio_ordinal` | DiamondImpliesCH |
| `expSeries_div_hasSum_exp 𝕂 x` — moved to `NormedSpace` namespace, field now implicit (only `(x)` explicit); result is `NormedSpace.exp x` | `NormedSpace.expSeries_div_hasSum_exp x`; `Real.exp_eq_exp_ℝ : Real.exp = NormedSpace.exp` bridges | DerangementsConvergenceOQ05OQ01 |
## §7u Doctor increment 22 recipes (parse/sig/elab/dot structured remainder, #38065, +7 GREEN)

| Symptom | Fix | Examples |
|---|---|---|
| `expected token` at every `ℝ≥0∞` occurrence in a file | `ℝ≥0∞` notation is now SCOPED → add `open scoped ENNReal` | Erdos1043Aristotle, LebesgueMeasureOQ03OQ01 |
| `norm_num` "unsolved goals" on an ENNReal scientific literal (`2.386`, `3.3`) comparison | bridge `(d : ℝ≥0∞) = ((d : NNReal) : ℝ≥0∞)` (by `rfl`), `rw [ENNReal.coe_lt_coe/coe_le_coe]`, then `rw [← NNReal.coe_lt_coe/coe_le_coe]; push_cast; norm_num` | Erdos1043Aristotle |
| calc first-term/step `EXPR \|>.card` → `unsolved goals` + next line `unexpected token '≤'; expected command` | parenthesize: `calc (EXPR).card ≤ …` (pipe-projection no longer parses as a calc atom; def-body / non-calc uses are fine) | Erdos52Problem, Erdos806Problem, Erdos863Aristotle |
| `unterminated comment` at EOF, unclosed `/-` traces to line 1 | a literal `/-!`/`/-` token sits as PROSE inside the `/- … -/` header; v4.31 NESTS block comments so it opened a nested comment that ate the header's `-/` → remove/reword the token | Hilbert11_QuadraticFormsAristotle |
| `X has already been declared` where X is in a `namespace` the file's imported parent also opens | remove the child's duplicate stub (parent already declares it; same-namespace re-decl across an import now errors) | Erdos795ProblemAristotle |
| `interval_cases <term>` (non-variable, e.g. `p.natDegree`) / `simp_all […] at *` (simp_all takes no `at`) | replace the block with a direct lemma-driven proof (e.g. `Polynomial.comp_eq_zero_iff` case split) | BaselProblemOQ02Aristotle |
| `left`/`right` "target is not an inductive datatype" after a `simp only […]` that used to unfold `∈ … ∪ …` | `simp only [Finset.mem_product]` no longer unfolds `Finset.mem_union` → `exact Finset.mem_union.mpr (Or.inl/inr …)` | Erdos806Problem |
| `absurd h (by decide)` / `by decide` "Expected type must not contain free variables" | goal carries a free var (e.g. `n`) `decide` can't reduce → `simp [structFields] at h` (reduce the projection to a literal first) | Hilbert11_QuadraticFormsAristotle |

**Meta-finding (confirms inc-17/19/21):** the parse/sig/elab/dot remainder is now dominated by
files whose structural first-error is NECESSARY-BUT-NOT-SUFFICIENT — the mechanical fix
(reserved-token rename, namespace-wrap, docstring/omit reorder, `/-!`→`/-`, Std.Symm/Irrefl
`⟨⟩` field, universe pin, `open scoped ENNReal`, calc-pipe parenthesization) clears the first
error but exposes a multi-error cascade in another class (unknown-const / rewrite-drift /
instance-synth / tm / removed-const / latent statement bug). Those files were reverted to keep
the tree clean; see STATUS.md inc-22 "Flagged deep" for the full list and the exact residual
per file. The reliably-flippable shapes this increment were small self-contained Aristotle
companions and duplicate-decl / nested-comment / calc-pipe single-issue files.

---

## §7v Doctor increment 24 recipes (tm/pd/rewrite/unknown-const/instance-synth, N-Z + Erdos≥600 partition, #38065, +24 GREEN)

| Symptom (v4.31) | Fix | Files |
|---|---|---|
| `theorem foo : DecidablePred p` / any `Sort`-valued (non-Prop) theorem "type of theorem is not a proposition" | `noncomputable def foo` | Erdos1006OQ04Decidability |
| explicit binder `n` referenced in `by omega`/lemma-arg AFTER `obtain ⟨m, rfl⟩ := hodd` substituted `n := 2*m+1` → "Unknown identifier `n`" | replace the now-gone `n` with its substituted value `(2*m+1)` | Erdos1012OQ01OQ02 |
| `rpow_one` / `rpow_le_rpow_of_exponent_le` "Unknown identifier" in narrow-import file | namespace-qualify `Real.rpow_one`, `Real.rpow_le_rpow_of_exponent_le` | Erdos1028Problem |
| `use a,b,…,N` then `exact hN` → "No goals to be solved" (the `use` auto-closed the ∀-tail via `hN`) | fold the witness into one `exact ⟨a,b,…,N,hN⟩` | Erdos1028Problem |
| `Nat.factorial_le_factorial` "Unknown constant" | `Nat.factorial_le` | Erdos1059OQ02OQ01 |
| **`ring` fails / `ring_nf made no progress` on a NON-commutative `[Ring R]` commutator identity** (`[x+y,z]=[x,z]+[y,z]`, Jacobi) — v4.31 `ring` no longer silently falls through on a non-`CommRing` | `unfold myDef; noncomm_ring` | Erdos1098OQ03 |
| **axiom / theorem used BEFORE its declaration** (v4.31 forbids forward reference that older elab tolerated) → "Unknown identifier `foo`" where `foo` is declared later in the file | MOVE the `axiom`/`theorem` block up above its first consumer; if this orphans a docstring, convert that `/-- -/` → `/- -/` (or attach it to the moved decl) | Erdos1126Problem (axiom), Erdos1150Problem (theorem), Erdos829Problem (native_decide theorem) |
| `tendsto_const_nhds.add _` / `.const_mul_zero` — const/filter metavars unsolved, or `Filter.Tendsto.const_mul_zero` removed | pin `tendsto_const_nhds (x := 1) (f := atTop)`; for the removed `const_mul_zero` use `(h.inv_tendsto_atTop).const_mul c` + `simpa` | Erdos1150Problem, Erdos612ProblemAristotle |
| `calc EXPR \|>.card ≤ …` pipe-projection at calc-atom → "type expected, got #(…)" + next-line "unexpected token" | parenthesize: `calc (EXPR).card ≤ …` (also fix the `have`-type line the same way) | Erdos604Problem |
| `obtain ⟨…⟩ := hmem` where `hmem : x ∈ Finset.image/filter …` → "Quot.lift … is not an inductive datatype" | destructure via explicit `rw [Finset.mem_image] at hmem; obtain …; rw [Finset.mem_filter] at …`; build membership with `Finset.mk_mem_product hx hy` (filter predicate `(p,q)↦p≠q` wants `x≠y`, so `hy_ne.symm` if you have `y≠x`) | Erdos604Problem |
| `native_decide` "depends on 'X', which is 'noncomputable'" where the *only* noncomputability source is an `open scoped Classical` / `attribute [local instance] Classical.propDecidable` making a genuinely-decidable `def` noncomputable | DROP the Classical open/attribute so the concrete `Decidable` instance is used; if the def is over `Finset ℤ` etc. the `≤`/`Icc` are already computable. **CAUTION**: after dropping, native_decide computes the REAL truth — if it evaluates the test proposition to `False`, that was a pre-existing bad statement (flag, don't weaken) | (Erdos662/Erdos838 = Classical is load-bearing for ℤ-order, deferred; TestApi241 = evaluates FALSE, flagged) |
| `#{1,p}=2` residual after `simp [Nat.Prime.divisors hp]` | `Finset.card_pair hp.one_lt.ne` | Erdos673Aristotle |
| `Nat.Coprime.divisors_mul` now returns a `Finset.attach.map` form (card lemma broke) | use `hcop.card_divisors_mul` (in `Nat.Coprime` ns, gives `#(m*n).divisors = #m.divisors * #n.divisors`) | Erdos673Aristotle |
| docstring `/-! -/` (or `/-- -/`) FOLLOWED BY `import` → "invalid 'import' command, it must be used in the beginning of the file" | move ALL `import` lines to the very top, above the header docstring | PtolemysTheoremOQ01Incomplete01 (import fixed; deeper `Complex.abs_mul_exp_arg_mul_I` cascade deferred) |
| `Int.cast_nonneg.mpr` "Unknown constant" (`Int.cast_nonneg` no longer the Iff/moved to bare `cast_nonneg`) | `by exact_mod_cast h.le` / `by exact_mod_cast h` | PellEquationOQ01 |
| `Finset.exists_ne_of_one_lt_card h a` removed (only the `Fintype.card` form `exists_ne_of_one_lt_card` survives, in EquivFin.lean) | `(Finset.one_lt_card_iff_nontrivial.mp h).exists_ne a` | PropertyBFirstMomentRecoloring |
| `Units.val_pow_eq_pow_val` `rw` metavar-stalls on a `↑((-1:ℤˣ)^k)` coercion goal `x = ↑(y^k)` | close with `norm_cast` (not rw + norm_num) | QuadraticReciprocityAlgorithmOQ03M2Capstone |
| `isCyclic_of_subgroup_isDomain f Units.ext` — `Units.ext` no longer the injectivity proof | `Units.val_injective` | PrimitiveRoots, PrimitiveRootsOQ02 |
| `orderOf_eq_card_of_forall_mem_zpowers hg` now returns `orderOf g = Nat.card α` (was `Fintype.card α`) | append `Nat.card_eq_fintype_card` in the rw chain | PrimitiveRoots, PrimitiveRootsOQ02 |
| `instance : Decidable (myDef …) := inferInstance` fails because `myDef := orderOf g = …` and `orderOf` is noncomputable in v4.31 | `noncomputable instance … := Classical.dec _` (acceptable when no `native_decide` depends on it) | PrimitiveRootsOQ02 |
| duplicate `theorem foo` where an imported parent (same `namespace`) already declares `foo` → "`Parent.foo` has already been declared" | remove the child's duplicate decl; its uses resolve to the parent's | RothTheoremOQ03OQ01OQ01 |
| `not_even_iff_odd` "Unknown identifier" | `Nat.not_even_iff_odd` | SumOfDivisorsOQ01SpecialPrime |
| `Finset.disjoint_comm` "Unknown constant" (moved out of `Finset` ns) | bare `disjoint_comm` (Order namespace) | SubsetCountOQ02OQ01 |
| `Real.pi_lt_3141593` removed (decimal-name pi bounds gone) | `Real.pi_lt_four` (goal needs π<4) / `Real.pi_lt_d4` (needs <3.1416) | TestApi513 |
| `Nat.not_prime_of_le_one h` removed | `fun h' => absurd h'.one_lt (by omega)` | TestApi688 |
| `omega` fails on a `Nat.div_add_mod`-based goal with `p` a variable (nonlinear `p * (x/p)`) | `rw` the `% p = a` and equal-div hyps INTO the `div_add_mod` equations first, so omega sees only linear residuals | TestApi688 |
| `Finset.lcm_insert (by simp)` — "Function expected" (`lcm_insert` is now a bare `@[simp]` eq, no membership arg) | drop the `(by simp)`: `rw [Finset.lcm_insert]` | Erdos873ProblemProvable |

**Meta**: the batch-build "clean" heuristic is UNRELIABLE — a file with no own `error:` line in a
multi-target build often just never compiled (a shared dep failed early). Always confirm each
candidate with an isolated per-file `lake build Proofs.X; echo $?`. Mid-edit races produce
transient wrong exit codes (a build that overlaps a file write) — re-run once, isolated, and trust
the "Build completed successfully"/`EXIT=0` line. Forward-reference (axiom/theorem-before-use) and
duplicate-decl are the two highest-yield NEW v4.31 shapes in this partition (5 of 24 flips).

**Deferred (deep / multi-class / genuine gap, reverted):** Erdos1055Problem (`change`/`show` defeq
blocked by a `foldl` `have`-proof-term in the WF def body); Erdos1206Problem (`simp`/`linarith`
gaps are REAL math: subset needs `N-k≥1`, card bound needs `·^3` injectivity); Erdos680Problem
(`tendsto_pow_mul_exp_neg_atTop_nhds` lost its `(1+ε)` scaling arg → proof restructure);
Erdos662Problem/Erdos838Problem (Classical propDecidable is load-bearing for the ℤ/Point2D-order
Finset); SchroederBernsteinOQ01 (`HasForget` removed → ConcreteCategory overhaul);
SylowTheoremsOQ05 (whnf heartbeat blowup, >1M insufficient); PtolemysTheoremOQ01Incomplete01
(`Complex.abs_mul_exp_arg_mul_I` removed atop an existing partial migration); Erdos870Aristotle
(sorry-in-`def` after the `theorem`→`def` Sort fix — hard error). TestApi241 flagged: `IsB3 {1,2,4,8}`
native-evaluates to FALSE once Classical is dropped (bad pre-existing test, not weakened).
### §7u continued — increment 23 waves DR33n-p (follow-up)

| symptom (v4.31) | fix | files |
|---|---|---|
| `simp at h` loses `id`-reduction; `omega` then can't see the ineq | `simp only [id_eq] at h` | Erdos341Problem |
| `rw [Finset.mem_product] at hp` "did not find pattern" on `S.product S` (SetLike-membership elab) | `(Finset.mem_product.mp hp).1/.2` term-mode | Erdos341Problem |
| `simp only [h0, Prod.fst, Prod.snd]` — `Prod.fst`/`Prod.snd` are projection FUNCTIONS not simp lemmas → no reduction, `omega` sees nothing | plain `rw [h0]` (the `.1`/`.2` then reduce definitionally) | Erdos341Problem |
| `fin_cases h` on a hypothesis that is a **Prop-disjunction of equations** (e.g. from `simp [subset_insert_iff]` on `X ⊆ {1,2}`) fails "expected Type" | recover the enumerable form: `X ∈ ({1,2}).powerset` (via `Finset.mem_powerset.mpr hX`), then `fin_cases` on that | Erdos350Problem |
| `rw [zpow_neg, …, zpow_natCast, …]` chain after a `ring_nf` that already normalized the exponent → "did not find pattern" | drop `ring_nf`; normalize the exponent first `rw [show -(↑(n+1)) = -↑n - 1 by push_cast; ring]` then `zpow_sub₀ (‹2≠0›), zpow_neg, field_simp, ring` | Erdos350Problem |
| `rintro (rfl | …)` on disjunction equalities that are not `x = t` (e.g. `2*a+2 = a+1`) fails "subst" | `rintro (h | …)` named + `omega` (unfold nonlinear def on the GOAL first: `simp only [somaniC]` before rintro) | Erdos397Problem |
| `Finset.prod_insert`/`prod_singleton` builds a RIGHT-associated product; goal is LEFT-associated | append `mul_assoc` (or `ring`) after the rw chain | Erdos397Problem |

### §7w addendum — Doctor increment 24 continued (post-PR#38625, +8 more GREEN)

| Symptom (v4.31) | Fix | Files |
|---|---|---|
| `Finset.card_Ioc` "Unknown constant" | `Nat.card_Ioc` | Erdos867Problem |
| `List.get? i` "environment does not contain `List.get?`" | `l[i]?` (GetElem? notation) | Erdos867Problem |
| `simp [Finset.subset_iff]` now self-closes a concrete `⊆` goal → trailing `omega` "No goals" | replace the block with `decide` (concrete Finset) | Erdos867Problem |
| `l[(i.val+1) % l.length]` / any `l[expr]` with a computed index → "failed to prove index is valid" | supply the bound: `l[expr]'(Nat.mod_lt _ i.pos)` (for `Fin`-derived `i`, `i.pos : 0 < l.length`) or `Nat.mod_lt _ (by omega)` | Erdos916Problem, Erdos608Problem (partial) |
| `.get ⟨i, by omega⟩` where the bound hyp is the `∀`'s anonymous arrow antecedent → omega "No usable constraints" | NAME the antecedent (`∀ i, (hi : i+1 < len) → …`) so it enters the local context, and switch to `l[i]'(by omega)` | Erdos900Problem (partial) |
| `isOrdinaryLine_symm P p q h` / `distSq_self q` → "Unknown identifier p/q" after `rcases … with rfl`/`rintro rfl` substituted the binder away (v4.31 subst direction eliminates the named binder) | pass `_` for the substituted point args and let the expected type drive inference | Erdos960Problem, Erdos661Problem |
| `pow_lt_pow_left h (0≤a) (0<n)` → "Unknown identifier" (general lemma gone; now 2-arg `Nat.pow_lt_pow_left : a<b → n≠0 → a^n<b^n`) | `Nat.pow_lt_pow_left (by omega) n_ne_zero` | Erdos773Problem |
| `ne_of_lt` / `le_or_lt` / `Nat.le_or_lt` ambiguous or removed | `_root_.ne_of_lt`; `le_or_gt a b : a≤b ∨ b<a` | Erdos773Problem, Erdos922Aristotle |
| `∀ᶠ N in Filter.atTop, … (f N) … (N:ℝ)^…` where `f N` needs `N:ℕ` but binder infers `N:ℝ` → "argument N has type ℝ expected ℕ" | pin the binder `∀ᶠ (N : ℕ) in Filter.atTop` | Erdos773Problem |
| bare `log n` ambiguous (`Nat.log` vs `Real.log`) in a `K * log n` real statement | qualify `Real.log` | Erdos728Problem |
| `nlinarith`/`linarith` can't multiply a hypothesis `ε < 1/2` by a variable `n` | add the product term explicitly: `nlinarith [mul_lt_mul_of_pos_right hε hn0]` | Erdos728Problem |
| `|(f n : ℕ) - g n|` "failed to synthesize `AddGroup ℕ`" (abs needs a group; ℕ subtraction truncates) | cast the whole difference to ℝ: `|((f n : ℝ) - (g n : ℝ))|` (intended-true form for an "…- O(n)" statement) | Erdos669Problem |
| `theorem foo : myDef k …` where `myDef` unfolds to `nhds (1/(k*(k-1)))` not defeq the axiom's `nhds (1/6)` | `unfold myDef; norm_num; exact axiom` (compute the numeral before matching) | Erdos669Problem |
| `omega` on `n*(n-1)/2 ≥ n` (nonlinear ℕ product + division) | `rw [ge_iff_le, Nat.le_div_iff_mul_le (by norm_num)]` then `Nat.mul_le_mul_left`/`omega` on the cleared form | Erdos911Problem |
| `linarith` on a goal whose LHS is an un-beta-reduced `(fun x => …) x` | `refine ⟨…, fun x hx => ?_⟩; simp only; have := …; omega` (beta-reduce first) | Erdos911Problem |
| `divisors_prime` / `simp [Nat.divisors]` residual `#{1,p}=2` / `#({x∈{1}|x=1})=1` | `Nat.divisors_one`; `Nat.Prime.divisors hp` + `Finset.card_pair hp.one_lt.ne` (same as §7v Erdos673) | Erdos964Aristotle |
| `omega` on a ℕ goal whose only constraint is a Real hypothesis (`hq_pos : (0:ℝ) < ↑q`) | bridge with `Nat.cast_pos.mp hq_pos` (omega can't read Real casts) | Erdos964Aristotle |
| structure-field `Nat.pow_le/lt_pow_right (by norm_num) (by omega)` where the base metavar can't be pinned (RHS `2^(n+1)≥2` not syntactically `2^1`) | `gcongr` (for `<`) or `show 2^1 ≤ …` + `pow_one` bridge (for `≥`) | Erdos967Problem |
| `Filter.Tendsto.const_mul_zero` removed; div_pos ambiguous (`_root_` vs `Nat`) | `(h.inv_tendsto_atTop).const_mul c` + `simpa`; `_root_.div_pos` | Erdos977ProblemAristotle |
## §7v Doctor increment 25 recipes (tm/pd/rewrite + unknown-const + instance-synth, A–M partition, #38065, +16 GREEN)

| Symptom | Fix | Files |
|---|---|---|
| `inner x y` (real/complex inner product) "Type mismatch: `a-b` has type Plane but expected Type" — `inner` now takes the **scalar field explicitly first** | `inner ℝ x y` (or `⟪x, y⟫_ℝ`); a `det`/2nd-`inner` error on the same decl is a CASCADE of the first — fix the first and rebuild | Erdos189Problem |
| `Nat.coprime_succ_self` removed | `(Nat.coprime_self_add_right (n:=1)).mpr (Nat.coprime_one_right _)` (`simpa`) | Erdos375Aristotle |
| `h.not_le` / `.le` projection on a `≤`-value → "environment does not contain `Nat.le.not_le`" | `absurd (le_proof) (Nat.not_le.mpr h)` (confirms §7u: ≤-values have no `.le`/`.not_le` field) | Erdos375Aristotle |
| `Nat.choose_two_middle` removed (goal `(k+1).choose 2 = (k+1)*k/2`) | `rw [Nat.choose_two_right, Nat.add_sub_cancel]` (behind a `show (k+1).choose 2 = …` so the `1+1` reduces to `2`) | ArithmeticSeriesOQ02OQ03 |
| `Nat.smul_eq_mul` removed (after `Finset.sum_const` gives `card • n`) | bare `smul_eq_mul` | Erdos250Problem |
| `Nat.one_lt_iff_ne_one.mp hn` removed (need `n ≠ 1` from `hn : 1 < n`) | `hn.ne'` | Erdos384Problem |
| `Nat.choose_symm_diff` removed (goal `C(n, n-1) = n`) | `rw [Nat.choose_symm (by omega : 1 ≤ n), Nat.choose_one_right]` | Erdos384Problem |
| **Forward reference to an `axiom` (or theorem) declared LATER in the same file now hard-errors** (`Unknown identifier` + `rcases … is not an inductive datatype`) | REORDER: move the axiom/lemma block above its first use (preserves axiom/assumption count — pure reorder, not a repair) | Erdos530Problem |
| Mathlib **added `SimpleGraph.pathGraph`** → an imported same-named local `Foo.pathGraph`/`starGraph` becomes **"Ambiguous term"** at every bare use | qualify the local refs with the owning namespace, `Foo.pathGraph n` | Erdos548Aristotle |
| Same-namespace **re-declaration** of a lemma the imported parent now also proves ("has already been declared") AND the companion adds nothing new | reduce the Aristotle companion to an import shim (`import parent` + comment) — all targets live in the parent | Erdos156ProblemAristotle |
| `Finset.induction … | insert ha ih` case pattern | `| @insert a t ha ih` (name the element+set); `Finset.prod_insert`/`sum_insert` inside also needs `[DecidableEq ι]` on the enclosing decl | Hilbert20OQ01OQ03Aristotle |
| `Finset.mem_product` alone no longer rewrites membership in `A.product A` (`simp` reports it unused; leaves a raw `Quot.lift` term, breaking a following `rcases`/`⟨⟩`) | add `Finset.product_eq_sprod` to the simp set alongside `Finset.mem_product` | Erdos476Aristotle |
| `apply Finset.card_image_of_injOn` fails to unify `#?s` with the literal `n` in `#(image f (range n)) = n` | `rw [Finset.card_image_of_injOn, Finset.card_range]` (then discharge the injOn goal) | Erdos476Aristotle |
| `rcases h with rfl | rfl <;> rcases h' with rfl | rfl` — the `rfl` substitutes the WRONG side, deleting the theorem's bound vars (`a`/`b` → "Unknown identifier") in a later branch | replace the explicit per-branch tactics with `<;> first | exact absurd rfl hne | rfl | exact add_comm _ _` (var-name-agnostic) | Erdos476Aristotle |
| coercion elaboration: a goal written `(∫ x, x ∂μ : ℂ)` now elaborates by pushing the cast **inside** the integral (`∫ x, ↑x`), so a lemma proving `↑(∫ x, x)` won't `exact` | write the outer cast explicitly: `Complex.ofReal (∫ x, x ∂μ)` | CentralLimitTheorem |
| `tendsto_one_plus_div_pow_exp` (the `(1+x/n)^n → eˣ` limit) unknown | `Real.tendsto_one_add_div_pow_exp` | CentralLimitTheorem |
| `expSeries_div_hasSum_exp ℂ x` — the leading algebra arg was dropped (now `(x)` only), and it's namespaced | `NormedSpace.expSeries_div_hasSum_exp x` (confirms DR33m) | EulerIdentity* (partial) |
| `IsSplittingField.adjoin_rootSet'` is a class FIELD requiring an `IsSplittingField` instance that won't synth through a `set p :=` | use the canonical `Polynomial.SplittingField.adjoin_rootSet _`; likewise `Normal ℚ p.SplittingField` synth → explicit `Polynomial.SplittingField.instNormal p` | InverseGaloisF20 |
| a `set p := (X^5 - C 2)` folds the polynomial, so a lemma output mentioning `(X^5-C 2).rootSet` won't `rw`-match the folded `p.rootSet` | avoid `rw`; chain with `.trans` (`(lemma …).trans …`) | InverseGaloisF20 |
| NormedRing (possibly noncommutative) `ring` fails on a purely-additive identity (`B-1 = -(1-B)`, `B = A-(A-B)`) or a `↑u*(↑u⁻¹*x)` unit-cancel | use `neg_sub`/`abel` for additive goals; a reusable `hcancel : ∀ x, ↑u*(↑u⁻¹*x) = x` via `← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul` | GeometricSeriesOQ02OQ03 |
| `edgeCount` def with `p.1 < p.2` on a bare `V` → "failed to synthesize `LT V`" | add `[LinearOrder V]` to the def; an internal `∃ (V : Type*)` in a `Prop def` also needs `Type`-pinning to kill the derived-thm universe-metavar (§7o) | Erdos571Problem |
| nlinarith fails on a ℕ descent `(2x)²+(2y)²+(2z)² = 4^(a+1)(8b+7) ⊢ x²+y²+z² = 4^a(8b+7)` | `have hpow : 4^(a+1)=4*4^a := by rw [pow_succ]; ring`, then `have : 4*(sum)=4*(target) := by rw [hpow] at heq; nlinarith [heq]`, then `omega` | LagrangeFourSquaresOQ04 |

## §7x Doctor increment 27 recipes (tm/pd/rewrite/unknown-const, N-Z + Erdos≥600, #38065, +6 GREEN)

| Symptom (v4.31) | Fix | Files |
|---|---|---|
| `Finset.exists_smaller_set s n (h : n ≤ s.card)` "Unknown constant" | `Finset.exists_subset_card_eq (h : n ≤ #s)` — same `∃ t ⊆ s, #t = n`, drop the explicit `s`/`n` positional args, pass only the `≤` proof | Erdos1026Problem (4 uses) |
| `omega` fails on `n = (k+1-1)*(k+1-1)+1` given `hn : n = k^2+1` (omega can't equate `k^2` with `k*k`) | `rw [Nat.add_sub_cancel, hn, pow_two]` | Erdos1026Problem |
| `even_zero` "Unknown identifier" (removed) | `Even.zero` | PythagoreanTriplesOQ04OQ01OQ01 (3 uses) |
| `Nat.even_iff_not_odd.mp he` "Unknown constant" (goal `False` from `Even`/`Odd`) | `Nat.not_odd_iff_even.mpr he` (returns `¬Odd`, apply to the `Odd` hyp) | PythagoreanTriplesOQ04OQ01OQ01 |
| symmetric-difference `∆` "expected token" (notation now `scoped[symmDiff]`) | add `open scoped symmDiff` to the file header | Erdos1123Problem (parse fixed; Setoid-proof cascade deferred) |
| `Set.image_subset f (h : s⊆t)` "Unknown constant" | `Set.image_mono (h : s⊆t)` (f now implicit) | Erdos1018OQ04Incomplete01 (first-error only; deeper cascade) |
| `lt_of_le_not_le` "Unknown identifier" | `lt_of_le_not_ge` | Erdos1059OQ04 (first-error only) |
| child re-declares a lemma the imported parent now also declares (same namespace) BUT the two have
  DIFFERENT statements | RENAME the child's decl (e.g. `foo`→`foo_mul`) + update its internal uses —
  do NOT delete (they are genuinely distinct theorems that only collide by name) | ProbMethodSecondMomentOQ01 (`paley_zygmund_quantitative`→`_mul`; first-error only) |
| top-level local `structure Hypergraph`/`def Foo` clashes with a NEW Mathlib top-level decl of the
  same name ("has already been declared") | wrap the file's decls in `namespace X … end X` OR rename
  the local — but CAUTION: namespace-wrapping can expose latent universe-metavariable / defeq errors
  that the global elaboration had masked | Erdos1020Problem (deferred — universe metavars surfaced) |

**Meta (partition N-Z + Erdos≥600)**: heavily multi-error. First-error rename/reorder/notation fixes
usually expose 2-6 downstream errors (cascade). Reliable wins: single-symptom rename files, and
stale-RESIDUAL rows already clean off the 37508 base (PentagonalNumberTheoremOQ01OQ01/OQ01OQ02 flipped
with zero edits). `Complex.abs` removal (now a local compat `def`, not an `AbsoluteValue` hom) is a
recurring deep blocker: `map_mul`/`map_add`/`AbsoluteValue`-API on it all fail — needs whole-file
migration, not a one-line compat (NapoleonsTheorem family deferred).
## §7x Doctor increment 26 recipes (tm/pd/rewrite + instance-synth, A–M / Erdos<600 partition, #38065, +21 GREEN)

| symptom | fix | files |
|---|---|---|
| `Ordinal.omega` in `ω^β` → `HPow (Ordinal ↪o Ordinal) ...` synth failure | `Ordinal.omega0` — plain ω₀; `Ordinal.omega` is now the ↪o normal-function embedding | Erdos592 |
| `2 ^ ℵ₀` / `2 ^ κ` → `HPow ℕ Cardinal` synth failure (the `2` elaborates as ℕ) | annotate the base: `(2 : Cardinal) ^ ℵ₀` | ContinuumHypothesisOQ02OQ01 |
| `p ^ c` with `p:ℕ`, `c:ℝ` → `HPow ℕ ℝ` failure | `(p : ℝ) ^ c` | Erdos445 |
| `def X := Finset …` (or any type alias) → `∈`/`.card`/`∅` can't find Membership/EmptyCollection | make it `abbrev` so the alias is reducible for instance search | Erdos500, Erdos94OQ02 |
| `IsAlgClosure ℚ (AlgebraicClosure ℚ)` no longer auto-synthesizes (the `Algebra.IsAlgebraic` half isn't an instance) | reassemble: `where isAlgClosed := inferInstance; isAlgebraic := AlgebraicClosure.isAlgebraic ℚ` | AlgebraicNumbersCountableOQ01OQ03 |
| parent `Algebra.IsAlgebraic K (algebraicIntermediateField K L)` instance won't unify through a downstream `abbrev` in instance search | re-expose a local specialized instance `Algebra.IsAlgebraic ℚ algebraicNumbersField := parent_lemma (K:=ℚ)(L:=ℂ)` | AlgebraicNumbersCountableOQ01OQ01OQ01/OQ03 |
| after `push_neg`, `∀ε>0,∃…` and `¬∃ε>0,∀…` become **definitionally equal** | drop the brittle `constructor <;> intro`/destructure machinery — just `rfl` | Erdos543 |
| `Finset.sum_le_sum_of_subset` → `failed to synthesize CanonicallyOrderedAdd ℝ` | on non-canonically-ordered types use `Finset.sum_le_sum_of_subset_of_nonneg h (fun i _ _ => …nonneg…)` | BaselProblemOQ01OQ01 |
| `Finset.le_sup h` type-mismatch (wrong `f` inferred) | pass the function explicitly: `Finset.le_sup (f := fun i => …) h` | ContinuumHypothesisOQ02OQ01 |
| `Irreducible.separable` → `failed to synthesize CharZero K` (base field not assumed perfect) | obtain the splitting-field root separability-free: `(SplittingField.splits p).exists_eval_eq_zero hdeg` with `hdeg : (p.map …).degree ≠ 0` via `degree_map` + `degree_pos_of_irreducible` | CayleyHamiltonMinpolyOQ05OQ02 |
| `finrank_mul_finrank K M L : … = finrank K L` but goal wants the reverse | append `.symm` | CayleyHamiltonMinpolyOQ05OQ02 |
| `Real.log_le_rpow_div` output is `x^p / p` shaped; a `rw [div_div_eq_mul_div, one_mul]` no longer matches | close with a `calc … ≤ x^p/p := h; _ = c*x^p := by ring` | ChebyshevBoundsOQ03OQ02 |
| `Finset.add_sum_erase _ (fun n => …explicit…) h` fails (summand lambda won't match goal after an earlier rw) | let the summand infer: `Finset.add_sum_erase _ _ h` | ChebyshevBoundsOQ03OQ02 |
| `Nat.floor_le (by positivity)` — positivity can't prove `0 ≤ log x / log 2` | supply explicitly: `div_nonneg (Real.log_nonneg h1≤x) (Real.log_nonneg …)` | ChebyshevBoundsOQ03OQ02 |
| `zify [show 1 ≤ m^2 from by positivity]` — positivity proves `0<`/`0≤` not `1≤` | use `by nlinarith` (or `by omega`) for the `1 ≤ …` side conditions | Erdos370 |
| a bound-var `n` gets typed ℝ in a multi-conjunct ∀ where later use needs `n!` | pin `∀ (n : ℕ) …`; if that then breaks a dependent `M : Matrix (Fin n)…` binder, make M's type explicit too | Erdos499 |
| `simp only [matrix cons lemmas]` leaves `!![…] i j` unreduced | plain `simp [diagonalProduct, Fin.prod_univ_two, perm-lemmas]` finishes the entry reduction | Erdos499 |
| `simpa … using c.map_zsmul …` over-reduces `c(n•1)=n•c 1` to `True` | pin the goal first: `conv_lhs => rw [show n = n•(1:ℤ) by simp]; rw [map_zsmul]; simp` | BorsukUlamOQ03OQ02 |
| `map_zsmul g n` prints/orders as `f(g*n)=g*f n` — pick arg order to match the goal's factor order | call `ψ.map_zsmul d a` (not `a d`) for `ψ(d*a)=d*ψ a` | BorsukUlamOQ03OQ02 |
| `Nat.primeFactors_mul` now yields `{p} ∪ {q}` (was `insert p {q}`) | `Finset.sup_union` + `Finset.sup_singleton ×2` instead of `sup_insert` | BorsukUlamOQ02OQ01OQ01OQ02OQ03OQ01 |
| `intro ⟨h⟩` on a Prop that is actually a `<` (or any multi-ctor inductive) → "expected type … has more than one constructor" | `intro h` then use it (`not_le.mpr h`, etc.) | BorsukUlamOQ02OQ01OQ01OQ02OQ03OQ01 |
| a `def f n := if n=0 then 0 else …` — after `unfold`, tactics see the `if` | `rw [if_neg (by omega : n ≠ 0)]` under the positivity hypothesis, then proceed | Erdos453OQ02 |
| `simp; exact lemma` → "No goals" because `simp` now fully closes it (e.g. `Nat.nth_prime_*` are simp lemmas) | drop the stale `exact` | Erdos453OQ02 |
| `Nat.sqrt_le_self` only gives `sqrt n ≤ n`, not `sqrt (n/2) ≤ n` | `calc sqrt (n/2) ≤ n/2 := Nat.sqrt_le_self _; _ ≤ n := Nat.div_le_self _ _` | Erdos441Aristotle |
| `simp [Nat.lcm]` leaves `a*a/a=a` | use `Nat.lcm_self a` directly | Erdos441Aristotle |
| `ArithmeticFunction.Carmichael` (capital) is a **deprecated alias** with a distinct head symbol → Mathlib rw-lemmas (`carmichael_pow_of_prime_ne_two`, `carmichael_factorization`) whose LHS is lowercase `carmichael` won't `rw`-match | replace applied `Carmichael` → `carmichael` (keep prose) | EulerTotientOQ01OQ01OQ01 |
| `mem_primeFactors` third field now wants `m ≠ 0` (was `0 < m`) | pass `hm.ne'` | Erdos459 (partial) |
| `⟪a, b⟫_ℝ` — the `_ℝ` suffix notation was removed | with `open scoped RealInnerProductSpace`, plain `⟪a, b⟫` is the ℝ-inner product; fix the atom name in any `linear_combination`/`ring` that referenced the old term | LawOfCosinesOQ04OQ01(+Bisector transitively) |
| local support-lemma gained a hypothesis / arg reorder (`… (hn : 1 ≤ n) (hsteps …)`) → "expected 1 ≤ … got euclidSteps … =" | supply args in the new order (`… hb hba (by omega) hsteps`) | GCDAlgorithmOQ01OQ03OQ01OQ01 |
| `field_simp; ring` → "No goals to be solved" | `field_simp` self-closes on ℝ div goals — drop the trailing `ring` (confirms earlier §7 recipe) | GCDAlgorithmOQ01OQ03OQ01OQ01 |
| `List.mem_cons_self a l` → "Function expected … a::l" | `List.mem_cons_self ..` (explicit args dropped) | (Erdos382 partial) |
| `![…] : EuclideanSpace ℝ (Fin 2)` type mismatch (matrix literal no longer coerces to PiLp) | `!₂[…]` (or `(EuclideanSpace.equiv _ _).symm ![…]`) | (Erdos94OQ02 partial) |

## §7y Doctor increment 31 recipes (tm/pd/rewrite/unknown-const/instance-synth, N-Z + Erdos≥600, #38065, +5 GREEN)

| Symptom (v4.31) | Fix | Files |
|---|---|---|
| **`Complex.abs` removed** (now a local compat `def Complex.abs z := ‖z‖`); `map_mul`/`AbsoluteValue`-API on it all fail; a prior migration's compat `lemma Complex.norm_def` now **collides** with Mathlib's real `Complex.norm_def` ("has already been declared") | Rename the local shim `Complex.norm_def`→`Complex.abs_def`; add `lemma Complex.abs_mul (w z) : Complex.abs (w*z) = _ * _ := norm_mul w z` and replace every `map_mul` on `Complex.abs` with `Complex.abs_mul`; for `Complex.abs X = 1` proofs, prove `Complex.normSq X = 1` as a `have` then `rw [abs_def, hns, Real.sqrt_one]` (the old `rw [show √(…)=√1 from …]` pattern no longer matches the drifted simp form) | NapoleonsTheorem, NapoleonsTheoremOQ02 |
| **`simp only`+`nlinarith`/`ring_nf` on a ℂ-`ext` algebraic identity fails** — v4.31 simp leaves `(I * ↑√3).im` / `{re:=…, im:=…}` structure-literals when the simp set is **asymmetric** (real bullet missing `mul_im`/`add_im`/`sub_im`, or vice versa) | Give BOTH `Complex.ext` bullets the **FULL symmetric** simp set (all `add/sub/mul/neg/one/zero`_re AND _im + `I_re/I_im/ofReal_re/ofReal_im/div_ofNat/re_ofNat/im_ofNat`), then close each **exact** identity with `linear_combination (C) * h3` where `h3 : √3*√3=3` and `C` = the √3²-coefficient polynomial of the goal difference. Probe C via `linear_combination (0:ℝ)*h3` and read the residual's `√3^2` coefficients, or compute symbolically (sympy `Poly(diff,t).coeff_monomial(t**2)`). nlinarith cannot prove these (equalities over ℝ with an exact √3²→3 substitution). | NapoleonsTheorem (6 cores), NapoleonsTheoremOQ02 (10 DFT branches) |
| **STATEMENT REPAIR**: `napoleon_side_sq` cross-term sign was `+(√3/6)·(signed area)`; the true Napoleon side-length identity needs `−(√3/6)·(…)` — verified symbolically (`solve` for the cross coeff k=−1/6). Repaired to intended-true form, NOT weakened. | NapoleonsTheorem |
| `Finset.prod_pos _ (fun i _ => …)` "Function expected" — `Finset.prod_pos` **dropped its leading placeholder arg**, now takes only the pointwise-positivity proof | `Finset.prod_pos (fun i _ => …)` | NewtonInductiveStepOQ03 |
| `simp [pow_succ]` no longer **folds `set`-bound atoms** (`set A := q^(n-k)`; goal `q^(n-k+1)=A*q` — simp re-expands to `q^(n-k)*q ≠ A`) | `rw [pow_succ]` (A is defeq q^(n-k)); for `A*B=q^n` use explicit `rw [show A=q^(n-k) from rfl, …, ← pow_add]` | NewtonInductiveStepOQ03 |
| `induction xs generalizing k` where a hypothesis `hxs : ∀ x ∈ xs, 0≤x` **mentions the inducted list** → v4.31 reverts `hxs` too, so the IH's **first** arg becomes the tail-nonneg hypothesis (arg order shifted) | reorder IH calls: `ih hxs' k hk hkn` (nonneg-hyp FIRST, was `ih k hk hkn hxs'`) | NewtonInductiveStepOQ02 (partial — deeper nlinarith drift remains) |
| `simp [M] at hM` no longer closes `Nat.Prime 0`/`Nat.Prime 1` to `False` | `norm_num [M, Nat.not_prime_zero] at hM` | PerfectNumbersOQ03 |
| `rw [ZMod.natCast_eq_zero_iff]` "did not find `↑?a = 0`" — a bare `(2 : ZMod q)` is NOT seen as a `natCast` | `rw [show (2:ZMod q) = ((2:ℕ):ZMod q) by norm_cast, ZMod.natCast_eq_zero_iff]` | PerfectNumbersOQ03 |
| `ZMod.pow_card_sub_one_eq_one h` now returns `x^(q-1)=1` **directly** (was the `Fintype.card (ZMod q)` form) | drop the redundant `rw [ZMod.card q]`; type the `have` as `x^(q-1)=1` | PerfectNumbersOQ03 |
| `norm_num [M]` now **fully evaluates** `¬Nat.Prime 2047` → a trailing `decide` hits "No goals to be solved" | drop the `decide` | PerfectNumbersOQ03 |
| **`p ∣ x` destructures as `⟨k, hkp : x = p * k⟩`** (was `k * p`) — later `rw [hkp]`/`hkp.symm` break on factor order | add `have hkp' : k * p = x := by rw [hkp]; ring` and use `hkp'` (or `mul_comm`) at every consumer | PicksTheoremOQ02 |
| `Finset.mem_image`/`mem_range` membership no longer **auto-splits a `Prod` equality**: a merged goal `(k*p, k*q) = (x,y)` wants ONE `⟨…⟩` proof field, not two ("Constructor `Eq.refl` does not have explicit fields, but 2 were provided") | provide the pair eq as a single term: `⟨k, by omega, by rw […]⟩` (fold the two r[/simp closers into one) | PicksTheoremOQ02 |

**Meta (partition N-Z + Erdos≥600)**: the Complex.abs cluster (NapoleonsTheorem family) IS clearable but is a genuine whole-file migration, not a one-line compat — the payoff recipe is *full-symmetric-simp + linear_combination(√3²-coeff)* for every ℂ-`ext` algebraic core. Two S-files (SubsetCountOQ02OQ01, SumOfDivisorsOQ01SpecialPrime) were stale-clean off the 37508 base but already flipped by the sibling — always re-check `origin/feature/issue-38065-c` GREEN set before claiming.

### §7y addendum — increment 31 continued (+4 more GREEN: SpectralTrace, SolutionOfCubic, PowerMean, Search, TestApi960/1061)

| Symptom (v4.31) | Fix | Files |
|---|---|---|
| `Matrix.charpoly_units_conj P A` is now `(↑P·A·(↑P)⁻¹).charpoly = A.charpoly` (P first; the `↑P⁻¹·A·↑P` order was the *primed* variant pre-v4.31) | for the `↑P⁻¹·A·↑P` goal apply `charpoly_units_conj P⁻¹ A` then `simpa` (folds `(↑P⁻¹)⁻¹ = ↑P`); needs `set_option maxHeartbeats 1000000 in` (abbrev-`charpoly` defeq is heavy) — put the `set_option … in` ABOVE the docstring | SpectralTraceDetEigenvaluesOQ02 |
| `ring` no longer distributes `Polynomial.C` over `+`/`*` | `simp only [Polynomial.C_add, Polynomial.C_mul]; ring` | SolutionOfCubicOQ03OQ05 |
| coeff-matching `simp [Polynomial.coeff_mul]` leaves an un-reduced `∑ x ∈ Finset.antidiagonal n, if …` | use `simp only [coeff_add, coeff_sub, coeff_X_pow, coeff_C_mul, coeff_C, coeff_X]; norm_num`; over a general `CommRing` close with `linear_combination this` (NOT linarith — R unordered) | SolutionOfCubicOQ03OQ05 |
| **STATEMENT REPAIR**: a `Filter.Tendsto (fun r => …) (nhdsWithin 0 {0}ᶜ) …` whose binder `r` **defaulted to ℕ** (broken: ℕ-division `1/r`, ℕ-`nhds 0`) — the intended real limit collapses | annotate `fun r : ℝ => …`; then the whole rpow/exp/log chain elaborates. (`HasDerivAt.sum` also needs the goal as `∑ i, (fun r => …)` via `Finset.sum_apply`, not `fun r => ∑`; `.const_mul` already gives `c*f` order — drop stale `mul_comm`; `slope` unfolds via `vsub_eq_sub`) | PowerMeanLimitOQ |
| `IsCompact.of_isClosed_isBounded` / `isCompact_of_isClosed_of_isBounded` unknown | `Metric.isCompact_of_isClosed_isBounded` | SearchMathlib, TestApi1056 (partial) |
| `Submodule.isClosed` unknown (finite-dim submodule is closed) | `Submodule.closed_of_finiteDimensional` | SearchMathlib |
| `Finset.offDiag_card` is now `#s.offDiag = #s * #s - #s` (was `#s * (#s - 1)`) | update the RHS; `Rat.toNat` removed (drop) | TestApi960 |
| `Finset.sum_pair h` — for a `{1, p}` (ascending) literal wants `h : 1 ≠ p` (use `hp.one_lt.ne`, NOT `.ne'` which gives `p ≠ 1` for `{p,1}`); a `.sum id` needs `rw [show id = fun x => x from rfl]` first | as noted | TestApi1061 |
## §7y Doctor increment 30 recipes (tm/pd/rewrite/unknown-const/instance-synth, A–M partition, +23 GREEN)

| symptom (v4.31) | fix | files |
|---|---|---|
| `rw [hker] at e` "motive is not type correct" (quotient group instance depends on the subgroup) | bridge via `QuotientGroup.quotientMulEquivOfEq hker`: `(quotientMulEquivOfEq hker).symm.trans e` | AbelRuffiniGaloisExtensionsOQ04OQ03 |
| `rw [Fintype.prod_sum]` leaves a defeq `X = X` residual (`Family σ` unfold) | append `rfl` | BallotProblemOQ03OQ02OQ03 |
| `structure.field` projection (`F.Total`) won't reduce for `[Subsingleton …]`/`[Nontrivial …]` instance synth | supply locally: `have : Subsingleton F.Total := inferInstance` (concrete type is known) | BorsukUlamOQ04OQ03 |
| `p ∈ L` "failed to synthesize `Membership _ Line`" (structure has no membership) | add `instance : Membership Point Line where mem L p := …` — **v4.31 arg order is `mem collection element`** | Erdos211Problem |
| `omega` on `0 < a*(b)*(c)` "No usable constraints" (nonlinear product) | `positivity` | Erdos130WIP01 |
| `lt_or_le` "Unknown identifier" | `lt_or_ge` (`a < b ∨ b ≤ a`) | CombinationsFormula…OQ02OQ01 |
| `inv_ne_zero.mpr` "Unknown constant" | `inv_ne_zero` is now a plain implication `a ≠ 0 → a⁻¹ ≠ 0` (drop `.mpr`, `apply inv_ne_zero`) | GeometricSeriesOQ03 |
| `rw [heq]` picks wrong occurrence when `heq : 1 = f x` (reversed) rewrites the RHS `1` | `rw [← heq]` | GeometricSeriesOQ03 |
| `Nat.eq_of_mul_eq_left` "Unknown constant" | `Nat.eq_of_mul_eq_mul_left` | Erdos327OQ01 |
| `Nat.dvd_of_dvd_of_dvd h (dvd_refl _)` "Unknown constant" (was a no-op trans) | drop it — the term is just `h` | Erdos369Problem |
| `Finset.card_Ico` "Unknown constant" | `Nat.card_Ico` (lives in `namespace Nat`, `#(Ico a b) = b - a`) | Erdos456Aristotle |
| `Real.one_lt_sqrt` "Unknown constant" | `Real.lt_sqrt (hx : 0 ≤ x) : x < √y ↔ x^2 < y` (rw `[gt_iff_lt, Real.lt_sqrt (le for x)]`) | Erdos267Problem |
| `Nat.fib_pos hn` "Function expected" | `Nat.fib_pos.mpr hn` (now an iff `0 < fib n ↔ 0 < n`) | Erdos267Problem |
| `intermediate_value_zero_of_le` "Unknown identifier" | `intermediate_value_Icc'` (decreasing: `hab` + `ContinuousOn` gives `Icc (f b) (f a) ⊆ f '' Icc a b`); membership `⟨hg1, hg0⟩` | IntermediateValueTheoremOQ03 |
| local `def Complex.abs (z) := ‖z‖` compat shim: `Complex.abs.map_zero` fails, `map_zero` won't fire | unfold the shim: `simp only [Complex.abs, norm_zero]` (the identifier `Complex.abs` itself is GONE from Mathlib — many files add a local shim) | Erdos509Problem |
| `Finset.sum_eq_sum_diff_singleton_add` "Unknown constant" | `← Finset.sum_erase (a := x₀) s (h : f x₀ = 0)` + `Finset.erase_eq` (`s.erase x = s \ {x}`); match the summand's `↑`-cast form exactly in the `f x₀ = 0` proof | TriangularNumberReciprocals |
| removed helper referenced BEFORE its later `def`/`theorem` = forward-ref hard-error (not just unknown-const) | inline the proof at the use site (don't rely on the later decl) | Erdos479Problem |
| Fermat `2^p ≡ 2 [ZMOD p]` from scratch | `rw [← ZMod.intCast_eq_intCast_iff]; push_cast; exact ZMod.pow_card (2 : ZMod p)` (needs `haveI : Fact p.Prime`) | Erdos479Problem |
| `rw [← ZMod.card p]` "motive not type correct" (rewrites the exponent `p` which also appears in `Fact p.Prime`) | use `ZMod.pow_card x : x^p = x` directly (avoids rewriting `p`) | Erdos479Problem |
| `List.bind` "environment does not contain" | `List.flatMap` | Erdos356Problem |
| `Finset.range'` "Unknown constant" (no such thing; only `List.range'`) | for `{1,…,n}` use `Finset.Icc 1 n` | Erdos356Problem |
| `![a, b]` "Type mismatch, expected `EuclideanSpace ℝ (Fin 2)`" (a `PiLp` alias) — `![…]` gives plain `Fin 2 → ℝ` | `(EuclideanSpace.equiv (Fin 2) ℝ).symm ![…]` (a bare `Fin 2 → ℝ` value coerces INTO `mulVec` etc. fine, only the constructed alias-typed value needs the wrap) | Hilbert16 |
| **`Module.finBasisOfFinrankEq` binder order changed** — `@… R M _ _ inst hfree hmf` now misaligns | new order is `(R M)[Semiring][AddCommMonoid][Module][Free][StrongRankCondition][Module.Finite]{n} hn` → `@Module.finBasisOfFinrankEq R M _ _ inst hfree _ hmf n hn` (query with `#check @…` to confirm binder order before guessing) | GroupOrderPrimeSquaredAbelianIsoOQ01OQ01OQ02 |
| own `theorem foo` collides with an imported parent's `foo` in a **reopened same namespace** ("already been declared") | rename the local (`foo_self`) and, if the parent's is more general, derive the local from it | Hilbert22OQ01OQ03Universal |
| `Nat.Primes.instCountable.toEncodable.decode i` "Unknown constant" (i-th prime) | `Nat.nth Nat.Prime i` | Erdos386Problem |
| `Set.eq_of_subset_of_ncard_le` needs `.ncard` but hyp is `Nat.card ↥S` | bridge each side: `(Nat.card_coe_set_eq _).symm : (↑S).ncard = Nat.card ↥S` then `rw` | LagrangeTheoremOQ01OQ03OQ01 |
| element bracket `⁅a, b⁆` "failed to synthesize `Bracket G G`" (subgroup bracket `⁅N,N⁆` still works) | `open scoped commutatorElement` | LagrangeTheoremOQ01OQ03OQ01 |
| `charmatrix_apply_ne h` "rewrite did not find pattern" / "hne wrong type" | now takes explicit `i j h` (`charmatrix_apply_ne _ _ _ hne`); `rw` won't unify the `.charmatrix` dot-notation → wrap as `rw [show M.charmatrix i j = -C (M i j) from charmatrix_apply_ne _ _ _ hne]` | MinpolyCharpolyOQ01 |

**Triage recipe (reusable):** build ALL sorry-free my-class candidates in ~5 batches of 90 off the warm
cache; the combined `lake build` stderr tags every error with its file (`error: Proofs/File.lean:L:C:`),
so `grep -oE '^error: Proofs/[^:]+' | sort | uniq -c` finds single-/two-error files (highest-confidence
fixes) across the whole partition in one pass, without per-file rebuilds.

## §7z Doctor increment 35 recipes (tm/pd/rewrite/unknown-const/instance-synth, N-Z + Erdos≥600, #38065, +9 GREEN)

Test*/TestApi* API-probe files are the reliable seam once single-error math rows are harvested:
they are small and their errors are usually `#check @<removed-const>` (delete/rename the line) plus
one example needing a rename.

| v4.31 breakage | fix | file(s) |
|---|---|---|
| `card_sylow_dvd_index P` "Unknown constant" | `P.card_dvd_index` (`Sylow.card_dvd_index`, returns `Nat.card (Sylow p G) ∣ P.index`) | SylowTheorem |
| `Sylow.exists_smul_eq G P Q` "Unknown constant" | `MulAction.exists_smul_eq G P Q` (pretransitivity method) | SylowTheorem, (OQ02Orbit) |
| `rw [← normalizer_eq_top]` did not find pattern | `rw [← normalizer_eq_top_iff]` (now the `↔ H.Normal` iff) | SylowTheorem |
| `isCyclic_of_prime_card rfl` instance-synth fail | it now takes `Nat.card α = p` (was `Fintype.card`): supply `Fact (Nat.card G).Prime` via `⟨by rwa [Nat.card_eq_fintype_card]⟩` | SylowTheorem |
| `rw [mem_normalizer_iff] at this` did not find pattern (after `smul_eq_iff_mem_normalizer`) | term-mode `(mem_normalizer_iff.mp this) x` avoids the coercion-shape mismatch | SylowTheorem |
| `fin_cases i` on `Fin 3` yields `⟨0,_⟩/⟨1,_⟩/⟨2,_⟩` so `rw [show (i:Fin 3).val = k from rfl, {zero,one,two}_nsmul]` no longer matches | replace the rw chain with `simpa [two_nsmul, ← two_mul] using …` (both `∀ i` and `.mp` directions) | RothTheoremOQ03 |
| `Set.Finite.isCompact_convexHull` "failed to synthesize `𝕜`" | `𝕜` is now an explicit leading arg: `(hFinite).isCompact_convexHull (𝕜 := ℝ)` | TestConvexHull |
| `MeasureTheory.snorm` / `snorm_add_le` / `snorm_le_snorm_mul_snorm_of_nq` "Unknown constant" | `eLpNorm` / `eLpNorm_add_le` / `eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm` | TestHolderApi |
| `rw [NNReal.HolderConjugate]` fails (now a predicate, not a def to unfold) | `rw [NNReal.holderConjugate_iff]` (`↔ 1 < p ∧ p⁻¹ + q⁻¹ = 1`) | TestHolderApi |
| `σ 1` (opened `ArithmeticFunction`) "Function expected at σ" in application position | qualify: `ArithmeticFunction.sigma 1` | TestApi1061b |
| `Continuous.if_lt` "Unknown constant" (only `if_le`/`if_ge` remain) | restate the `if p < q` as `if q ≤ p` (swap then/else) and use `Continuous.if_le hf' hg' hf hg hfg`; discharge frontier `hfg : ∀ x, f x = g x → f' x = g' x` by `subst` | TestApi234 |
| `Finset.filter_subset_filter` "could not unify" — it now means SAME predicate, subset SETS (`s ⊆ t → s.filter p ⊆ t.filter p`) | for a monotone PREDICATE use `Finset.monotone_filter_right` (`s ⦃p q⦄ (h : ∀ a ∈ s, p a → q a)`) | TestApi234 |
| `Int.Icc_toFinset_card`/`Nat.card_Icc_of_le`/`Real.exp_ge_one_add_of_nonneg`/`Real.exp_lt_one_of_neg`/`isLittleO_pow_exp_atTop`/`Nat.divisors_prime_eq`/`HasLines.mkFinOrder`/`ProjectivePlane.mkFinOrder`/`isCompact_isClosed_isBounded` "Unknown const/ident" as `#check` | removed constants — delete the exploratory `#check` line (API-probe files) | TestErdos43Api, TestApi312, TestApi1061b, TestApi1159b, TestConvexHull |
| `(Finset.Icc (1:ℤ) (N-1)).card` no longer `rfl`/`decide` | `rw [Int.card_Icc]; omega` | TestErdos43Api |

**Meta (reconfirms inc-14/17/32):** in the N–Z + Erdos≥600 partition the residual math rows
(proof-drift, type-mismatch, instance-synth) now cluster **3–18 errors each** — a single rename is
necessary-but-not-sufficient and the file must be reverted if any error remains. `Nat.one_lt_of_ne_one`
→ `one_lt_of_ne_one` (dropped `Nat.` prefix; now the general ordered-monoid alias) is correct but
Erdos733 still fails on removed `List.Sorted` in a `def`. No reusable cluster found for the
`fin_cases nsmul`, `isCompact_convexHull (𝕜:=)`, or `if_le`/`monotone_filter_right` renames — each hit
exactly one file in this partition.

## §7z Increment 37 recipes (N–Z + Erdos≥600) — HIGH-VALUE reusable

| Symptom | Fix | Files |
|---|---|---|
| `simpa using this` fails: goal `Real.exp ∘ f`/`Real.log ∘ f` Tendsto no longer auto-unfolds `∘` | `simpa [Function.comp_def] using this` | Erdos1014OQ03 (+LogIncrement) |
| bare `inner x y` "Application type mismatch: x has type V of sort Type but expected Type ?u" | `inner ℝ x y` (scalar field now EXPLICIT first arg) | PythagoreanTheorem |
| `open scoped RealInnerProductSpace` → `⟪·,·⟫_ℝ` errors `unexpected identifier` at `_ℝ` | `open scoped InnerProductSpace` (notation moved scopes) | ProductOfSegmentsOfChordsOQ01 |
| `inner_smul_left/right` leave `(starRingEnd ℝ) t` blocking `ring` | `simp only [starRingEnd_apply, star_trivial]` before `ring` | ProductOfSegmentsOfChordsOQ01 |
| `G.symm h` "Function expected at G.symm (has type Std.Symm G.Adj)" | `G.adj_symm h` | Erdos620Problem, Erdos1018Problem |
| `G.loopless x`/`G.loopless _ h` "Function expected at G.loopless (Std.Irrefl)" | `G.irrefl` (vertex now IMPLICIT): field `loopless.irrefl := fun _ => G.irrefl` / `fun _ h => G.irrefl h` | Erdos620Problem, Erdos1018Problem |
| `Finset.induction_on` insert case `\| insert ha ih` binds ELEMENT not hyp (ha : ι) | `\| @insert a s' ha ih =>` (element, set, `a∉s`, IH) | PythagoreanTheorem |
| `(realExpr).toNat` "Invalid field toNat: no Real.toNat" | `⌊realExpr⌋₊` (Nat.floor) | Erdos704Problem |
| `G.chromaticNumber` (now `ℕ∞`) used where ℕ expected | `.toNat` | Erdos704Problem |
| `Filter.limsSup atTop (fun n => …)` "Function expected" | `Filter.limsup (fun n => …) atTop` (function-first) | Erdos704Problem |
| `List.Mem.elim` gone: `hx.elim` for `x ∈ ([] : List _)` | `absurd hx (by simp)` | Erdos1029Problem |
| `rw [Tendsto, Filter.map_atTop_atTop]` "Failed to rewrite equation theorems for Tendsto" | `rw [Filter.tendsto_atTop_atTop]` (bridge `<`/`≤` with `h (M+1)`/`.le`) | Erdos1029Problem |
| `IsPrimePow p` by `decide` fails (instance won't reduce) for odd primes | `(prime_proof).isPrimePow` e.g. `Nat.prime_three.isPrimePow`, `(by norm_num : Nat.Prime 5).isPrimePow` | Erdos723Problem |
| `(realExpr on ℕ base)^(realpow)` "HPow ℕ ℝ" | cast base to ℝ: `(x : ℝ)^(r : ℝ)`; drop `.toNNReal.toNat` (NNReal `{r//0≤r}` has no `.toNat`) | Erdos1008ProblemProvable |
| `summable/tsum_geometric_of_lt_one` 2nd arg now STRICT `r < 1` | drop `.le` on the `<1` arg (keep `.le` on `0≤r`) | Erdos1049Problem |
| `∀ n ≥ 2, …` defaults `n:ℝ` breaking a ℕ-indexed fn | `∀ n : ℕ, n ≥ 2 → …` | Erdos620Problem |

**Statement repairs (inc-37):** Erdos723 `order_1_is_prime_power : IsPrimePow 1` was FALSE (1∉PrimePow)
→ `order_1_not_prime_power : ¬IsPrimePow 1`. Erdos620 `triangleFree_implies_K4Free` intro pattern
mismatched HasK4's 6-neq/6-adj conjunction → rewrote destructuring.

## §7aa Increment 37 (continued) recipes

| Symptom | Fix | Files |
|---|---|---|
| `norm_num`/`omega`/`push_neg`/`linarith` "unknown tactic" (parse error) in a file importing only narrow `Mathlib.X` modules | add `import Mathlib.Tactic` | Erdos775Problem, Erdos966Problem |
| `Set.ncard_insert_of_not_mem` "Unknown constant" | `Set.ncard_insert_of_notMem` | Erdos757Problem |
| `Set.ncard_coe_Finset` "Unknown constant" | `Set.ncard_coe_finset` (lowercase f) | Erdos757Problem |
| `Set.Finite.toFinset_card` "Unknown constant" for `hfin.toFinset.card` | `rw [← Set.ncard_eq_toFinset_card s hfin]` | Erdos757Problem |
| `insert a ↑F` treated as `Finset` ("Invalid field ncard: no Finset.ncard") | annotate `(↑F : Set _)` | Erdos757Problem |
| `x < ⊤` where `x : ℝ` ("failed to synthesize Top ℝ") | ℝ has no Top; restate finiteness as `∃ B, x ≤ B` | Erdos652Problem |
| `congr 1; Fin.ext h` overshoots to `b x = b y` goal | build `hidx : (⟨…⟩:Fin n) = ⟨…⟩ := Fin.ext h` then `rw [hidx]` | Erdos640Problem |
| `(k+1) % n = 0` / variable-modulus omega fails | `rw [Nat.sub_add_cancel …, Nat.mod_self]` | Erdos640Problem |

**Deferred:** universe-polymorphism mismatch between two `Prop` defs that each fix a different
`Type u` (`@h V` rejects `V : Type u₂`) is NOT a rename — needs `Type _`/level unification (Erdos794).
## §7z Doctor increment 34 recipes (tm/pd/rewrite/unknown-const/instance-synth, A–M partition, #38065, +15 GREEN)

| symptom (v4.31) | fix | files |
|---|---|---|
| `x*` / `hx*_in` as a **code identifier** → `unexpected token '*'; expected ',' or binderPred` (v4.31 tokenizes `*` after an ident in binder position) | rename the identifier (`x*`→`xs`, `hx*_in`→`hxs_in`); leave `x*` in `--`/`/- -/` prose | BrouwerFixedPointOQ04OQ04 |
| `rw [div_lt_iff₀ hn_pos]` yields `2 < ε * ↑n` (factor order flipped) so `← div_lt_iff₀ hε` won't match | insert `mul_comm` between: `rw [div_lt_iff₀ hn_pos, mul_comm, ← div_lt_iff₀ hε]` | BrouwerFixedPointOQ04OQ04 |
| `Nat.lt_of_lt_pred` "Unknown constant" (was used to get `0 < n` from `k+1 ≤ n`) | `have : 0 < n := by omega; exact_mod_cast this` | BrouwerFixedPointOQ04OQ04 |
| `![a, b] : EuclideanSpace ℝ (Fin 2)` "Type mismatch" (matrix literal is plain `Fin 2 → ℝ`, not the `WithLp`/`PiLp` alias) | `!₂[a, b]` (= `WithLp.toLp 2 ![a,b]`); the singleton `{![0,0]} : Finset (EuclideanSpace …)` likewise → `{!₂[0,0]}` | FeuerbachsTheoremDefsOQ04, Erdos216Problem |
| a `dist`/`norm` proof over `EuclideanSpace` now shows `(x - y).ofLp i` component atoms that `Matrix.cons_val_*` won't reduce | `rw [EuclideanSpace.dist_eq]` then `simp [WithLp.toLp_sub, WithLp.ofLp_toLp, Pi.sub_apply, Matrix.cons_val_zero, Matrix.head_cons, Matrix.cons_val_one, Matrix.head_fin_const]` | FeuerbachsTheoremDefsOQ04 |
| `have h : ⟨struct⟩.field ≠ 0 := …` "failed to infer universe levels in `have`" when the struct's carrier field is `X : Type*` (existential leaves the universe a metavar) | either drop the explicit `have` type (`have h := …` infers from the term, which carries the universe) OR **monomorphize the struct's carrier `X : Type*`→`Type`** if it is never constructed with a specific higher-universe carrier | FurstenbergCorrespondence |
| `open scoped ENNReal` missing → `expected token` at every `ℝ≥0∞` | add `open scoped ENNReal` (confirms §7u inc-22) | Erdos353Aristotle |
| `FiniteDimensional.finrank` "Unknown constant" | `Module.finrank` | Erdos353Aristotle |
| `inv_ne_zero.mpr h` "Unknown constant" (now a bare implication) | `inv_ne_zero h`; `ENNReal.ofReal_ne_zero` → `ENNReal.ofReal_ne_zero_iff`; `ENNReal.mul_top` takes the `a ≠ 0` proof directly (`ENNReal.mul_top h`) | Erdos353Aristotle |
| `-(1 / k)` with `k : ℕ` in an rpow-exponent slot → `failed to synthesize Neg ℕ` (`1/k` elaborated ℕ) | cast: `-(1 / (k : ℝ))` | Erdos35ProblemAristotle |
| `List.mem_cons_self a l` / `List.mem_cons_self _ _` "Function expected" | `List.mem_cons_self ..` (explicit args dropped) | DescartesRuleOfSignsOQ02Parity |
| a `% 2` case-bash `omega` fails (`↑(…)/2` unconstrained atom) after `split_ifs at ih ⊢` didn't resolve the `if` | materialize the parity fact `have := Nat.mod_two_eq_zero_or_one (countF …)` before the bash; `norm_num at ih ⊢` (not `split_ifs`) to reduce concrete `if` conditions, then `omega` | DescartesRuleOfSignsOQ02Parity |
| an auto-bound implicit `{n✝}` for the FIRST use of a name (`def f (H : G (Fin n) → Prop) (n : ℕ)`) collides with the later explicit `(n : ℕ)` → `Fin n✝` vs `Fin n` mismatch | reorder so the explicit `(n : ℕ)` binder comes FIRST | Erdos180Problem |
| `def Foo := ℕ → ℕ` / `Finset X` used where a class instance (`SemilatticeInf`/`Singleton`/`HasSubset`) is needed → synth fails through the `def` alias | `abbrev Foo := …` (reducible for instance search) | Erdos180Problem, Erdos216Problem |
| `Finset.inf' (by assumption) id` inside a `∀ … → (… ) → …` where the `Nonempty` proof is an earlier arrow (not in scope for `assumption`) | name the hypothesis: `∀ … (hne : s.Nonempty), … s.inf' hne id …` | Erdos180Problem |
| `RegularSingularSystem n S` "Application type mismatch: n has type ℕ but expected SingularPoints" (struct takes only `(S)`, `n` is a section var) | drop the stray leading arg: `RegularSingularSystem S` | Hilbert21RiemannHilbert |
| `⟨p, ‹_›⟩` anonymous-membership-proof in a `∀ p ∈ S, …` def → `assumption failed` (v4.31 doesn't name the `∈` binder for `‹_›`) | spell it out: `∀ p, ∀ hp : p ∈ S, … ⟨p, hp⟩ …` | Hilbert21RiemannHilbert |
| `Pairwise (Disjoint on f)` → `Disjoint on ?m has type Prop but expected a function` (`on` combinator elaboration) | `Pairwise (Function.onFun Disjoint f)` | Hilbert6PhysicsAxioms |
| `inner ψ φ` (Complex inner product) type-mismatch — `inner` takes the **scalar field first** | `inner ℂ ψ φ` (confirms §7v Erdos189) | Hilbert6PhysicsAxioms |
| `[MulAction G R] [MulDistribMulAction G R]` **redundant-instance diamond** → `smul_add`/`smul_mul_assoc`/`smul_one` "rewrite did not find pattern" (two `SMul G R` instances don't unify) | drop the redundant `[MulAction G R]`; for a group acting by ring automorphisms use `[MulSemiringAction G R]` (gives `smul_add`, `smul_mul'`, `smul_one` — faithful); `smul_mul_assoc`→`smul_mul'` | Hilbert14InvariantsOQ01 |
| `exp ℝ X` (`NormedSpace.exp`) → `exp ℝ has type Type` (Function expected) — the leading field arg was DROPPED | `exp X` (field inferred); `exp_add_of_commute` now additionally requires `[NormedAlgebra ℚ 𝔸]` — add it to the variable block (every ℝ-Banach-algebra is a ℚ-algebra, faithful) | Hilbert5OQ02 |
| `A + A` / `A - A` on `Set ℕ` → `failed to synthesize HAdd (Set ℕ) (Set ℕ) ?` | `open scoped Pointwise`; if the intended set is over ℤ (`(A - A : Set ℤ)` with `A : Set ℕ`), cast first via image: `(((↑) : ℕ → ℤ) '' A) - (((↑) : ℕ → ℤ) '' A)` | Erdos156Aristotle |
| `Nat.find_min h` used as a function (`h (proof)`) → `don't know how to synthesize implicit argument m` | `Nat.find_min` now needs the tested value explicit: `Nat.find_min h (hlt : m < Nat.find h)` — supply it (`refine ⟨val, …, ?_⟩; exact Nat.find_min h (show val < Nat.find h by omega)`) | Erdos114OQ01Problem |
| `Set.Finite.ncard_eq_toFinset_card'` (method, primed) "environment does not contain" | `Set.ncard_eq_toFinset_card s hs` (takes the set + `s.Finite`, gives `s.ncard = hs.toFinset.card`) | Erdos14UniqueSums (partial) |
| `Finset.offDiag_card` gives `#s*#s - #s`; goal `#s*(#s-1)`; `omega` can't equate (nonlinear) | supply the bridge `have : #s * (#s - 1) = #s * #s - #s := Nat.mul_pred _ _` then `omega` | Erdos14UniqueSums (partial) |

### §7z Increment 36 recipes (Doctor A–M)

| Symptom | Fix | Files |
|---------|-----|-------|
| `isNilpotent_of_ker_le_center f hf inferInstance` "Function expected"/extra arg | `IsNilpotent H` now instance-implicit — drop trailing `inferInstance`: `isNilpotent_of_ker_le_center f ?_` | AbelRuffiniOQ04OQ01OQ03 |
| `index_comap_of_surjective _ hf` rw "not type-correct under instances transparency" | pass `f` explicitly `(f := ConjAct.toConjAct.toMonoidHom)` and close by `.symm` (exact, not rw) | AbelRuffiniOQ04OQ01OQ03 |
| `Even.neg_one_pow` rw fails to match `(-1:ℤˣ)^n` (units power-instance diamond) | avoid it — `interval_cases` the bounded exponent var + `decide` the sign contradiction | AbelRuffiniOQ07Order6 |
| Multiset `{a, b}` literal not defeq-closed by trailing `rw` | append explicit `rfl` | AbelRuffiniOQ07Order6 |
| `Int.Coprime` / `Int.Coprime.mul_dvd_of_dvd_of_dvd` / `Int.dvd_gcd` unknown | `Int.isCoprime_iff_gcd_eq_one` (iff) + `IsCoprime.mul_dvd`/`IsCoprime.mul_left`; `Int.dvd_gcd`(Nat)→`Int.dvd_coe_gcd`(↑gcd) | BezoutIdentityOQ03OQ04, OQ04OQ01 |
| `Int.coe_nat_dvd` unknown | `Int.natCast_dvd_natCast` | BezoutIdentityOQ03OQ03 |
| `Int.gcd_eq_gcd_ab` gives `m*gcdA + n*gcdB` but goal wants `s*m + t*n` | `mul_comm` both terms before `.symm` | BezoutIdentityOQ03OQ04 |
| `Fintype (Fin (n+?m))` stuck — size param not inferable from a smaller-typed arg | supply the size implicit explicitly `(m := m)` at each application | BezoutIdentityOQ01OQ02OQ02Descent |
| `Fin.sum_univ_two` now emits `M 0 1` (OfNat literals) — old `rw [hEntry]` with `⟨0,_⟩` indices misses; matrix-literal entry `![…] ⟨0,_⟩` won't reduce | state helper hyps + `congr_fun` indices with LITERAL `(0:Fin k)`; add `Matrix.cons_val_fin_one`; when atoms are then defeq-literal, `linarith`→`exact h` | BezoutIdentityOQ04OQ01 |
| `simpa`/`convert` type-mismatch on a ℕ index expr (`m+j+2` vs `m+(j+1)+1`) + instLE/instPreorder diamond | add `have : m+j+2 = m+(j+1)+1 := by omega`, rw at hyp before simpa | BetaCentralBinomialExplicitRateOQ02 |
| `Matrix.charpoly_conj_of_isUnit` removed | `Matrix.charpoly_units_conj' hP.unit N` then `rw [hP.unit_spec]` (its `M.val⁻¹` is already the matrix inverse) | CayleyHamiltonMinpolyOQ02OQ03 |
| `minpoly_conj_of_isUnit` removed (similar-matrix minpoly invariance) | build conjugation AlgEquiv `MulSemiringAction.toAlgEquiv F _ (ConjAct.toConjAct hP.unit⁻¹)`, prove `e A = P⁻¹AP` via `ConjAct.units_smul_def`+`Matrix.coe_units_inv`, then `minpoly.algEquiv_eq` | CayleyHamiltonMinpolyOQ02OQ03 |

## §7ab Doctor increment 38 recipes (tm/pd/rewrite/unknown-const/instance-synth, N–Z + Erdos≥600, #38065, +10 GREEN)

| Symptom | Fix | File |
|---|---|---|
| `by decide` errors "Expected type must not contain free variables" | `by decide +revert` (auto-reverts free vars) | WaringGgLowerBoundsOQ02 |
| `have h : !χ T = false` type-mismatch → expected `!decide(χ T = false) = true` (`!` parsed as `Not` over the eq, not `Bool.not`) | write `Bool.not (χ T) = false` explicitly | RamseyHypergraph |
| `cases hc : χ T with \| true =>` leaves goal `true = true`, `exact hc` fails | close with `rfl` (scrutinee substituted) | RamseyHypergraph |
| `omega` can't close nonlinear-product Nat goals (`n*(n+1)/2 ≥ n`, `n*(n+1) > 0`) — was OK in v4.26 | `Nat.le_div_iff_mul_le` + `Nat.mul_le_mul_left k h` (k explicit) / `Nat.mul_pos` / `Nat.mul_div_cancel` | TriangularReciprocalsFigurate |
| `rpow_neg` / `rpow_natCast` unknown identifier | `Real.rpow_neg` / `Real.rpow_natCast` (not root-exported) | TriangularReciprocalsFigurate |
| `Finset.sum_Ico_consecutive _ …` → `AddCommMonoid ?m` stuck | function arg now explicit; pass the lambda `(fun j => …)` | SumOfKthPowersOQ03 |
| `EuclideanGeometry.angle_add_angle_add_angle_eq_pi h₂ h₃` arg-mismatch | now `(p₃ : P) (h : p₂ ≠ p₁)`: pass `p₃ h₂` | TriangleAngleSum |
| `taylor_mean_remainder_lagrange`/`_cauchy` type-mismatch (ℕ∞ vs WithTop ℕ∞; Icc vs uIcc; < vs ≠) | now `uIcc`/`uIoo` + `x₀ ≠ x`; `differentiableOn_iteratedDerivWithin` cast is `WithTop ℕ∞`; bridge `uIcc_of_le hx.le`/`uIoo_of_lt hx`/`hx.ne` | TaylorTheorem |
| `Polynomial.natDegree_eq_one` destructure `⟨a,b,ha,hfab⟩` fails | now `∃ a, a≠0 ∧ ∃ b, C a*X+C b = p` → `⟨a,ha,b,hfab⟩`; hfab RHS is `= p` (use `rw [← hfab]`); after `rw [ha1]` add `map_one` before `one_mul` | Sqrt2MinpolyOQ01 |
| `simp [aeval_esymm_eq]` unsolved — simp normalizes `MvPolynomial.aeval x`→`eval x` first | add `eval`-form bridge lemmas (`rw [← MvPolynomial.aeval_eq_eval, aeval_…]`) to simp set; `map_natCast` for aeval of natCast | VietasFormulasOQ03OQ01 |
| `(\|intExpr\| : ℚ)` — abs now elaborates IN ℚ (each var cast), `rw [h]` (h over ℤ) fails | bridge via `Int.cast_abs` + `push_cast` | PicksTheoremOQ01 |
| `decide` slow whnf-timeout on bounded-Nat ∀ | `set_option maxHeartbeats 4000000 in` (axiom-free; must precede the docstring) | TaxicabNumberOQ01 |

Statement repair: PicksTheoremOQ01 `picks_additivity` — added `hglue : 2*k+2 ≤ b₁+b₂` (ℕ truncated
subtraction made the original statement false; geometric gluing bound). No callers.

### §7ab Increment 38 (continued)

| Symptom | Fix | File |
|---|---|---|
| `HahnSeries.support_add_subset hq` app-type-mismatch (hq is Prop, expects HahnSeries) | now `(x y)` explicit + returns `⊆`: `support_add_subset _ _ hq` | PuiseuxTheorem |
| `by decide` "did not reduce to isTrue/isFalse", instance = `Classical.propDecidable`, file has `open scoped Classical` | replace with `rfl` / `refine ⟨rfl,…⟩` on concrete goals (Classical shadows the computable instance) | PicksTheoremOQ01OQ01 |
| old `zify [h]; Int.natAbs_of_nonneg (by omega)` breaks (omega sees metavar) | modern `omega` closes `((n:ℤ)-1).natAbs = n-1` directly | PicksTheoremOQ01OQ01 |
### §7ab Increment 39 recipes (Doctor-b A–M / Erdos<600)

| Symptom | Fix | Files |
|---------|-----|-------|
| `pi_gt_3141592` / `pi_lt_3141593` unknown identifier | renamed to digit-count form: `pi_gt_d6` (`3.141592 < π`) / `pi_lt_d6` (`π < 3.141593`); also `pi_gt_d2`/`pi_lt_d2` (3.14/3.15), `pi_gt_d4`/`pi_lt_d4`, `pi_gt_d20`/`pi_lt_d20`, `pi_gt_three`/`pi_lt_four`. In `Mathlib.Analysis.Real.Pi.Bounds` | AreaOfCircleOQ01OQ02OQ01OQ03, BuffonsNeedleOQ01OQ02 (blocked by other errs) |
| `rw [← integral_ofReal]` fails on a SET integral (`∫ x in s, …`) "did not find pattern" | two `integral_ofReal` now exist: Bochner `_root_.integral_ofReal : ∫ ↑f = ↑(∫ f)` and `intervalIntegral.integral_ofReal` (only `a..b`); a bare name resolves to the interval one. Use `_root_.integral_ofReal (f := …)` for set integrals; note orientation is now `∫ ↑f = ↑(∫ f)` | AreaOfCircleOQ07OQ04OQ01 |
| `setIntegral_prod_mul` "did not find pattern … ∂Measure.prod ?m ?m" (target has `∂volume`) | measure must be literally `μ.prod ν`; prefix `rw [Measure.volume_eq_prod ℝ ℝ, setIntegral_prod_mul …]` (also `integral_prod_mul` needs `volume_eq_prod`) | AreaOfCircleOQ07OQ04OQ01 |
| def `Foo {G α …} [SMul G α] …` where `G` doesn't appear in an arg type → every use "typeclass instance problem is stuck: SMul ?m α" | pin the phantom type param at every occurrence (conclusion + hypotheses) with named arg `Foo (G := G) …` | BorsukUlamOQ02OQ02 |
| `push_neg at h` where `h : ¬ Nonempty α` → now yields `h : IsEmpty α` (not `α → False`); old `h (Classical.arbitrary α)` breaks ("Function expected") | if the statement is genuinely false on the empty case (const-map ⟹ fixed-point needs a point), add `[Nonempty α]` and use `Classical.arbitrary α` directly | BorsukUlamOQ02OQ02 |
| FREE-GREEN detection: ledger row RESIDUAL but source already fixed by a prior commit | grep the flagged `unknown-const:X` leaf in the source file; if absent, `lake build` it — often EXIT 0 already; flip with no edit. Worth a full-partition sweep | CauchyInterlacing*, Erdos265Problem |
| `omega` can't prove a `Nat.choose _ 2` identity (`choose_two_right = n*(n-1)/2` is nonlinear+division) | expand `Nat.add_choose_eq` over `antidiagonal 2` via `Finset.Nat.sum_antidiagonal_succ` (twice) + `Finset.Nat.antidiagonal_zero`, then `Nat.choose_one_right`/`ring` | BinomialTheoremOQ02OQ02 |
| `pascal_from_vandermonde : C(m+1,r)=C(m,r)+C(m,r-1)` FALSE at r=0 (ℕ truncation `0-1=0`) | restate unconditionally shifted: `C(m+1,r+1)=C(m,r+1)+C(m,r)`, prove `rw [Nat.choose_succ_succ, Nat.add_comm]` | BinomialTheoremOQ02OQ02 |

### §7ac Increment 39 recipes (batch 2)

| Symptom | Fix | Files |
|---------|-----|-------|
| `Sym2.mk (x, y)` "Application type mismatch … has type α×α → Sym2 (α×α)" | `Sym2.mk` is now CURRIED `(a b : α)`; use notation `s(x, y)` (or `Sym2.mk x y`) | Erdos166Problem |
| `linarith [show P by <tactic block spanning lines>]` "unexpected identifier; expected ']'" | hoist the `show … by …` term to a preceding `have h : P := …` and pass `linarith [h]` | Erdos166Problem |
| statement uses real exponent `x ^ (A:ℝ)`/`x ^ (β:ℝ)` (rpow) but a hyp/axiom states `x ^ (4:ℕ)` (npow) → "Type mismatch ^(4:ℝ) vs ^(4:ℕ)" | bridge with `Real.rpow_natCast`: `have : x^(4:ℝ)=x^(4:ℕ) := by rw [← Real.rpow_natCast]; norm_num` then `rw` before applying | Erdos166Problem |
| broken anon-ctor field `symm.symm :=` (a mangled auto-edit) "invalid {...} notation" | the field is just `symm` — drop the extra `.symm` | Erdos159Problem |
| `G.adj_comm.mp` / `from G.adj_comm` — "Function.mp does not exist" / iff expected | `SimpleGraph.adj_comm` is now fully `∀ u v` → supply args: `G.adj_comm x y`, `(G.adj_comm _ _).mp` | Erdos159Problem |
| `Finset.mem_singleton.mp hu ▸ Finset.mem_singleton.mp hv` ▸-chain breaks | build the eq directly: `(Finset.mem_singleton.mp hu).trans (Finset.mem_singleton.mp hv).symm` | Erdos159Problem |
| `interval_cases k <;> simp only [Fin.ext_iff] at … <;> omega` → "simp made no progress" on the vacuous (too-few-vertices) cases | guard: `<;> first | (simp only [Fin.ext_iff] at …; omega) | omega` | Erdos159Problem |
| `pow_lt_pow_of_lt_one` unknown identifier | `pow_lt_pow_right_of_lt_one₀ (h₀ : 0<a) (h₁ : a<1) (hmn : m<n) : a^n < a^m` (in `Algebra.Order.GroupWithZero.Basic`) | Erdos120Problem |
| `isBounded_Icc (a := …) (b := …)` unknown / named-arg | now `Metric.isBounded_Icc (a b : α)` with EXPLICIT positional args: `Metric.isBounded_Icc 0 1` | Erdos120Problem |
| after `ring_nf`, `rw [mul_div_mul_left …]` "did not find pattern a*?/(a*?)" (ring_nf turned `/` into `⁻¹`) | avoid ring_nf; pre-rewrite numerator & denominator into `a*(…)` form via `show … from by ring`, then `mul_div_mul_left` | Erdos120Problem |
| `push_neg at h` where `h : ¬ (someDef …)` → "push Not made no progress" | `unfold someDef at h` (or `simp only [someDef] at h`) before `push_neg` | Erdos120Problem |
| `not_not (avoidable A)` "Function expected" (not_not is now an `Iff`) | `rw [← not_not (a := avoidable A)]` (named implicit) or bare `rw [← not_not]` | Erdos120Problem |

### §7ad Doctor increment 45 recipes (Doctor-b A–M / Erdos<600, #38065, +7 GREEN)

| Symptom | Fix | Files |
|---------|-----|-------|
| `Λ` (capital lambda) as a user abbrev name → `unexpected token 'Λ'; expected identifier` | `Λ` is now a RESERVED token like `λ`; rename the abbrev (e.g. `abbrev vonM := ArithmeticFunction.vonMangoldt`) and every code use-site (leave comments) | BoundedPrimeGapsOQ04 |
| `Nat.totient_pos hq` "Function expected" | `Nat.totient_pos` is now an `Iff` (`0 < φ n ↔ 0 < n`); use `Nat.totient_pos.mpr hq` | BoundedPrimeGapsOQ04, BoundedPrimeGapsOQ04OQ02 |
| `div_pos` "ambiguous [_root_.div_pos, Nat.div_pos]" on ℝ goal | `_root_.div_pos` | BoundedPrimeGapsOQ04OQ02 |
| `Nat.cast_nonneg` (no arg) type-mismatch `∀ n, 0 ≤ ↑n` vs `0 ≤ ↑x` | supply the arg: `Nat.cast_nonneg _` | BoundedPrimeGapsOQ04OQ02 |
| `Polynomial.descPochhammer` / `Polynomial.descPochhammer_succ_right` "Unknown constant" | `descPochhammer` moved OUT of the `Polynomial` namespace to top-level; drop the prefix (`descPochhammer`, `descPochhammer_succ_right`) | BinomialTheoremOQ01 |
| `EMetric.ball` / `EMetric.mem_ball` deprecated; `rw [EMetric.mem_ball]` "did not find pattern Metric.eball" | rename to `Metric.eball` and `Metric.mem_eball` (both `eball`/`mem_eball` live in the `Metric` namespace, NOT `EMetric`) | BinomialTheoremOQ01 |
| `rw [edist_zero_right]` then old NNReal-coe proof fails; goal is now `‖x‖ₑ < ↑1` | `edist_zero_right` now yields `‖·‖ₑ` (enorm); close with `simpa [enorm_eq_nnnorm, ← ENNReal.coe_one, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe] using hx` | BinomialTheoremOQ01 |
| `apply h1.congr; intro k` where `HasSum.congr` now gives a Finset-partial-sum goal (`k : Finset ℕ`, `∑ x_1 ∈ k, …`) | avoid `.congr`; prove the two summand functions equal via `have hfun : (fun n => …) = (fun k => …) := by funext k; …` then `rwa [hfun] at h1` | BinomialTheoremOQ01 |
| `floor_eq_iff.mpr` "Unknown constant" for ℤ floor (`round_eq` → `⌊x + 1/2⌋`) | `Int.floor_eq_iff.mpr` (no side condition; the ℤ version is `⌊a⌋ = z ↔ ↑z ≤ a ∧ a < z+1`) | DerangementsConvergenceOQ03 |
| `div_le_iff₀` rewrite produces `≤ 1/b * a` but calc/target wants `≤ a * (1/b)` | insert `by rw [mul_comm]; exact hrate` at the calc step | DerangementsConvergenceOQ03 |
| local `theorem foo` used BEFORE its definition in the same file → "Unknown identifier `foo`" | reorder: move the definition above its first use-site (forward refs are hard errors) | CombinationsFormulaOQ02Aristotle (moved `choose_2n_succ`) |
| `Nat.coprime_succ_self` removed | consecutive coprimality: `rw [show m+2=(m+1)+1 from rfl, Nat.coprime_self_add_right]; exact Nat.coprime_one_right _` | CombinationsFormulaOQ02Aristotle |
| `omega` fails on a `Nat.choose (2m+2) …` Pascal identity: `@Nat.choose_succ_succ` produces `succ`-form atoms omega can't unify with `2*m+2` | state each Pascal step as an explicit `have` using `Nat.choose_succ_succ'` (the `+1` form), normalize `m-1+1=m` via `rw`, then `omega` | CombinationsFormulaOQ02Aristotle |
| `Nat.mul_le_mul_left _ (Nat.le_succ n)` produces a `sorry` metavar (arg-shape drift) | for `a*(n+1) - a*n = a`: `rw [Nat.mul_succ]; omega` | CombinationsFormulaOQ02Aristotle |
| `hev.comp_tendsto htends` "Invalid field notation" (`Filter.Eventually.comp_tendsto` REMOVED; type shows as `atTop.1 {x | …}`) | pull back along the tendsto: `have htends : Tendsto (fun x => t*x) atTop atTop; filter_upwards [hev, htends.eventually hev] with …` | CentralLimitTheoremOQ03OQ01 |
| `tendsto_const_mul_atTop_of_pos ht tendsto_id` "Function expected" | now an `Iff`; `(tendsto_const_mul_atTop_of_pos ht).mpr tendsto_id` | CentralLimitTheoremOQ03OQ01 |
| `this.symm` on a `=ᶠ[l]` (EventuallyEq) value "Invalid field notation" (shows as `atTop.1 {…}`) | dot-notation can't find the `EventuallyEq` namespace through the reduced `Eventually`; use `Filter.EventuallyEq.symm this` explicitly | CentralLimitTheoremOQ03OQ01 |
| after `convert … using 1` closes fully, trailing `ext x; ring` → "No goals to be solved" | drop the trailing tactic (convert now discharges) | CentralLimitTheoremOQ03OQ01, DerangementsConvergenceOQ03 (drop `ring`), BinomialTheoremOQ01 |
| FREE-GREEN: sibling `*Aristotle` companion RESIDUAL but builds EXIT 0 (transitive dep already fixed) | flip ledger with no edit | CentralLimitTheoremOQ03OQ01Aristotle |

### §7ae Doctor increment 47 recipes (Doctor-b A–M / Erdos<600, #38065, +4 GREEN)

- **Output-only implicit type-class param = stuck metavar in v4.31.** A `def`/`theorem`
  whose type variable (e.g. `𝕜` in `[RCLike 𝕜]`) appears ONLY in the body / return type and
  never in an explicit argument now fails with `typeclass instance problem is stuck /
  InnerProductSpace ?m E (first and third args are metavars)` at every USE site. Fix: make the
  type an EXPLICIT named parameter of the def (`def foo (𝕜 : Type*) [RCLike 𝕜] {E …} … `) and
  supply it at all call sites. NOTE: `foo (𝕜 := 𝕜)` named-arg pinning FAILS ("Invalid argument
  name 𝕜") for auto-bound-implicit vars — must restructure the binder. (CauchySchwarzOQ01OQ01OQ01)
- **`Ico 1 (n+1)` index-type leak.** Inside a sum whose body is ℤ/ℚ-valued, `Ico 1 (n+1)`
  elaborates its bounds at the body's field → `HAdd ℕ ℕ ℤ` / `LocallyFiniteOrder ℚ` synth
  failures. Pin the index type: `Ico (1 : ℕ) (n+1)`. (ArithmeticSeriesOQ00OQ02OQ01)
- **`Polynomial.content` / `IsPrimitive.mul` / `Polynomial.content_mul` need
  `[NormalizedGCDMonoid R]`** (v4.31), not bare `[GCDMonoid R]`. Widen the typeclass constraint.
  Also `Polynomial.content_mul` now takes its polynomial args IMPLICITLY (`content_mul` not
  `content_mul f g`). (BezoutIdentityOQ02OQ04)
- **`Nat.one_le_succ` removed** → `Nat.succ_le_succ (Nat.zero_le _)` (or `Nat.succ_pos`/`by omega`).
- **`lgvDet_nonneg` (BallotProblemOQ03) gained order hyps** `(ha hb ha₁ ha₂ ha₂₁)`; downstream
  wrappers must add the missing ordering hypotheses to their statement (intended-true strengthening).
- **`RCLike.norm_ofReal` can loop in `simp`.** For `‖(↑(‖v‖^2) : 𝕜)‖`: recast
  `(‖v‖^2 : 𝕜) = ((‖v‖^2 : ℝ) : 𝕜)` (`by push_cast; ring`) then `rw [RCLike.norm_ofReal,
   abs_of_nonneg (by positivity)]`. `RCLike.norm_conj` for `‖conj c‖ = ‖c‖`.
- **Cast-of-power/product `choose` goals**: `push_cast; ring` closes `↑(a^2) - ↑(x*y)` vs
  `↑a^2 - ↑y*↑x` once the `Nat`-arith `choose` indices are normalized via omega-`show`s.
- **CAUTION**: low reported error count (4) ≠ mechanical. Lean stops at the first blocking error
  per decl; clearing it can surface a cluster of genuine drift (AmgmInequalityOQ02OQ01OQ02OQ01OQ03:
  4 reported → 6+ real induction-drift sites). Probe by fixing the head error and re-counting
  before committing to a file.

## §7af — Increment 52 recipes (N–Z / Erdos≥600 deep-rework)

- **`LpAddConst` / `LpAddConst_of_one_le` moved to the `ENNReal` namespace.** Unqualified or
  `MeasureTheory.LpAddConst*` now fail (`Function expected` / `unknown-const`). Qualify:
  `ENNReal.LpAddConst`, `ENNReal.LpAddConst_of_one_le`. (`eLpNorm_add_le'` stays
  `MeasureTheory.eLpNorm_add_le'`.) The Mathlib file that uses them just does `open … ENNReal`.
- **`omit … in` must PRECEDE a docstring, not follow it.** In v4.31 `/-- doc -/` immediately
  before `omit h in theorem …` errors `unexpected token 'omit'; expected 'lemma'` (the docstring
  is orphaned). Reorder to `omit h in` then `/-- doc -/` then the declaration.
- **Euler partition theorem moved Archive→mainline.** `Theorems100.partition_theorem` lived in
  `Archive/Wiedijk100Theorems/Partition.lean` (NOT reachable via `import Mathlib`). Now mainline:
  `Nat.Partition.card_odds_eq_card_distincts (n) : #(odds n) = #(distincts n)`
  (Mathlib.Combinatorics.Enumerative.Partition.Glaisher). For `#(distincts n) = #(odds n)` use
  `.symm`. Related: `Nat.Partition.odds n = restricted n (¬Even ·)`; to reduce membership to
  `∀ i ∈ p.parts, ¬Even i`, `simp [Nat.Partition.odds, Nat.Partition.restricted]` — do NOT rewrite
  `¬Even`→`Odd` (the def is stated with `¬Even`, so it re-loops).
- **`chromaticNumber` ambiguity.** With `open GraphCore SimpleGraph`, `chromaticNumber` resolves
  to both `SimpleGraph.chromaticNumber : ℕ∞` and the project's `GraphCore.chromaticNumber : ℕ`
  (`Ambiguous term`). Qualify to the intended one (usually `GraphCore.chromaticNumber`, matched to
  `cliqueNumber : ℕ`).
- **Project-namespace `open` needs the defining file imported.** `open InformationTheory.BinaryEntropy`
  is a PROJECT namespace (Mathlib removed its own binaryEntropy); `h` (binary entropy) lives in
  `Proofs.ShannonChannelCodingOQ04`. Companions that only `import Mathlib` get `unknown namespace`
  + `Function expected` on `h`; add `import Proofs.ShannonChannelCodingOQ04`.
- **Type-valued `theorem` now rejected.** `theorem f … : T` where `T : Type _` (e.g. returns a
  `structure` like `KRep A k n`) errors `type of theorem … is not a proposition`. Make it a `def`.
  (Often the body can be a real term, discharging any sorry — e.g. re-bundle the structure fields
  and thread the hypothesis through the `Prop`-valued fields.)
- **`Nontrivial (ℤ√d)` lost its instance (regression, NOT a rename).** `IsDomain (ℤ√d)` no longer
  synthesizes (the global `Zsqrtd` instance calls `NoZeroDivisors.to_isDomain _` which needs
  `Nontrivial`). Blocks `PrincipalIdealRing.to_uniqueFactorizationMonoid` and any UFD/prime chain
  on `ℤ√d`. `EuclideanDomain.to_principal_ideal_domain` (PID half) still works under a local
  `letI := euclideanDomain …`. Full fix needs `Nontrivial (ℤ√d)` reconstructed — deep.
- **FREE-GREENS:** re-probe RESIDUAL files whose ONLY errors were in deps (own=0) — several now
  build clean as earlier increments greened their deps (this increment:
  QuadraticReciprocityAlgorithmOQ03FieldBridge, Erdos620ProblemAristotle). A `PASS` with no source
  edit is a legitimate flip.

### §7af addenda (inc52 second half)

- **`deriving DecidableEq` on a struct with `ℝ` (or other noncomputable-DecidableEq) fields now
  fails to COMPILE.** `deriving DecidableEq` errors `failed to compile definition, consider marking
  it as 'noncomputable' … depends on 'decidableEq'`. Fix: drop the `deriving` clause and add
  `noncomputable instance : DecidableEq T := Classical.decEq _`. Downstream `Finset T` still works.
- **Well-founded recursion no longer auto-inferred for `Nat.log`-style descent.** A `def f : ℕ → ℕ`
  with a recursive call `f (Nat.log b (n+…))` errors `fail to show termination`. Add
  `termination_by n => n` and `decreasing_by exact Nat.log_lt_self b (by omega)`.
- **UNSOUND-placeholder files are NOT migration seams** (skip, don't force-green): e.g. Erdos807
  (`ERW_conjecture := True` ⇒ `¬∀n, True` unprovable), TestApi241's original `{1,2,4,8}` B3 claim.
  For TestApi241 the fix was a genuine STATEMENT REPAIR to a true witness `{1,4,16,64}` — do that only
  when a true correction is clear; otherwise leave the file RESIDUAL.

## Recurring seams (added 2026-07-16 from Erdos864Problem, ~15+ hits/file)
- **Anonymous-constructor associativity**: v4.31's elaborator no longer auto-flattens mixed-associativity
  conjunctions. For a goal `(a∈A∧b∈A)∧R`, `exact ⟨a,b,ha,hb,rfl⟩` BUILDS wrong — write nested
  `⟨⟨ha,hb⟩,hab⟩`. (Destructuring `obtain` is more forgiving than construction.)
- **`Finset.card_le_one.mp`** now needs explicit element witnesses: `hle.mp (a,b) hp1 (c,d) hp2`, not
  `hle hp1 hp2`.
