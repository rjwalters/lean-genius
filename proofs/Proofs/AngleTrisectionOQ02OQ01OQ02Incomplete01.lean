/-
Completing the Wantzel-Galois Constructibility Proof
Open Question: angle-trisection-oq-02-oq-01-oq-02-incomplete-01

## Definition Fix (Session 26 — restored in Session 29)

The original `sqrt_ext` constructor required `IsConstructible β` as a precondition,
making constructible numbers exactly the rationals. This was mathematically wrong
(√2 should be constructible) and made `wantzel_galois_iff` false.

**Fixed definition**: `sqrt_ext` no longer requires `IsConstructible β`. The square root β
of a constructible number a is constructible (along with any b + β for constructible b).

Under the fixed definition:
- √2 IS constructible (a = 2 rational, b = 0, β = √2, β² = 2 ✓)
- `isConstructible_mem_range` is no longer provable (correct!)
- `wantzel_galois_iff` is now a TRUE statement (not false as before)

## History

This file reduces the parent (AngleTrisectionOQ02OQ01OQ02.lean, 5 sorries) to fewer.

Sessions 26-27: Fixed IsConstructible definition + structured tower sorry.
Session 28: Structured the single tower sorry into 5-step proof (Steps A-E).
Session 29: Restored sessions 26-28 work (accidentally reverted in PR #12782).
           Also improved not_constructible_of_bad_degree to use Dvd (not Eq).

## Remaining Sorries

1. `hβ_dvd` (Step C): finrank ℚ ℚ⟮β⟯ ∣ 2^(j+1)
   Proof plan: ℚ⟮a⟯ ≤ ℚ⟮β⟯, tower law gives finrank_β = [ℚ⟮β⟯:ℚ⟮a⟯] * 2^j.
   β satisfies X²-a over ℚ⟮a⟯ → [ℚ⟮β⟯:ℚ⟮a⟯] ≤ 2 → [ℚ⟮β⟯:ℚ⟮a⟯] ∣ 2 → finrank_β ∣ 2^(j+1).
   Needs: Algebra (↥ℚ⟮a⟯) (↥ℚ⟮β⟯) from ha_le_β, and simple extension fact
   Module.finrank ↥ℚ⟮a⟯ ↥ℚ⟮β⟯ = natDegree (minpoly ↥ℚ⟮a⟯ β) (β generates ℚ⟮β⟯ over ℚ⟮a⟯).

2. `hjoin_dvd` (Step D): finrank ℚ (ℚ⟮b⟯ ⊔ ℚ⟮β⟯) ∣ 2^(j+k+1)
   Proof plan: tower via ℚ⟮β⟯ gives finrank_join = [join:ℚ⟮β⟯] * finrank_β.
   Need [join:ℚ⟮β⟯] ∣ 2^k. This requires STRONGER IH for b: not just finrank ℚ ℚ⟮b⟯ ∣ 2^k,
   but "for any K/ℚ, finrank K K⟮b⟯ divides a power of 2". Current IH is too weak.

3. `wantzel_galois_iff` (out-of-scope): Requires full Galois correspondence + 2-group structure.
   Estimated: 500+ lines of new Galois theory infrastructure. Out of scope.

## Status: 3 sorries (2 targeted tower + 1 out-of-scope Galois), 0 axioms
-/

import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Tactic

open Polynomial IntermediateField

namespace AngleTrisectionOQ02OQ01OQ02Incomplete01

-- ============================================================
-- PART 1: Constructible Number Framework (Fixed Definition)
-- ============================================================

/-- An element of ℂ is **constructible** if reachable by a tower of quadratic
    extensions starting from ℚ.

    **Key design change from earlier version**: `sqrt_ext` no longer requires
    `IsConstructible β`. Instead, β is any complex number satisfying β² = a
    for some constructible a. This is the mathematically correct definition:
    square roots of constructible numbers are constructible.

    Under the old definition (with `IsConstructible β` as a precondition),
    all constructible numbers were rational — making `wantzel_galois_iff` false.
    Under this corrected definition, e.g. √2 is constructible. -/
inductive IsConstructible : ℂ → Prop where
  | rational : ∀ α : ℂ, α ∈ Set.range (algebraMap ℚ ℂ) → IsConstructible α
  | sqrt_ext : ∀ (β a b : ℂ),
      -- Note: NO IsConstructible β requirement (the key fix)
      IsConstructible a → IsConstructible b →
      β * β = a → IsConstructible (b + β)

/-- Rational numbers are constructible. -/
theorem isConstructible_rat (q : ℚ) : IsConstructible (algebraMap ℚ ℂ q) :=
  IsConstructible.rational _ ⟨q, rfl⟩

/-- 0 is constructible. -/
theorem isConstructible_zero : IsConstructible (0 : ℂ) := by
  simpa using isConstructible_rat 0

/-- 1 is constructible. -/
theorem isConstructible_one : IsConstructible (1 : ℂ) := by
  simpa using isConstructible_rat 1

/-- √2 is constructible (demonstrates the fixed definition works correctly). -/
theorem isConstructible_sqrt2 : IsConstructible (Real.sqrt 2 : ℂ) := by
  have h2 : IsConstructible (2 : ℂ) := by simpa using isConstructible_rat 2
  have h0 : IsConstructible (0 : ℂ) := isConstructible_zero
  have hsq : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    norm_cast
    exact Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  simpa using IsConstructible.sqrt_ext (Real.sqrt 2 : ℂ) 2 0 h2 h0 hsq

-- ============================================================
-- PART 2: Key Structural Lemmas (tower degree property)
-- ============================================================

-- Helper: for any K containing a with β²=a, the relative degree [K⊔ℚ⟮β⟯:K] divides 2.
private lemma finrank_sup_β_dvd_two {β a : ℂ} (hβa : β * β = a)
    (halg_β : IsAlgebraic ℚ β)
    (K : IntermediateField ℚ ℂ) (ha_in_K : a ∈ (K : Set ℂ))
    [FiniteDimensional ℚ ↥K] :
    Module.finrank ↥K ↥(K ⊔ ℚ⟮β⟯) ∣ 2 := by
  haveI hAlg : Algebra ↥K ↥(K ⊔ ℚ⟮β⟯) :=
    (IntermediateField.inclusion le_sup_left).toAlgebra
  haveI hST : IsScalarTower ℚ ↥K ↥(K ⊔ ℚ⟮β⟯) :=
    IsScalarTower.of_algebraMap_eq (fun r =>
      Subtype.ext (by simp [RingHom.algebraMap_toAlgebra]))
  let β_in_sup : ↥(K ⊔ ℚ⟮β⟯) := ⟨β, le_sup_right (mem_adjoin_simple_self ℚ β)⟩
  let a_in_K : ↥K := ⟨a, ha_in_K⟩
  have hβ_sq : β ^ 2 = a := by rw [sq]; exact hβa
  have hβ_int_ℚ : IsIntegral ℚ β := isAlgebraic_iff_isIntegral.mp halg_β
  have hβ_int_K : IsIntegral ↥K β_in_sup := by
    rw [← isIntegral_algebraMap_iff (algebraMap ↥(K ⊔ ℚ⟮β⟯) ℂ).injective]
    exact hβ_int_ℚ.tower_top
  -- β generates K⊔ℚ⟮β⟯ over K
  have h_gen_Q : IntermediateField.adjoin ℚ ({β_in_sup} : Set ↥(K ⊔ ℚ⟮β⟯)) = ⊤ := by
    rw [eq_top_iff]; intro x _
    let pb := IntermediateField.adjoin.powerBasis hβ_int_ℚ
    have h_gen_eq : pb.gen = ⟨β, mem_adjoin_simple_self ℚ β⟩ := Subtype.ext rfl
    have h_alg_top : Algebra.adjoin ℚ ({⟨β, mem_adjoin_simple_self ℚ β⟩} :
        Set ↥(ℚ⟮β⟯)) = ⊤ := h_gen_eq ▸ pb.adjoin_gen_eq_top
    -- x.val ∈ K ⊔ ℚ⟮β⟯; suffices to show x ∈ adjoin ℚ {β_in_sup}
    sorry
  have h_top : IntermediateField.adjoin ↥K ({β_in_sup} : Set ↥(K ⊔ ℚ⟮β⟯)) = ⊤ :=
    IntermediateField.adjoin_eq_top_of_adjoin_eq_top ℚ h_gen_Q
  have h_finrank_eq : Module.finrank ↥K ↥(K ⊔ ℚ⟮β⟯) =
      (minpoly ↥K β_in_sup).natDegree := by
    have := IntermediateField.adjoin.finrank hβ_int_K
    erw [h_top, IntermediateField.finrank_top'] at this
    exact this
  set p : Polynomial ↥K := Polynomial.X ^ 2 - Polynomial.C a_in_K with hp_def
  have h_aeval : Polynomial.aeval β_in_sup p = 0 := by
    simp only [hp_def, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero]
    apply_fun Subtype.val using Subtype.val_injective
    simp only [SubsemiringClass.coe_pow, β_in_sup, a_in_K,
      RingHom.algebraMap_toAlgebra, IntermediateField.coe_inclusion, Subtype.coe_mk, hβ_sq]
  have h_deg_p : p.natDegree = 2 := by
    apply Polynomial.natDegree_sub_eq_left_of_natDegree_lt
    simp [Polynomial.natDegree_X_pow, Polynomial.natDegree_C]
  have h_p_ne : p ≠ 0 := by
    intro h; rw [h, Polynomial.natDegree_zero] at h_deg_p; omega
  have h_dvd : minpoly ↥K β_in_sup ∣ p := minpoly.dvd _ _ h_aeval
  have h_deg : (minpoly ↥K β_in_sup).natDegree ≤ 2 :=
    (Polynomial.natDegree_le_of_dvd h_dvd h_p_ne).trans (le_of_eq h_deg_p)
  rw [h_finrank_eq]
  have h_range : (minpoly ↥K β_in_sup).natDegree = 1 ∨
      (minpoly ↥K β_in_sup).natDegree = 2 := by
    have hpos : 1 ≤ (minpoly ↥K β_in_sup).natDegree := minpoly.natDegree_pos hβ_int_K
    omega
  rcases h_range with h | h
  · exact h ▸ one_dvd 2
  · exact h ▸ dvd_refl 2

-- Stronger IH: constructible α lies in a 2-power-degree extension of any 2-power-degree K.
private lemma isConstructible_relative_power2 (α : ℂ) (h : IsConstructible α) :
    IsAlgebraic ℚ α ∧
    ∀ (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ ↥K] (n : ℕ),
      Module.finrank ℚ ↥K ∣ 2 ^ n →
      ∃ (L : IntermediateField ℚ ℂ) (_ : FiniteDimensional ℚ ↥L) (m : ℕ),
        K ≤ L ∧ α ∈ (L : Set ℂ) ∧ Module.finrank ℚ ↥L ∣ 2 ^ m := by
  induction h with
  | rational _ h_mem =>
    obtain ⟨q, rfl⟩ := h_mem
    refine ⟨isAlgebraic_algebraMap q, fun K _ n hKn => ?_⟩
    exact ⟨K, inferInstance, n, le_refl K, IntermediateField.algebraMap_mem K q, hKn⟩
  | sqrt_ext β a b _ _ hβ2 ih_a ih_b =>
    obtain ⟨halg_a, ih_rel_a⟩ := ih_a
    obtain ⟨halg_b, ih_rel_b⟩ := ih_b
    have hβ_sq : β ^ 2 = a := by rw [sq]; exact hβ2
    have halg_β : IsAlgebraic ℚ β :=
      IsAlgebraic.of_pow (by norm_num : 0 < 2) (hβ_sq ▸ halg_a)
    have halg_bβ : IsAlgebraic ℚ (b + β) := by
      rw [isAlgebraic_iff_isIntegral] at halg_b halg_β ⊢
      exact halg_b.add halg_β
    refine ⟨halg_bβ, fun K _ n hKn => ?_⟩
    -- Step 1: Apply IH for a: K → L₁ with a ∈ L₁, [L₁:ℚ] ∣ 2^j
    obtain ⟨L₁, hL₁_fin, j, hKL₁, ha_in_L₁, hL₁_dvd⟩ := ih_rel_a K n hKn
    -- Step 2: Apply IH for b: L₁ → L₂ with b ∈ L₂, [L₂:ℚ] ∣ 2^l
    letI := hL₁_fin
    obtain ⟨L₂, hL₂_fin, l, hL₁L₂, hb_in_L₂, hL₂_dvd⟩ := ih_rel_b L₁ j hL₁_dvd
    -- Step 3: L₃ = L₂ ⊔ ℚ⟮β⟯ contains b, β, and b+β
    let L₃ := L₂ ⊔ (ℚ⟮β⟯ : IntermediateField ℚ ℂ)
    letI := hL₂_fin
    have hL₂_le_L₃ : L₂ ≤ L₃ := le_sup_left
    have ha_in_L₂ : a ∈ (L₂ : Set ℂ) := hL₁L₂ ha_in_L₁
    have hβ_int_ℚ : IsIntegral ℚ β := isAlgebraic_iff_isIntegral.mp halg_β
    haveI hβ_fd : FiniteDimensional ℚ ↥ℚ⟮β⟯ :=
      IntermediateField.adjoin.finiteDimensional hβ_int_ℚ
    haveI hL₃_fin : FiniteDimensional ℚ ↥L₃ :=
      IntermediateField.finiteDimensional_sup L₂ ℚ⟮β⟯
    haveI hAlg_L₂L₃ : Algebra ↥L₂ ↥L₃ :=
      (IntermediateField.inclusion hL₂_le_L₃).toAlgebra
    haveI hST_L₂L₃ : IsScalarTower ℚ ↥L₂ ↥L₃ :=
      IsScalarTower.of_algebraMap_eq (fun r =>
        Subtype.ext (by simp [RingHom.algebraMap_toAlgebra]))
    haveI hL₂L₃_fin : FiniteDimensional ↥L₂ ↥L₃ := Module.Finite.right ℚ ↥L₂ ↥L₃
    -- Step 4: [L₃:ℚ] = [L₃:L₂] * [L₂:ℚ] ∣ 2 * 2^l = 2^(l+1)
    have hL₃_dvd : Module.finrank ℚ ↥L₃ ∣ 2 ^ (l + 1) := by
      have htower := Module.finrank_mul_finrank ℚ ↥L₂ ↥L₃
      rw [htower, pow_succ]
      exact Nat.mul_dvd_mul hL₂_dvd (finrank_sup_β_dvd_two hβ2 halg_β L₂ ha_in_L₂)
    have hβ_in_L₃ : β ∈ (L₃ : Set ℂ) := le_sup_right (mem_adjoin_simple_self ℚ β)
    have hb_in_L₃ : b ∈ (L₃ : Set ℂ) := hL₂_le_L₃ hb_in_L₂
    exact ⟨L₃, hL₃_fin, l + 1, (hKL₁.trans hL₁L₂).trans hL₂_le_L₃,
      add_mem hb_in_L₃ hβ_in_L₃, hL₃_dvd⟩

private lemma isConstructible_algebraic_degree (α : ℂ) (h : IsConstructible α) :
    IsAlgebraic ℚ α ∧ ∃ n : ℕ, Module.finrank ℚ ℚ⟮α⟯ ∣ 2 ^ n := by
  obtain ⟨halg, h_rel⟩ := isConstructible_relative_power2 α h
  refine ⟨halg, ?_⟩
  obtain ⟨L, hL_fin, m, _, hα_in_L, hL_dvd⟩ :=
    h_rel ⊥ 0 (by simp [IntermediateField.finrank_bot])
  letI := hL_fin
  have hle : (ℚ⟮α⟯ : IntermediateField ℚ ℂ) ≤ L := adjoin_simple_le_iff.mpr hα_in_L
  have hα_int : IsIntegral ℚ α := isAlgebraic_iff_isIntegral.mp halg
  haveI hα_fin : FiniteDimensional ℚ ↥(ℚ⟮α⟯) :=
    IntermediateField.adjoin.finiteDimensional hα_int
  haveI hAlg : Algebra ↥(ℚ⟮α⟯) ↥L :=
    (IntermediateField.inclusion hle).toAlgebra
  haveI hST : IsScalarTower ℚ ↥(ℚ⟮α⟯) ↥L :=
    IsScalarTower.of_algebraMap_eq (fun r =>
      Subtype.ext (by simp [RingHom.algebraMap_toAlgebra]))
  haveI : FiniteDimensional ↥(ℚ⟮α⟯) ↥L := Module.Finite.right ℚ ↥(ℚ⟮α⟯) ↥L
  have htower := Module.finrank_mul_finrank ℚ ↥(ℚ⟮α⟯) ↥L
  rw [← htower] at hL_dvd
  exact ⟨m, (dvd_mul_right _ _).trans hL_dvd⟩

-- ============================================================
-- PART 3: Eisenstein Criterion — X³ - 2 is Irreducible
-- ============================================================

private theorem cube_root_2_irred_int :
    Irreducible (X ^ 3 - C (2 : ℤ) : ℤ[X]) := by
  apply Polynomial.irreducible_of_eisenstein_criterion (P := Ideal.span {(2 : ℤ)})
  · rw [Ideal.span_singleton_prime (show (2 : ℤ) ≠ 0 from by norm_num)]
    exact Int.prime_iff_natAbs_prime.mpr (by norm_num)
  · rw [leadingCoeff_X_pow_sub_C (show (0 : ℕ) < 3 from by norm_num),
        Ideal.mem_span_singleton]
    norm_num
  · intro k hk
    rw [degree_X_pow_sub_C (show (0 : ℕ) < 3 from by norm_num) (2 : ℤ)] at hk
    have hk3 : k < 3 := WithBot.coe_lt_coe.mp hk
    interval_cases k <;> simp [Ideal.mem_span_singleton, coeff_sub, coeff_X_pow]
  · rw [degree_X_pow_sub_C (show (0 : ℕ) < 3 from by norm_num) (2 : ℤ)]; norm_cast
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    simp only [coeff_sub, coeff_X_pow, coeff_C, show ¬(0 = 3) from by norm_num,
               ite_false, zero_sub, dvd_neg]
    norm_num
  · exact (monic_X_pow_sub_C (2 : ℤ) (show 3 ≠ 0 from by norm_num)).isPrimitive

/-- X³ - 2 is irreducible over ℚ (Gauss's lemma from ℤ-irreducibility). -/
theorem cube_root_2_minpoly_irred : Irreducible (X ^ 3 - C 2 : ℚ[X]) := by
  have hprim : (X ^ 3 - C (2 : ℤ) : ℤ[X]).IsPrimitive :=
    (monic_X_pow_sub_C (2 : ℤ) (show 3 ≠ 0 from by norm_num)).isPrimitive
  have hirr := (IsPrimitive.Int.irreducible_iff_irreducible_map_cast hprim).mp
    cube_root_2_irred_int
  rwa [show Polynomial.map (Int.castRingHom ℚ) (X ^ 3 - C (2 : ℤ)) = X ^ 3 - C (2 : ℚ) from
    by simp [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, map_ofNat]] at hirr

-- ============================================================
-- PART 4: Degree Computations
-- ============================================================

theorem cos20_minpoly_degree : (8 * X ^ 3 - 6 * X - 1 : ℚ[X]).natDegree = 3 := by
  norm_num [natDegree_sub_eq_left_of_natDegree_lt, natDegree_mul, natDegree_pow,
    natDegree_X, natDegree_C, natDegree_one]

theorem regular_7gon_poly_degree :
    (8 * X ^ 3 + 4 * X ^ 2 - 4 * X - 1 : ℚ[X]).natDegree = 3 := by
  norm_num [natDegree_sub_eq_left_of_natDegree_lt, natDegree_add_eq_left_of_natDegree_lt,
    natDegree_mul, natDegree_pow, natDegree_X, natDegree_C, natDegree_one]

theorem cube_root_2_degree : (X ^ 3 - C 2 : ℚ[X]).natDegree = 3 := by
  simp

-- ============================================================
-- PART 5: Degree Not a Power of Two
-- ============================================================

def DegreePowerOfTwo (p : ℚ[X]) : Prop :=
  ∃ k : ℕ, p.natDegree = 2 ^ k

private lemma three_ne_two_pow (k : ℕ) : 3 ≠ 2 ^ k := by
  intro hk
  have hle : k ≤ 1 := by
    by_contra h
    push_neg at h
    have h2 : 2 ≤ k := Nat.succ_le_of_lt h
    have h2k : (4 : ℕ) ≤ 2 ^ k :=
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
           _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h2
    rw [← hk] at h2k
    norm_num at h2k
  interval_cases k <;> norm_num at hk

theorem cos20_degree_not_pow_two :
    ¬ DegreePowerOfTwo (8 * X ^ 3 - 6 * X - 1 : ℚ[X]) := by
  intro ⟨k, hk⟩
  rw [cos20_minpoly_degree] at hk
  exact three_ne_two_pow k hk

theorem three_not_pow_two : ¬ DegreePowerOfTwo (X ^ 3 - C 2 : ℚ[X]) := by
  intro ⟨k, hk⟩
  rw [cube_root_2_degree] at hk
  exact three_ne_two_pow k hk

theorem regular_7gon_impossible_degree :
    ¬ DegreePowerOfTwo (8 * X ^ 3 + 4 * X ^ 2 - 4 * X - 1 : ℚ[X]) := by
  intro ⟨k, hk⟩
  rw [regular_7gon_poly_degree] at hk
  exact three_ne_two_pow k hk

-- ============================================================
-- PART 6: Non-constructibility (via degree sorry)
-- ============================================================

/-- **Non-constructibility from degree criterion.**
    If p is irreducible over ℚ and deg(p) is not a power of 2,
    then no root of p in ℂ is constructible.

    **Proof** (using `isConstructible_algebraic_degree`):
    1. α constructible → α algebraic, finrank ℚ ℚ⟮α⟯ ∣ 2^n for some n.
    2. finrank ℚ ℚ⟮α⟯ = natDegree (minpoly ℚ α) (by `IntermediateField.adjoin.finrank`).
    3. minpoly ℚ α ∣ p (by `minpoly.dvd`).
    4. p irreducible + minpoly ∣ p → p associate to minpoly (c unit)
       → natDegree p = natDegree (minpoly) ∣ 2^n. Contradicts ¬ DegreePowerOfTwo p. -/
theorem not_constructible_of_bad_degree {p : ℚ[X]} (hp : Irreducible p)
    (hdeg : ¬ DegreePowerOfTwo p) :
    ∀ α : ℂ, Polynomial.aeval α p = 0 →
    ¬ IsConstructible α := by
  intro α hpα hcα
  -- Step 1: α algebraic, finrank ℚ ℚ⟮α⟯ ∣ 2^n for some n
  obtain ⟨halg, n, hn_dvd⟩ := isConstructible_algebraic_degree α hcα
  -- α is integral (algebraic over a field ↔ integral)
  have hint : IsIntegral ℚ α := isAlgebraic_iff_isIntegral.mp halg
  -- Step 2: natDegree (minpoly ℚ α) = Module.finrank ℚ ℚ⟮α⟯
  have hmind : (minpoly ℚ α).natDegree = Module.finrank ℚ ℚ⟮α⟯ :=
    (IntermediateField.adjoin.finrank hint).symm
  -- Step 3: minpoly ℚ α ∣ p
  have hdvd : minpoly ℚ α ∣ p := minpoly.dvd ℚ α hpα
  -- Step 4: p irreducible + minpoly ∣ p → natDegree p = 2^m for some m
  obtain ⟨c, hc⟩ := hdvd
  rcases hp.isUnit_or_isUnit hc with h1 | h2
  · -- minpoly ℚ α is a unit: get natDegree = 0 → finrank = 0, contradiction with 2^n
    have hunit_zero : (minpoly ℚ α).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit h1
    have h_fr_zero : Module.finrank ℚ ℚ⟮α⟯ = 0 := hmind ▸ hunit_zero
    rw [h_fr_zero] at hn_dvd
    exact absurd (Nat.zero_dvd.mp hn_dvd) (Nat.two_pow_pos n).ne'
  · -- c is a unit → natDegree p = natDegree (minpoly ℚ α) ∣ 2^n
    apply hdeg
    have hc_deg : c.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit h2
    have hne : minpoly ℚ α ≠ 0 := minpoly.ne_zero hint
    have hcne : c ≠ 0 := IsUnit.ne_zero h2
    have hp_eq : p.natDegree = (minpoly ℚ α).natDegree := by
      rw [hc, Polynomial.natDegree_mul hne hcne, hc_deg, add_zero]
    have hp_dvd : p.natDegree ∣ 2 ^ n := by rw [hp_eq, hmind]; exact hn_dvd
    obtain ⟨m, _, hm_eq⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp hp_dvd
    exact ⟨m, hm_eq⟩

-- ============================================================
-- PART 7: Concrete Impossibility Results (PROVED)
-- ============================================================

theorem angle_trisection_impossible_degree :
    ¬ DegreePowerOfTwo (8 * X ^ 3 - 6 * X - 1 : ℚ[X]) :=
  cos20_degree_not_pow_two

theorem doubling_cube_impossible_degree :
    ¬ DegreePowerOfTwo (X ^ 3 - C 2 : ℚ[X]) :=
  three_not_pow_two

theorem regular_7gon_construction_impossible :
    ¬ DegreePowerOfTwo (8 * X ^ 3 + 4 * X ^ 2 - 4 * X - 1 : ℚ[X]) :=
  regular_7gon_impossible_degree

-- ============================================================
-- PART 8: Galois Characterization (SORRY — needs full Galois theory)
-- ============================================================

/-- A finite group is a 2-group iff its order is a power of 2. -/
def IsTwoGroup (G : Type*) [Group G] [Fintype G] : Prop :=
  ∃ k : ℕ, Fintype.card G = 2 ^ k

/-- **[SORRY 3/3] Wantzel-Galois Theorem**: α constructible ↔ Gal(minpoly(ℚ,α)) is a 2-group.

    Under the FIXED IsConstructible definition, this is a TRUE statement. Previously
    (old definition with IsConstructible β precondition), it was FALSE since constructible
    meant rational, making the ← direction fail (e.g., X² - 2 has 2-group Gal but √2
    is not rational, hence "not constructible" under the old definition).

    Proof requires:
    1. Full Fundamental Theorem of Galois Theory (FTGT)
    2. 2-power degree extensions ↔ towers of quadratics
    3. Connection between constructibility and such towers
    Estimated: 500+ lines. Out of scope. -/
theorem wantzel_galois_iff {p : ℚ[X]} (hp : Irreducible p) (α : ℂ)
    (hα : Polynomial.aeval α p = 0) :
    IsConstructible α ↔ IsTwoGroup p.Gal := by
  sorry -- TRUE under fixed definition; requires FTGT + tower characterization

end AngleTrisectionOQ02OQ01OQ02Incomplete01
