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

## Remaining Sorries (Session 34 — Strong IH implementation)

Sessions 26-33 had sorries `hβ_dvd` (tower via ℚ⟮a⟯) and `hjoin_dvd` (join degree).
Session 34 introduced `isConstructible_algebraic_degree_strong` with strong IH:
  "For any L/ℚ finite, FiniteDimensional ↥L ↥(L ⊔ ℚ⟮α⟯) ∧ finrank ↥L ↥(L ⊔ ℚ⟮α⟯) ∣ 2^n"
This strong IH subsumes both hβ_dvd and hjoin_dvd, replacing them with:

1. `h_top` (in finrank_sup_sq_dvd): IntermediateField.adjoin ↥K {β_in_sup} = ⊤
   Proof plan: β_in_sup ∈ K⊔ℚ⟮β⟯ and it generates K⊔ℚ⟮β⟯ over K because the
   ℚ-intermediate field spanned by K and β is exactly K⊔ℚ⟮β⟯.
   Key API: IntermediateField.adjoin_le_iff, IntermediateField.sup_eq_adjoin.

2. `hfd_L_join` (in isConstructible_algebraic_degree_strong, sqrt_ext case):
   FiniteDimensional ↥L ↥(L ⊔ ℚ⟮b+β⟯)
   Proof plan: L⊔ℚ⟮b+β⟯ embeds into L₃ = L₂⊔ℚ⟮β⟯ (finite over ℚ); both L and L₃
   are finite over ℚ → L₃/L is finite → subspace L⊔ℚ⟮b+β⟯/L is finite.
   Key API: Module.Finite.of_restrictScalars_finite.

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
-- PART 2: Key Structural Lemma (tower degree property)
-- ============================================================

/-- Helper: if β² = a ∈ K and β is algebraic over ℚ, finrank ↥K ↥(K ⊔ ℚ⟮β⟯) ∣ 2.

    KEY SORRY: β generates K ⊔ ℚ⟮β⟯ over K (i.e., adjoin ↥K {β_in_sup} = ⊤).
    This follows because (adjoin ↥K {β_in_sup}).restrictScalars ℚ is a ℚ-intermediate
    field of ℂ containing K and β, hence ≥ K ⊔ ℚ⟮β⟯, hence = K ⊔ ℚ⟮β⟯. -/
private lemma finrank_sup_sq_dvd (K : IntermediateField ℚ ℂ) (β a : ℂ)
    (halg_β : IsAlgebraic ℚ β) (ha_in : a ∈ K) (hβ2 : β * β = a)
    [FiniteDimensional ℚ ↥K] :
    FiniteDimensional ↥K ↥(K ⊔ ℚ⟮β⟯) ∧ Module.finrank ↥K ↥(K ⊔ ℚ⟮β⟯) ∣ 2 := by
  haveI hAlg_K : Algebra ↥K ↥(K ⊔ ℚ⟮β⟯) :=
    (IntermediateField.inclusion le_sup_left).toAlgebra
  haveI hST_K : IsScalarTower ℚ ↥K ↥(K ⊔ ℚ⟮β⟯) :=
    IsScalarTower.of_algebraMap_eq (fun r =>
      Subtype.ext (by simp [RingHom.algebraMap_toAlgebra]))
  let β_in_sup : ↥(K ⊔ ℚ⟮β⟯) :=
    ⟨β, le_sup_right (IntermediateField.mem_adjoin_simple_self ℚ β)⟩
  let a_in_K : ↥K := ⟨a, ha_in⟩
  have hβ_int_ℚ : IsIntegral ℚ β := isAlgebraic_iff_isIntegral.mp halg_β
  have hβ_int_inner_Q : IsIntegral ℚ β_in_sup := by
    rw [← isIntegral_algebraMap_iff (algebraMap ↥(K ⊔ ℚ⟮β⟯) ℂ).injective]
    exact hβ_int_ℚ
  have hβ_int_K : IsIntegral ↥K β_in_sup := hβ_int_inner_Q.tower_top
  -- KEY SORRY: β generates K ⊔ ℚ⟮β⟯ over K
  have h_top : IntermediateField.adjoin ↥K {β_in_sup} = ⊤ := by
    sorry
  constructor
  · rw [← IntermediateField.finrank_top' (K := ↥K) (L := ↥(K ⊔ ℚ⟮β⟯)), ← h_top]
    exact IntermediateField.adjoin.finiteDimensional hβ_int_K
  · have h_finrank : Module.finrank ↥K ↥(K ⊔ ℚ⟮β⟯) =
        (minpoly ↥K β_in_sup).natDegree := by
      have := IntermediateField.adjoin.finrank hβ_int_K
      erw [h_top, IntermediateField.finrank_top'] at this
      exact this
    set p : Polynomial ↥K := Polynomial.X ^ 2 - Polynomial.C a_in_K with hp_def
    have h_aeval : Polynomial.aeval β_in_sup p = 0 := by
      simp only [hp_def, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, sub_eq_zero]
      apply_fun Subtype.val using Subtype.val_injective
      simp only [SubsemiringClass.coe_pow, β_in_sup, a_in_K,
        RingHom.algebraMap_toAlgebra, IntermediateField.coe_inclusion, Subtype.coe_mk]
      rw [sq]; exact hβ2
    have h_deg_p : p.natDegree = 2 := by
      apply Polynomial.natDegree_sub_eq_left_of_natDegree_lt
      simp [Polynomial.natDegree_X_pow, Polynomial.natDegree_C]
    have h_p_ne : p ≠ 0 := by
      intro h; rw [h, Polynomial.natDegree_zero] at h_deg_p; omega
    have h_dvd : minpoly ↥K β_in_sup ∣ p := minpoly.dvd _ _ h_aeval
    have h_pos : 1 ≤ (minpoly ↥K β_in_sup).natDegree := minpoly.natDegree_pos hβ_int_K
    have h_deg : (minpoly ↥K β_in_sup).natDegree ≤ 2 :=
      (Polynomial.natDegree_le_of_dvd h_dvd h_p_ne).trans (le_of_eq h_deg_p)
    rw [h_finrank]
    rcases (by omega : (minpoly ↥K β_in_sup).natDegree = 1 ∨
        (minpoly ↥K β_in_sup).natDegree = 2) with h | h
    · exact h ▸ one_dvd 2
    · exact h ▸ dvd_refl 2

/-- Strong form: for any L/ℚ finite, finrank ↥L ↥(L ⊔ ℚ⟮α⟯) ∣ 2^n for some n.

    This is the key lemma needed to prove the tower degree theorem by induction:
    the naive IH (finrank ℚ ℚ⟮b⟯ ∣ 2^k) is too weak for the sqrt_ext case;
    we need finrank ↥ℚ⟮β⟯ ↥(ℚ⟮β⟯ ⊔ ℚ⟮b⟯) ∣ 2^k, which requires this strong IH. -/
private lemma isConstructible_algebraic_degree_strong (α : ℂ) (h : IsConstructible α) :
    IsAlgebraic ℚ α ∧ ∃ n : ℕ, ∀ (L : IntermediateField ℚ ℂ) [FiniteDimensional ℚ ↥L],
        FiniteDimensional ↥L ↥(L ⊔ ℚ⟮α⟯) ∧ Module.finrank ↥L ↥(L ⊔ ℚ⟮α⟯) ∣ 2 ^ n := by
  induction h with
  | rational _ h_mem =>
    obtain ⟨q, rfl⟩ := h_mem
    refine ⟨isAlgebraic_algebraMap q, 0, fun L _ => ?_⟩
    have hbot : (ℚ⟮algebraMap ℚ ℂ q⟯ : IntermediateField ℚ ℂ) = ⊥ :=
      IntermediateField.adjoin_simple_eq_bot_iff.mpr
        (IntermediateField.mem_bot.mpr ⟨q, rfl⟩)
    rw [hbot, sup_bot_eq, pow_zero]
    exact ⟨inferInstance, one_dvd 1⟩
  | sqrt_ext β a b _ _ hβ2 ih_a ih_b =>
    obtain ⟨halg_a, j, ihj⟩ := ih_a
    obtain ⟨halg_b, k, ihk⟩ := ih_b
    have hβ_sq : β ^ 2 = a := by rw [sq]; exact hβ2
    have halg_β : IsAlgebraic ℚ β :=
      IsAlgebraic.of_pow (by norm_num : 0 < 2) (hβ_sq ▸ halg_a)
    have halg_bβ : IsAlgebraic ℚ (b + β) := by
      rw [isAlgebraic_iff_isIntegral] at halg_b halg_β ⊢
      exact halg_b.add halg_β
    refine ⟨halg_bβ, j + k + 1, fun L hfdL => ?_⟩
    -- L₁ = L ⊔ ℚ⟮b⟯
    let L₁ : IntermediateField ℚ ℂ := L ⊔ ℚ⟮b⟯
    obtain ⟨hfd_L_L₁, hk_L⟩ := ihk L
    haveI hAlg_L_L₁ : Algebra ↥L ↥L₁ :=
      (IntermediateField.inclusion le_sup_left).toAlgebra
    haveI hST_L_L₁ : IsScalarTower ℚ ↥L ↥L₁ :=
      IsScalarTower.of_algebraMap_eq (fun r =>
        Subtype.ext (by simp [RingHom.algebraMap_toAlgebra]))
    haveI hfdQ_L₁ : FiniteDimensional ℚ ↥L₁ := by
      haveI : Module.Finite ℚ ↥L := hfdL
      haveI : Module.Finite ↥L ↥L₁ := hfd_L_L₁
      exact Module.Finite.trans (R := ℚ) (M := ↥L)
    -- L₂ = L₁ ⊔ ℚ⟮a⟯
    let L₂ : IntermediateField ℚ ℂ := L₁ ⊔ ℚ⟮a⟯
    obtain ⟨hfd_L₁_L₂, hj_L₁⟩ := ihj L₁
    haveI hAlg_L₁_L₂ : Algebra ↥L₁ ↥L₂ :=
      (IntermediateField.inclusion le_sup_left).toAlgebra
    haveI hST_L₁_L₂ : IsScalarTower ℚ ↥L₁ ↥L₂ :=
      IsScalarTower.of_algebraMap_eq (fun r =>
        Subtype.ext (by simp [RingHom.algebraMap_toAlgebra]))
    haveI hfdQ_L₂ : FiniteDimensional ℚ ↥L₂ := by
      haveI : Module.Finite ℚ ↥L₁ := hfdQ_L₁
      haveI : Module.Finite ↥L₁ ↥L₂ := hfd_L₁_L₂
      exact Module.Finite.trans (R := ℚ) (M := ↥L₁)
    -- L₃ = L₂ ⊔ ℚ⟮β⟯, using finrank_sup_sq_dvd
    have ha_in_L₂ : a ∈ (L₂ : IntermediateField ℚ ℂ) :=
      le_sup_right (IntermediateField.mem_adjoin_simple_self ℚ a)
    obtain ⟨hfd_L₂_L₃, h2_L₂⟩ := finrank_sup_sq_dvd L₂ β a halg_β ha_in_L₂ hβ2
    let L₃ : IntermediateField ℚ ℂ := L₂ ⊔ ℚ⟮β⟯
    haveI hAlg_L₂_L₃ : Algebra ↥L₂ ↥L₃ :=
      (IntermediateField.inclusion le_sup_left).toAlgebra
    haveI hST_L₂_L₃ : IsScalarTower ℚ ↥L₂ ↥L₃ :=
      IsScalarTower.of_algebraMap_eq (fun r =>
        Subtype.ext (by simp [RingHom.algebraMap_toAlgebra]))
    haveI hfdQ_L₃ : FiniteDimensional ℚ ↥L₃ := by
      haveI : Module.Finite ℚ ↥L₂ := hfdQ_L₂
      haveI : Module.Finite ↥L₂ ↥L₃ := hfd_L₂_L₃
      exact Module.Finite.trans (R := ℚ) (M := ↥L₂)
    -- b + β ∈ L₃
    have hb_in_L₃ : b ∈ (L₃ : IntermediateField ℚ ℂ) :=
      le_sup_left (le_sup_left (le_sup_right (IntermediateField.mem_adjoin_simple_self ℚ b)))
    have hβ_in_L₃ : β ∈ (L₃ : IntermediateField ℚ ℂ) :=
      le_sup_right (IntermediateField.mem_adjoin_simple_self ℚ β)
    -- L ⊔ ℚ⟮(b+β)⟯ ≤ L₃
    have hle_L₃ : (L ⊔ ℚ⟮b + β⟯ : IntermediateField ℚ ℂ) ≤ L₃ :=
      sup_le (le_trans (le_trans le_sup_left le_sup_left) le_sup_left)
             (IntermediateField.adjoin_simple_le_iff.mpr (add_mem hb_in_L₃ hβ_in_L₃))
    -- Algebra instances for L ≤ L ⊔ ℚ⟮b+β⟯ ≤ L₃
    haveI hAlg_L_join : Algebra ↥L ↥(L ⊔ ℚ⟮b + β⟯) :=
      (IntermediateField.inclusion le_sup_left).toAlgebra
    haveI hST_L_join : IsScalarTower ℚ ↥L ↥(L ⊔ ℚ⟮b + β⟯) :=
      IsScalarTower.of_algebraMap_eq (fun r =>
        Subtype.ext (by simp [RingHom.algebraMap_toAlgebra]))
    haveI hAlg_join_L₃ : Algebra ↥(L ⊔ ℚ⟮b + β⟯) ↥L₃ :=
      (IntermediateField.inclusion hle_L₃).toAlgebra
    haveI hST_join_L₃ : IsScalarTower ℚ ↥(L ⊔ ℚ⟮b + β⟯) ↥L₃ :=
      IsScalarTower.of_algebraMap_eq (fun r =>
        Subtype.ext (by simp [RingHom.algebraMap_toAlgebra]))
    haveI hST_L_join_L₃ : IsScalarTower ↥L ↥(L ⊔ ℚ⟮b + β⟯) ↥L₃ :=
      IsScalarTower.of_algebraMap_eq (fun r =>
        Subtype.ext (by simp [RingHom.algebraMap_toAlgebra]))
    -- FiniteDimensional ↥L ↥(L ⊔ ℚ⟮b+β⟯): subfield of L₃ which is finite over ℚ
    haveI hfd_L_join : FiniteDimensional ↥L ↥(L ⊔ ℚ⟮b + β⟯) := by
      -- L ⊔ ℚ⟮b+β⟯ is a submodule of L₃ over L; L₃ finite over ℚ + L finite over ℚ → L₃ finite over L
      sorry
    refine ⟨hfd_L_join, ?_⟩
    -- Tower algebra instances for L₁ ≤ L₂ ≤ L₃ and L ≤ L₁ ≤ L₃
    haveI hST_L₁_L₂_L₃ : IsScalarTower ↥L₁ ↥L₂ ↥L₃ :=
      IsScalarTower.of_algebraMap_eq (fun r =>
        Subtype.ext (by simp [RingHom.algebraMap_toAlgebra]))
    haveI hAlg_L₁_L₃ : Algebra ↥L₁ ↥L₃ :=
      (IntermediateField.inclusion (le_trans le_sup_left le_sup_left)).toAlgebra
    haveI hST_L_L₁_L₃ : IsScalarTower ↥L ↥L₁ ↥L₃ :=
      IsScalarTower.of_algebraMap_eq (fun r =>
        Subtype.ext (by simp [RingHom.algebraMap_toAlgebra]))
    -- Additional algebra + finiteness instances for tower law
    haveI hAlg_L_L₃ : Algebra ↥L ↥L₃ :=
      (IntermediateField.inclusion (le_trans (le_trans le_sup_left le_sup_left) le_sup_left)).toAlgebra
    haveI hST_Q_L₁_L₃ : IsScalarTower ℚ ↥L₁ ↥L₃ :=
      IsScalarTower.of_algebraMap_eq (fun r =>
        Subtype.ext (by simp [RingHom.algebraMap_toAlgebra]))
    haveI hfd_L₁_L₃ : FiniteDimensional ↥L₁ ↥L₃ :=
      Module.Finite.of_restrictScalars_finite ℚ ↥L₁ ↥L₃
    haveI hfd_join_L₃ : FiniteDimensional ↥(L ⊔ ℚ⟮b + β⟯) ↥L₃ :=
      Module.Finite.of_restrictScalars_finite ℚ ↥(L ⊔ ℚ⟮b + β⟯) ↥L₃
    -- finrank ↥L ↥(L ⊔ ℚ⟮b+β⟯) ∣ finrank ↥L ↥L₃
    have hdvd_L₃ : Module.finrank ↥L ↥(L ⊔ ℚ⟮b + β⟯) ∣ Module.finrank ↥L ↥L₃ :=
      ⟨Module.finrank ↥(L ⊔ ℚ⟮b + β⟯) ↥L₃,
       (Module.finrank_mul_finrank ↥L ↥(L ⊔ ℚ⟮b + β⟯) ↥L₃).symm⟩
    -- finrank ↥L ↥L₃ = finrank ↥L ↥L₁ * (finrank ↥L₁ ↥L₂ * finrank ↥L₂ ↥L₃) ∣ 2^(j+k+1)
    have hdvd_tower : Module.finrank ↥L ↥L₃ ∣ 2 ^ (j + k + 1) := by
      have h1 := Module.finrank_mul_finrank ↥L ↥L₁ ↥L₃
      have h2 := Module.finrank_mul_finrank ↥L₁ ↥L₂ ↥L₃
      rw [← h1, ← h2]
      have heq : (2 : ℕ) ^ (j + k + 1) = 2 ^ k * (2 ^ j * 2) := by ring
      rw [heq]
      exact Nat.mul_dvd_mul hk_L (Nat.mul_dvd_mul hj_L₁ h2_L₂)
    exact hdvd_L₃.trans hdvd_tower

/-- Constructible numbers are algebraic of 2-power degree. Derived from the strong form. -/
private lemma isConstructible_algebraic_degree (α : ℂ) (h : IsConstructible α) :
    IsAlgebraic ℚ α ∧ ∃ n : ℕ, Module.finrank ℚ ℚ⟮α⟯ ∣ 2 ^ n := by
  obtain ⟨halg, n, hn⟩ := isConstructible_algebraic_degree_strong α h
  refine ⟨halg, n, ?_⟩
  -- Apply the strong IH with L = ⊥ (which is FiniteDimensional ℚ ↥⊥ trivially)
  haveI : FiniteDimensional ℚ ↥(⊥ : IntermediateField ℚ ℂ) := inferInstance
  obtain ⟨_, hdvd⟩ := hn (⊥ : IntermediateField ℚ ℂ)
  -- ⊥ ⊔ ℚ⟮α⟯ = ℚ⟮α⟯
  rwa [bot_sup_eq] at hdvd

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
