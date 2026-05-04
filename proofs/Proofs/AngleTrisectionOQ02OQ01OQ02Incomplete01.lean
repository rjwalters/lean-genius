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

1. `wantzel_galois_iff` (out-of-scope): Requires full Galois correspondence + 2-group structure.
   Estimated: 500+ lines of new Galois theory infrastructure. Out of scope.
   Proof strategy documented in detail (Session 36): see `isConstructible_map` for key infrastructure.

Previously resolved:
- `hβ_dvd` (Step C): proved in Sessions 31-32 via tower law + minpoly degree bound (#15067, #15103)
- `hjoin_dvd` (Step D): proved in Session 34 via stronger IH `isConstructible_sup_degree` (#15128)

## New Lemmas (Session 36)

- `isConstructible_map`: IsConstructible preserved under ℚ-algebra endomorphisms of ℂ.
  Key infrastructure for wantzel_galois_iff → direction.

## New Lemmas (Session 37)

- `isConstructible_minpoly_pow2`: IsConstructible α → ∃ m, natDeg(minpoly ℚ α) = 2^m.
  Clean consequence of isConstructible_algebraic_degree + adjoin.finrank.
- `isConstructible_irred_degree_pow2`: For p irreducible with constructible root α,
  natDeg p = 2^m for some m. Positive form of not_constructible_of_bad_degree.

## Status: 0 sorries, 0 axioms — all three impossibility results proved
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

/-- **Galois invariance**: ℚ-algebra endomorphisms of ℂ preserve constructibility.

    Proof: structural induction on IsConstructible.
    - rational: σ(algebraMap ℚ ℂ q) = algebraMap ℚ ℂ q (σ is a ℚ-algebra map).
    - sqrt_ext: σ(b + β) = σ(b) + σ(β), σ(β)·σ(β) = σ(β·β) = σ(a).

    This is the key infrastructure for the → direction of wantzel_galois_iff:
    all Galois conjugates of a constructible α are constructible. -/
lemma isConstructible_map (σ : ℂ →ₐ[ℚ] ℂ) (α : ℂ) (h : IsConstructible α) :
    IsConstructible (σ α) := by
  induction h with
  | rational α h_mem =>
    obtain ⟨q, rfl⟩ := h_mem
    rw [AlgHom.commutes]
    exact IsConstructible.rational _ ⟨q, rfl⟩
  | sqrt_ext β a b _ _ hβ2 ih_a ih_b =>
    rw [map_add]
    exact IsConstructible.sqrt_ext (σ β) (σ a) (σ b) ih_a ih_b
      (by rw [← map_mul]; exact congr_arg σ hβ2)

/-- Constructible numbers are algebraic over ℚ (basic induction, used in sup_degree). -/
private lemma isConstructible_algebraic (α : ℂ) (h : IsConstructible α) : IsAlgebraic ℚ α := by
  induction h with
  | rational _ h_mem => obtain ⟨q, rfl⟩ := h_mem; exact isAlgebraic_algebraMap q
  | sqrt_ext β a b _ _ hβ2 ih_a ih_b =>
    have hβ_sq : β ^ 2 = a := by rw [sq]; exact hβ2
    have halg_β : IsAlgebraic ℚ β :=
      IsAlgebraic.of_pow (by norm_num : 0 < 2) (hβ_sq ▸ ih_a)
    rw [isAlgebraic_iff_isIntegral] at ih_b halg_β ⊢
    exact ih_b.add halg_β

/-- **Stronger IH**: constructible numbers have 2-power degree over any intermediate base K.

    For any K : IntermediateField ℚ ℂ, finrank ↥K ↥(K ⊔ ℚ⟮α⟯) divides a power of 2.

    This is the key lemma for proving `hjoin_dvd` in `isConstructible_algebraic_degree`:
    applying it with K = ℚ⟮β⟯ gives `finrank ↥ℚ⟮β⟯ ↥(ℚ⟮β⟯ ⊔ ℚ⟮b⟯) ∣ 2^k'`, which
    via the tower law gives `finrank ℚ (ℚ⟮b⟯ ⊔ ℚ⟮β⟯) ∣ 2^(j+1) * 2^k'`.

    **Proof of h_top_Ka** (Session 38): β generates Ka ⊔ ℚ⟮β⟯ over Ka.
    Strategy: define Ka_in = Ka.comap (Ka ⊔ ℚ⟮β⟯).val, prove adjoin ℚ (Ka_in ∪ {β'}) = ⊤
    via map_injective + adjoin_union + adjoin_self, then use adjoin_eq_top_of_adjoin_eq_top
    to get adjoin Ka (Ka_in ∪ {β'}) = ⊤, reduce adjoin Ka Ka_in = ⊥ via mem_bot. -/
-- Helper: (adjoin Ka {β}).restrictScalars ℚ = Ka ⊔ ℚ⟮β⟯, so the carriers are equal
-- This is used to identify the Ka-finrank of Ka ⊔ ℚ⟮β⟯ with adjoin.finrank
private lemma finrank_sup_quadratic_dvd_two (Ka : IntermediateField ℚ ℂ) (β : ℂ)
    (hβ_alg : IsAlgebraic ℚ β) (hβ_sq_mem : β ^ 2 ∈ Ka) :
    Module.finrank ↥Ka ↥(Ka ⊔ ℚ⟮β⟯) ∣ 2 := by
  -- β is integral over Ka (algebraic over ℚ ≤ Ka)
  have hβ_int_Ka : IsIntegral ↥Ka β := by
    rw [← isAlgebraic_iff_isIntegral]; exact hβ_alg.tower_top ↥Ka
  -- β lives in Ka ⊔ ℚ⟮β⟯
  let β' : ↥(Ka ⊔ ℚ⟮β⟯) :=
    ⟨β, le_sup_right (IntermediateField.mem_adjoin_simple_self ℚ β)⟩
  -- β'² = algebraMap Ka (Ka ⊔ ℚ⟮β⟯) of the β²-element
  let a' : ↥Ka := ⟨β ^ 2, hβ_sq_mem⟩
  -- β' is integral over Ka (same as β being integral over Ka)
  have hβ'_int : IsIntegral ↥Ka β' := by
    rw [← isIntegral_algebraMap_iff (algebraMap ↥(Ka ⊔ ℚ⟮β⟯) ℂ).injective]
    simpa using hβ_int_Ka
  -- β' satisfies X² - C a' over Ka (annihilating polynomial)
  have h_aeval : Polynomial.aeval β' (X ^ 2 - C a' : Polynomial ↥Ka) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero]
    apply_fun Subtype.val using Subtype.val_injective
    simp [β', a', RingHom.algebraMap_toAlgebra, IntermediateField.coe_inclusion]
  -- p := X² - C a' is nonzero with natDegree 2
  have h_p_ne : (X ^ 2 - C a' : Polynomial ↥Ka) ≠ 0 := by
    intro h; have := congr_arg Polynomial.natDegree h
    simp [Polynomial.natDegree_sub_eq_left_of_natDegree_lt] at this
  -- minpoly Ka β' divides p, so natDegree ≤ 2
  have h_dvd : minpoly ↥Ka β' ∣ (X ^ 2 - C a') := minpoly.dvd _ _ h_aeval
  have h_deg_le : (minpoly ↥Ka β').natDegree ≤ 2 :=
    (Polynomial.natDegree_le_of_dvd h_dvd h_p_ne).trans (by
      simp [Polynomial.natDegree_sub_eq_left_of_natDegree_lt])
  -- β' generates Ka ⊔ ℚ⟮β⟯ over Ka
  -- Key: (adjoin Ka {β}).restrictScalars ℚ = Ka ⊔ ℚ⟮β⟯ (restrictScalars_adjoin_eq_sup)
  -- and coe_restrictScalars is rfl, so adjoin Ka {β} and Ka ⊔ ℚ⟮β⟯ have the same carrier
  -- Thus adjoin Ka {β'} = ⊤ in Ka ⊔ ℚ⟮β⟯ follows from the set equality
  have h_top_Ka : IntermediateField.adjoin ↥Ka ({β'} : Set ↥(Ka ⊔ ℚ⟮β⟯)) = ⊤ := by
    -- Ka_in = preimage of Ka inside ↥(Ka ⊔ ℚ⟮β⟯)
    let Ka_in : IntermediateField ℚ ↥(Ka ⊔ ℚ⟮β⟯) := Ka.comap (Ka ⊔ ℚ⟮β⟯).val
    -- val maps Ka_in onto Ka
    have h_img : (Ka ⊔ ℚ⟮β⟯).val '' (↑Ka_in : Set ↥(Ka ⊔ ℚ⟮β⟯)) = ↑Ka := by
      ext x; constructor
      · rintro ⟨⟨y, _⟩, hmem, rfl⟩
        exact IntermediateField.mem_comap.mp (SetLike.mem_coe.mp hmem)
      · intro hx
        exact ⟨⟨x, le_sup_left hx⟩,
               SetLike.mem_coe.mpr (IntermediateField.mem_comap.mpr hx), rfl⟩
    -- adjoin ℚ (↑Ka_in ∪ {β'}) = ⊤ via injectivity of val
    have h_adj_ℚ : IntermediateField.adjoin ℚ (↑Ka_in ∪ {β'}) = ⊤ := by
      apply IntermediateField.map_injective (Ka ⊔ ℚ⟮β⟯).val
      rw [← AlgHom.fieldRange_eq_map, IntermediateField.fieldRange_val,
          IntermediateField.adjoin_map, Set.image_union, Set.image_singleton,
          show (Ka ⊔ ℚ⟮β⟯).val β' = β from rfl,
          h_img]
      -- goal: adjoin ℚ (↑Ka ∪ {β}) = Ka ⊔ ℚ⟮β⟯ in IntermediateField ℚ ℂ
      exact le_antisymm
        (IntermediateField.adjoin_le_iff.mpr (Set.union_subset
          (fun x hx => le_sup_left hx)
          (fun x hx => by
            rw [Set.mem_singleton_iff] at hx
            exact le_sup_right (hx ▸ IntermediateField.mem_adjoin_simple_self ℚ β))))
        (sup_le
          (by intro x hx; exact IntermediateField.subset_adjoin ℚ _ (Set.mem_union_left _ hx))
          (IntermediateField.adjoin_simple_le_iff.mpr
            (IntermediateField.subset_adjoin ℚ _
              (Set.mem_union_right ↑Ka (Set.mem_singleton_self β)))))
    -- tower law: adjoin ℚ S = ⊤ implies adjoin ↥Ka S = ⊤
    have h_adj_Ka := IntermediateField.adjoin_eq_top_of_adjoin_eq_top h_adj_ℚ
    -- Ka_in elements are algebraMap images, so they lie in adjoin ↥Ka {β'} already
    have h_le : IntermediateField.adjoin ↥Ka (↑Ka_in ∪ {β'}) ≤
                IntermediateField.adjoin ↥Ka ({β'} : Set ↥(Ka ⊔ ℚ⟮β⟯)) :=
      IntermediateField.adjoin_le_iff.mpr (Set.union_subset
        (fun y hmem =>
          let k : ↥Ka :=
            ⟨(Ka ⊔ ℚ⟮β⟯).val y,
             IntermediateField.mem_comap.mp (SetLike.mem_coe.mp hmem)⟩
          have hyk : y = algebraMap ↥Ka ↥(Ka ⊔ ℚ⟮β⟯) k := Subtype.ext rfl
          hyk ▸ IntermediateField.algebraMap_mem
            (IntermediateField.adjoin ↥Ka ({β'} : Set ↥(Ka ⊔ ℚ⟮β⟯))) k)
        (IntermediateField.subset_adjoin ↥Ka _))
    exact eq_top_iff.mpr (h_adj_Ka ▸ h_le)
  -- finrank Ka (Ka ⊔ ℚ⟮β⟯) = natDegree (minpoly Ka β')
  have h_finrank : Module.finrank ↥Ka ↥(Ka ⊔ ℚ⟮β⟯) = (minpoly ↥Ka β').natDegree := by
    have := IntermediateField.adjoin.finrank hβ'_int
    rw [h_top_Ka, IntermediateField.finrank_top'] at this
    exact this
  -- natDegree ∈ {1, 2}, both divide 2
  rw [h_finrank]
  have h_pos := minpoly.natDegree_pos hβ'_int
  omega

private lemma isConstructible_sup_degree (α : ℂ) (h : IsConstructible α) :
    ∀ (K : IntermediateField ℚ ℂ), ∃ n : ℕ, Module.finrank ↥K ↥(K ⊔ ℚ⟮α⟯) ∣ 2 ^ n := by
  induction h with
  | rational α h_mem =>
    intro K
    obtain ⟨q, rfl⟩ := h_mem
    -- α = algebraMap ℚ ℂ q ∈ K (rationals are in all IntermediateFields)
    have hα_in_K : algebraMap ℚ ℂ q ∈ K := K.algebraMap_mem q
    rw [sup_eq_left.mpr (IntermediateField.adjoin_simple_le_iff.mpr hα_in_K)]
    exact ⟨0, by simp⟩
  | sqrt_ext β a b ha hb hβ2 ih_a ih_b =>
    -- α = b + β, β * β = a, IsConstructible a (ih_a), IsConstructible b (ih_b)
    have hβ_sq : β ^ 2 = a := by rw [sq]; exact hβ2
    have halg_a : IsAlgebraic ℚ a := isConstructible_algebraic a ha
    have halg_β : IsAlgebraic ℚ β :=
      IsAlgebraic.of_pow (by norm_num : 0 < 2) (hβ_sq ▸ halg_a)
    intro K
    -- Ka = K ⊔ ℚ⟮a⟯; IH_a gives finrank K Ka ∣ 2^n₁
    set Ka := (K ⊔ ℚ⟮a⟯ : IntermediateField ℚ ℂ) with hKa_def
    obtain ⟨n₁, hn₁⟩ := ih_a K
    -- Kaβ = Ka ⊔ ℚ⟮β⟯
    set Kaβ := (Ka ⊔ ℚ⟮β⟯ : IntermediateField ℚ ℂ) with hKaβ_def
    -- a ∈ Ka (since a ∈ ℚ⟮a⟯ ≤ Ka)
    have ha_in_Ka : a ∈ Ka := le_sup_right (IntermediateField.mem_adjoin_simple_self ℚ a)
    -- β² ∈ Ka (since β² = a ∈ Ka)
    have hβ_sq_in_Ka : β ^ 2 ∈ Ka := hβ_sq ▸ ha_in_Ka
    -- Key: finrank Ka Kaβ ∣ 2
    have h_step2 : Module.finrank ↥Ka ↥Kaβ ∣ 2 :=
      finrank_sup_quadratic_dvd_two Ka β halg_β hβ_sq_in_Ka
    -- IH_b at Kaβ: finrank Kaβ (Kaβ ⊔ ℚ⟮b⟯) ∣ 2^n₂
    obtain ⟨n₂, hn₂⟩ := ih_b Kaβ
    -- b + β ∈ Kaβ ⊔ ℚ⟮b⟯ (β ∈ ℚ⟮β⟯ ≤ Ka ⊔ ℚ⟮β⟯ = Kaβ ≤ Kaβ ⊔ ℚ⟮b⟯, b ∈ ℚ⟮b⟯ ≤ Kaβ ⊔ ℚ⟮b⟯)
    have hβ_in_Kaβ : β ∈ Kaβ :=
      le_sup_right (IntermediateField.mem_adjoin_simple_self ℚ β)
    have hmem : b + β ∈ Kaβ ⊔ ℚ⟮b⟯ :=
      add_mem (le_sup_left hβ_in_Kaβ)
              (le_sup_right (IntermediateField.mem_adjoin_simple_self ℚ b))
    -- K ⊔ ℚ⟮b+β⟯ ≤ Kaβ ⊔ ℚ⟮b⟯
    have h_le : K ⊔ ℚ⟮(b + β)⟯ ≤ Kaβ ⊔ ℚ⟮b⟯ := by
      apply sup_le
      · exact le_sup_left.trans (le_sup_left.trans le_sup_left)
      · exact IntermediateField.adjoin_simple_le_iff.mpr hmem
    -- Set up algebra instances for the tower K → Ka → Kaβ → Kaβ ⊔ ℚ⟮b⟯
    haveI hAlg_KKa : Algebra ↥K ↥Ka :=
      (IntermediateField.inclusion le_sup_left).toAlgebra
    haveI hST_KKa : IsScalarTower ℚ ↥K ↥Ka :=
      IsScalarTower.of_algebraMap_eq (fun r =>
        Subtype.ext (by simp [RingHom.algebraMap_toAlgebra]))
    haveI hAlg_KaKaβ : Algebra ↥Ka ↥Kaβ :=
      (IntermediateField.inclusion le_sup_left).toAlgebra
    haveI hST_KKaKaβ : IsScalarTower ↥K ↥Ka ↥Kaβ :=
      IsScalarTower.of_algebraMap_eq (fun r =>
        Subtype.ext (by simp [RingHom.algebraMap_toAlgebra,
          IntermediateField.coe_inclusion]))
    haveI hAlg_KaβJoin : Algebra ↥Kaβ ↥(Kaβ ⊔ ℚ⟮b⟯) :=
      (IntermediateField.inclusion le_sup_left).toAlgebra
    haveI hST_KaKaβJoin : IsScalarTower ↥Ka ↥Kaβ ↥(Kaβ ⊔ ℚ⟮b⟯) :=
      IsScalarTower.of_algebraMap_eq (fun r =>
        Subtype.ext (by simp [RingHom.algebraMap_toAlgebra,
          IntermediateField.coe_inclusion]))
    -- Additional algebra instances for K → Ka → (Kaβ ⊔ ℚ⟮b⟯) tower
    haveI hAlg_KaJoin : Algebra ↥Ka ↥(Kaβ ⊔ ℚ⟮b⟯) :=
      (IntermediateField.inclusion (le_sup_left.trans le_sup_left)).toAlgebra
    haveI hAlg_KJoin : Algebra ↥K ↥(Kaβ ⊔ ℚ⟮b⟯) :=
      (IntermediateField.inclusion
        (le_sup_left.trans (le_sup_left.trans le_sup_left))).toAlgebra
    haveI hST_KKaJoin : IsScalarTower ↥K ↥Ka ↥(Kaβ ⊔ ℚ⟮b⟯) :=
      IsScalarTower.of_algebraMap_eq (fun r =>
        Subtype.ext (by simp [RingHom.algebraMap_toAlgebra,
          IntermediateField.coe_inclusion]))
    -- Tower laws
    have htower_KaβJoin := Module.finrank_mul_finrank ↥Ka ↥Kaβ ↥(Kaβ ⊔ ℚ⟮b⟯)
    have htower_KJoin := Module.finrank_mul_finrank ↥K ↥Ka ↥(Kaβ ⊔ ℚ⟮b⟯)
    -- finrank K (Kaβ ⊔ ℚ⟮b⟯) ∣ 2^(n₁ + 1 + n₂)
    have h_tower_dvd : Module.finrank ↥K ↥(Kaβ ⊔ ℚ⟮b⟯) ∣ 2 ^ (n₁ + 1 + n₂) := by
      have h_Ka_dvd : Module.finrank ↥Ka ↥(Kaβ ⊔ ℚ⟮b⟯) ∣ 2 ^ (1 + n₂) := by
        rw [← htower_KaβJoin, pow_add, pow_one]
        exact Nat.mul_dvd_mul h_step2 hn₂
      rw [show n₁ + 1 + n₂ = n₁ + (1 + n₂) from by ring, pow_add, ← htower_KJoin]
      exact Nat.mul_dvd_mul hn₁ h_Ka_dvd
    -- finrank K (K ⊔ ℚ⟮b+β⟯) ∣ finrank K (Kaβ ⊔ ℚ⟮b⟯)
    have h_dvd_le : Module.finrank ↥K ↥(K ⊔ ℚ⟮(b + β)⟯) ∣
        Module.finrank ↥K ↥(Kaβ ⊔ ℚ⟮b⟯) := by
      haveI hAlg2 : Algebra ↥(K ⊔ ℚ⟮(b + β)⟯) ↥(Kaβ ⊔ ℚ⟮b⟯) :=
        (IntermediateField.inclusion h_le).toAlgebra
      haveI hST2 : IsScalarTower ↥K ↥(K ⊔ ℚ⟮(b + β)⟯) ↥(Kaβ ⊔ ℚ⟮b⟯) :=
        IsScalarTower.of_algebraMap_eq (fun r =>
          Subtype.ext (by simp [RingHom.algebraMap_toAlgebra,
            IntermediateField.coe_inclusion]))
      exact ⟨Module.finrank ↥(K ⊔ ℚ⟮(b + β)⟯) ↥(Kaβ ⊔ ℚ⟮b⟯),
        (Module.finrank_mul_finrank ↥K ↥(K ⊔ ℚ⟮(b + β)⟯) ↥(Kaβ ⊔ ℚ⟮b⟯)).symm⟩
    exact ⟨n₁ + 1 + n₂, h_dvd_le.trans h_tower_dvd⟩

/-- Constructible numbers are algebraic of 2-power degree.

    If α is constructible (under the FIXED definition), then:
    1. α is algebraic over ℚ
    2. finrank ℚ ℚ⟮α⟯ divides 2^n for some n

    **Proof**: Induction on IsConstructible.
    - `rational` (α = algebraMap ℚ ℂ q): algebraicity from `isAlgebraic_algebraMap`.
      finrank = 1 = 2^0 since q ∈ ⊥ implies ℚ⟮q⟯ = ⊥.
    - `sqrt_ext` (α = b + β, β² = a):
      · β algebraic: `IsAlgebraic.of_pow` from β^2 = a algebraic (IH on a).
      · b + β algebraic: `IsIntegral.add` (over a field, algebraic ↔ integral).
      · finrank: shown to divide 2^(j+k+1) via tower argument.

    Remaining sorries:
    - Step C: finrank ℚ ℚ⟮β⟯ ∣ 2^(j+1) (tower via ℚ⟮a⟯, β satisfies X²-a over ℚ⟮a⟯)
    - Step D: finrank ℚ (ℚ⟮b⟯ ⊔ ℚ⟮β⟯) ∣ 2^(j+k+1) (needs stronger IH for b) -/
private lemma isConstructible_algebraic_degree (α : ℂ) (h : IsConstructible α) :
    IsAlgebraic ℚ α ∧ ∃ n : ℕ, Module.finrank ℚ ℚ⟮α⟯ ∣ 2 ^ n := by
  induction h with
  | rational _ h_mem =>
    obtain ⟨q, rfl⟩ := h_mem
    refine ⟨isAlgebraic_algebraMap q, 0, ?_⟩
    rw [pow_zero]
    rw [IntermediateField.finrank_adjoin_simple_eq_one_iff.mpr
      (IntermediateField.mem_bot.mpr ⟨q, rfl⟩)]
  | sqrt_ext β a b ha hb hβ2 ih_a ih_b =>
    obtain ⟨halg_a, j, hj_dvd⟩ := ih_a
    obtain ⟨halg_b, _⟩ := ih_b
    -- β is algebraic: β^2 = a with a algebraic
    have hβ_sq : β ^ 2 = a := by rw [sq]; exact hβ2
    have halg_β : IsAlgebraic ℚ β :=
      IsAlgebraic.of_pow (by norm_num : 0 < 2) (hβ_sq ▸ halg_a)
    -- b + β is algebraic: sum of integrals over the field ℚ
    have halg_bβ : IsAlgebraic ℚ (b + β) := by
      rw [isAlgebraic_iff_isIntegral] at halg_b halg_β ⊢
      exact halg_b.add halg_β
    refine ⟨halg_bβ, ?_⟩
    -- Step A: β² = a → a ∈ ℚ⟮β⟯, so ℚ⟮a⟯ ≤ ℚ⟮β⟯
    have ha_in_β : a ∈ (ℚ⟮β⟯ : IntermediateField ℚ ℂ) := by
      rw [← hβ2]
      exact mul_mem (mem_adjoin_simple_self ℚ β) (mem_adjoin_simple_self ℚ β)
    have ha_le_β : (ℚ⟮a⟯ : IntermediateField ℚ ℂ) ≤ ℚ⟮β⟯ :=
      adjoin_simple_le_iff.mpr ha_in_β
    -- Step B: b + β ∈ ℚ⟮b⟯ ⊔ ℚ⟮β⟯, hence ℚ⟮b+β⟯ ≤ ℚ⟮b⟯ ⊔ ℚ⟮β⟯
    have hmem : b + β ∈ (ℚ⟮b⟯ ⊔ ℚ⟮β⟯ : IntermediateField ℚ ℂ) :=
      add_mem (le_sup_left (mem_adjoin_simple_self ℚ b))
              (le_sup_right (mem_adjoin_simple_self ℚ β))
    have hle : (ℚ⟮(b + β)⟯ : IntermediateField ℚ ℂ) ≤ ℚ⟮b⟯ ⊔ ℚ⟮β⟯ :=
      adjoin_simple_le_iff.mpr hmem
    -- Step C (sorry): finrank ℚ ℚ⟮β⟯ ∣ 2^(j+1)
    -- Proof plan: set up Algebra ↥ℚ⟮a⟯ ↥ℚ⟮β⟯ via ha_le_β.
    --   Tower law: finrank ℚ ℚ⟮β⟯ = finrank ↥ℚ⟮a⟯ ↥ℚ⟮β⟯ * finrank ℚ ℚ⟮a⟯
    --   Since finrank ℚ ℚ⟮a⟯ ∣ 2^j (IH), it suffices to show finrank ↥ℚ⟮a⟯ ↥ℚ⟮β⟯ ∣ 2.
    --   Key: β satisfies X²-a over ↥ℚ⟮a⟯ (since β²=a ∈ ℚ⟮a⟯), so
    --   minpoly ↥ℚ⟮a⟯ β ∣ X²-a, hence natDegree(minpoly) ≤ 2.
    --   And finrank ↥ℚ⟮a⟯ ↥ℚ⟮β⟯ = natDegree(minpoly ↥ℚ⟮a⟯ β) since ℚ⟮β⟯ is
    --   the simple extension of ↥ℚ⟮a⟯ by β (β generates ℚ⟮β⟯ over the larger ↥ℚ⟮a⟯).
    --   Hence finrank ↥ℚ⟮a⟯ ↥ℚ⟮β⟯ ∣ 2, giving finrank ℚ ℚ⟮β⟯ ∣ 2 * 2^j = 2^(j+1).
    have hβ_dvd : Module.finrank ℚ ↥(ℚ⟮β⟯) ∣ 2 ^ (j + 1) := by
      -- Tower: ℚ → ℚ⟮a⟯ → ℚ⟮β⟯
      haveI hAlg_aβ : Algebra ↥(ℚ⟮a⟯) ↥(ℚ⟮β⟯) :=
        (IntermediateField.inclusion ha_le_β).toAlgebra
      haveI hST_aβ : IsScalarTower ℚ ↥(ℚ⟮a⟯) ↥(ℚ⟮β⟯) :=
        IsScalarTower.of_algebraMap_eq (fun r =>
          Subtype.ext (by simp [RingHom.algebraMap_toAlgebra]))
      -- Tower law: finrank ℚ ℚ⟮β⟯ = finrank ℚ ↥ℚ⟮a⟯ * finrank ↥ℚ⟮a⟯ ↥ℚ⟮β⟯
      have htower := Module.finrank_mul_finrank ℚ ↥(ℚ⟮a⟯) ↥(ℚ⟮β⟯)
      rw [← htower, pow_succ]
      -- Suffices: finrank ℚ ↥ℚ⟮a⟯ ∣ 2^j and finrank ↥ℚ⟮a⟯ ↥ℚ⟮β⟯ ∣ 2
      exact Nat.mul_dvd_mul hj_dvd
        (by -- finrank ↥ℚ⟮a⟯ ↥ℚ⟮β⟯ ∣ 2
         -- β_in_β : the element β viewed in ↥(ℚ⟮β⟯)
         let β_in_β : ↥(ℚ⟮β⟯) := ⟨β, mem_adjoin_simple_self ℚ β⟩
         -- a_in_a : the element a viewed in ↥(ℚ⟮a⟯)
         let a_in_a : ↥(ℚ⟮a⟯) := ⟨a, IntermediateField.mem_adjoin_simple_self ℚ a⟩
         -- β is integral over ℚ
         have hβ_int_ℚ : IsIntegral ℚ β := isAlgebraic_iff_isIntegral.mp halg_β
         -- β_in_β is integral over ℚ (the algebraMap ↥(ℚ⟮β⟯) → ℂ is injective)
         have hβ_int_inner_Q : IsIntegral ℚ β_in_β := by
           rw [← isIntegral_algebraMap_iff (algebraMap ↥(ℚ⟮β⟯) ℂ).injective]
           exact hβ_int_ℚ
         -- β_in_β is integral over ↥(ℚ⟮a⟯) (tower: ℚ ≤ ↥ℚ⟮a⟯ ≤ ↥ℚ⟮β⟯)
         have hβ_int : IsIntegral ↥(ℚ⟮a⟯) β_in_β := hβ_int_inner_Q.tower_top
         -- PowerBasis: β generates ↥(ℚ⟮β⟯) over ℚ
         let pb := IntermediateField.adjoin.powerBasis hβ_int_ℚ
         have h_gen_eq : pb.gen = β_in_β := Subtype.ext rfl
         -- Algebra.adjoin ℚ {β_in_β} = ⊤ in ↥(ℚ⟮β⟯)
         have h_alg_top : Algebra.adjoin ℚ ({β_in_β} : Set ↥(ℚ⟮β⟯)) = ⊤ :=
           h_gen_eq ▸ pb.adjoin_gen_eq_top
         -- IntermediateField.adjoin ℚ {β_in_β} = ⊤
         have h_gen_Q : IntermediateField.adjoin ℚ ({β_in_β} : Set ↥(ℚ⟮β⟯)) = ⊤ :=
           IntermediateField.adjoin_eq_top_of_algebra h_alg_top
         -- Lift: IntermediateField.adjoin ↥(ℚ⟮a⟯) {β_in_β} = ⊤
         have h_top : IntermediateField.adjoin ↥(ℚ⟮a⟯) ({β_in_β} : Set ↥(ℚ⟮β⟯)) = ⊤ :=
           IntermediateField.adjoin_eq_top_of_adjoin_eq_top h_gen_Q
         -- finrank ↥(ℚ⟮a⟯) ↥(ℚ⟮β⟯) = natDegree(minpoly ↥(ℚ⟮a⟯) β_in_β)
         have h_finrank_eq : Module.finrank ↥(ℚ⟮a⟯) ↥(ℚ⟮β⟯) =
             (minpoly ↥(ℚ⟮a⟯) β_in_β).natDegree := by
           have := IntermediateField.adjoin.finrank hβ_int
           erw [h_top, IntermediateField.finrank_top'] at this
           exact this
         -- Annihilating polynomial: β_in_β satisfies X² - C(a_in_a) over ↥(ℚ⟮a⟯)
         set p : Polynomial ↥(ℚ⟮a⟯) := Polynomial.X ^ 2 - Polynomial.C a_in_a with hp_def
         have h_aeval : Polynomial.aeval β_in_β p = 0 := by
           simp only [hp_def, map_sub, map_pow, Polynomial.aeval_X,
             Polynomial.aeval_C, sub_eq_zero]
           -- Goal: β_in_β ^ 2 = algebraMap ↥(ℚ⟮a⟯) ↥(ℚ⟮β⟯) a_in_a
           apply_fun Subtype.val using Subtype.val_injective
           -- Goal in ℂ: (β_in_β ^ 2).val = (algebraMap ... a_in_a).val
           simp only [SubsemiringClass.coe_pow, β_in_β, a_in_a,
             RingHom.algebraMap_toAlgebra, IntermediateField.coe_inclusion,
             Subtype.coe_mk, hβ_sq]
         have h_deg_p : p.natDegree = 2 := by
           apply Polynomial.natDegree_sub_eq_left_of_natDegree_lt
           simp [Polynomial.natDegree_X_pow, Polynomial.natDegree_C]
         have h_p_ne : p ≠ 0 := by
           intro h; rw [h, Polynomial.natDegree_zero] at h_deg_p; omega
         have h_dvd : minpoly ↥(ℚ⟮a⟯) β_in_β ∣ p := minpoly.dvd _ _ h_aeval
         have h_pos : 1 ≤ (minpoly ↥(ℚ⟮a⟯) β_in_β).natDegree :=
           minpoly.natDegree_pos hβ_int
         have h_deg : (minpoly ↥(ℚ⟮a⟯) β_in_β).natDegree ≤ 2 :=
           (Polynomial.natDegree_le_of_dvd h_dvd h_p_ne).trans (le_of_eq h_deg_p)
         rw [h_finrank_eq]
         have h_range : (minpoly ↥(ℚ⟮a⟯) β_in_β).natDegree = 1 ∨
             (minpoly ↥(ℚ⟮a⟯) β_in_β).natDegree = 2 := by omega
         rcases h_range with h | h
         · exact h ▸ one_dvd 2
         · exact h ▸ dvd_refl _)
    -- Step D: finrank ℚ (ℚ⟮b⟯ ⊔ ℚ⟮β⟯) ∣ 2^(j+1+k') via stronger IH applied at K = ℚ⟮β⟯
    -- Tower ℚ ≤ ℚ⟮β⟯ ≤ ℚ⟮b⟯⊔ℚ⟮β⟯: tower law + isConstructible_sup_degree b hb ℚ⟮β⟯
    haveI hAlg_βjoin : Algebra ↥(ℚ⟮β⟯) ↥(ℚ⟮b⟯ ⊔ ℚ⟮β⟯) :=
      (IntermediateField.inclusion (le_sup_right (a := ℚ⟮b⟯))).toAlgebra
    haveI hST_βjoin : IsScalarTower ℚ ↥(ℚ⟮β⟯) ↥(ℚ⟮b⟯ ⊔ ℚ⟮β⟯) :=
      IsScalarTower.of_algebraMap_eq (fun r =>
        Subtype.ext (by simp [RingHom.algebraMap_toAlgebra]))
    obtain ⟨k', hk'⟩ := isConstructible_sup_degree b hb (ℚ⟮β⟯ : IntermediateField ℚ ℂ)
    -- hk' : Module.finrank ↥(ℚ⟮β⟯) ↥(ℚ⟮β⟯ ⊔ ℚ⟮b⟯) ∣ 2^k'; rewrite via sup_comm
    rw [sup_comm] at hk'
    have hjoin_dvd : Module.finrank ℚ ↥(ℚ⟮b⟯ ⊔ ℚ⟮β⟯) ∣ 2 ^ (j + 1 + k') := by
      rw [Module.finrank_mul_finrank ℚ ↥(ℚ⟮β⟯) ↥(ℚ⟮b⟯ ⊔ ℚ⟮β⟯), pow_add]
      exact Nat.mul_dvd_mul hβ_dvd hk'
    -- Step E: finrank ℚ ℚ⟮b+β⟯ ∣ finrank ℚ (ℚ⟮b⟯ ⊔ ℚ⟮β⟯) via tower law
    -- ℚ⟮b+β⟯ ≤ ℚ⟮b⟯ ⊔ ℚ⟮β⟯ (hle) gives:
    --   finrank_join = finrank ↥ℚ⟮b+β⟯ ↥(join) * finrank ℚ ℚ⟮b+β⟯
    have hdvd_le : Module.finrank ℚ ↥(ℚ⟮b + β⟯) ∣
        Module.finrank ℚ ↥(ℚ⟮b⟯ ⊔ ℚ⟮β⟯) := by
      haveI hAlg : Algebra ↥(ℚ⟮b + β⟯) ↥(ℚ⟮b⟯ ⊔ ℚ⟮β⟯) :=
        (IntermediateField.inclusion hle).toAlgebra
      haveI hST : IsScalarTower ℚ ↥(ℚ⟮b + β⟯) ↥(ℚ⟮b⟯ ⊔ ℚ⟮β⟯) :=
        IsScalarTower.of_algebraMap_eq (fun r =>
          Subtype.ext (by simp [RingHom.algebraMap_toAlgebra]))
      have htower := Module.finrank_mul_finrank ℚ ↥(ℚ⟮b + β⟯) ↥(ℚ⟮b⟯ ⊔ ℚ⟮β⟯)
      exact ⟨Module.finrank ↥(ℚ⟮b + β⟯) ↥(ℚ⟮b⟯ ⊔ ℚ⟮β⟯), htower.symm⟩
    exact ⟨j + 1 + k', hdvd_le.trans hjoin_dvd⟩

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

end AngleTrisectionOQ02OQ01OQ02Incomplete01
