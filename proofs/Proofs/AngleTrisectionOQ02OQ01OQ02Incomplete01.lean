/-
Completing the Wantzel-Galois Constructibility Proof
Open Question: angle-trisection-oq-02-oq-01-oq-02-incomplete-01

## Definition Fix (Session 26)

The original `sqrt_ext` constructor required `IsConstructible β` as a precondition,
making constructible numbers exactly the rationals. This was mathematically wrong
(√2 should be constructible) and made `wantzel_galois_iff` false.

**Fixed definition**: `sqrt_ext` no longer requires `IsConstructible β`. The square root β
of a constructible number a is constructible (along with any b + β for constructible b).

Under the fixed definition:
- √2 IS constructible (a = 2 rational, b = 0, β = √2, β² = 2 ✓)
- `isConstructible_mem_range` is no longer provable (correct!)
- `wantzel_galois_iff` is now a TRUE statement (not false as before)

## Progress: 1 false sorry → 2 true sorries

1. `isConstructible_algebraic_degree` — tower degree property (TRUE, needs ~120 lines)
2. `wantzel_galois_iff`               — full Galois correspondence (TRUE, needs 500+ lines)

## Remaining Sorries

1. `isConstructible_algebraic_degree`: IsConstructible α → IsAlgebraic ℚ α ∧ ∃ n, finrank ℚ ℚ⟮α⟯ = 2^n
   Proof sketch: Induction on IsConstructible.
   - rational case: algebraic (minpoly = X - C q), finrank = 1 = 2^0
   - sqrt_ext case: β² = a, a constructible (IH: finrank ℚ ℚ⟮a⟯ = 2^j), b constructible
     (IH: finrank ℚ ℚ⟮b⟯ = 2^k). β satisfies X² - a over ℚ(a), so [ℚ(β):ℚ(a)] ≤ 2.
     Tower law: finrank ℚ ℚ⟮b+β⟯ | finrank ℚ ℚ(b,β) ≤ finrank ℚ ℚ⟮b⟯ * finrank ℚ ℚ⟮β⟯ | 2^(k+j+1).
   Estimated: ~120 lines. Needs tower law lemmas from Mathlib.

2. `wantzel_galois_iff`: Requires full Galois correspondence + 2-group structure.
   Estimated: 500+ lines of new Galois theory infrastructure. Out of scope.

## Status: 2 sorries (both TRUE), 0 axioms
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

/-- **Strong induction hypothesis**: every constructible α lives in a 2-power
    extension of any given 2-power base field F.

    The direct induction fails because in the `sqrt_ext` case the compositum degree
    over ℚ cannot be controlled from the IH finranks alone. This stronger statement
    threads a single growing 2-power field through the recursion.

    **Proof** (sqrt_ext case α = b+β, β²=a):
    1. Apply ih_a to F → Ka ≥ F, a ∈ Ka, finrank ℚ Ka = 2^ja
    2. β integral over ↥Ka (satisfies X²-a, a ∈ Ka); form Kβ := (↥Ka)⟮β⟯
       as `IntermediateField ↥Ka ℂ` (base field = ↥Ka, NOT ℚ)
    3. finrank ↥Ka ↥Kβ = natDegree(minpoly ↥Ka β) ≤ 2 → divides 2
    4. Tower: finrank ℚ ↥Kβ = finrank ℚ ↥Ka · finrank ↥Ka ↥Kβ
       (instances automatic since Kβ : IntermediateField ↥Ka ℂ)
       = 2^ja · 2^e = 2^(ja+e) for some e ≤ 1
    5. Apply ih_b to Kβ.restrictScalars ℚ → Kb, b ∈ Kb, finrank Kb = 2^jb
    6. G = Kb: β ∈ Kβ ≤ Kb, b ∈ Kb → b+β ∈ Kb -/
private lemma isConstructible_exists_2power_ext (α : ℂ) (h : IsConstructible α) :
    ∀ (F : IntermediateField ℚ ℂ) (n : ℕ), Module.finrank ℚ ↥F = 2 ^ n →
    ∃ (G : IntermediateField ℚ ℂ) (m : ℕ),
      F ≤ G ∧ (α : ℂ) ∈ (G : Set ℂ) ∧ Module.finrank ℚ ↥G = 2 ^ m := by
  induction h with
  | rational _ h_mem =>
    -- α = algebraMap ℚ ℂ q ∈ F already (every intermediate field contains ℚ)
    intro F n hF
    obtain ⟨q, rfl⟩ := h_mem
    exact ⟨F, n, le_refl F, IntermediateField.algebraMap_mem F q, hF⟩
  | sqrt_ext β a b _ _ hβ2 ih_a ih_b =>
    intro F n hF
    -- Step 1: Ka ≥ F with a ∈ Ka and finrank ℚ Ka = 2^ja
    obtain ⟨Ka, ja, hF_Ka, ha_Ka, hKa⟩ := ih_a F n hF
    -- Step 2: β is integral over ↥Ka (β² = a ∈ Ka)
    have hβ_sq : β ^ 2 = a := by rw [sq]; exact hβ2
    have hβ_integral : IsIntegral ↥Ka (β : ℂ) := by
      -- β² = a ∈ Ka, so β² is integral over ↥Ka; then β is integral
      apply IsIntegral.of_pow (n := 2) (by norm_num)
      have : (β ^ 2 : ℂ) = algebraMap ↥Ka ℂ ⟨a, ha_Ka⟩ := by
        simp only [hβ_sq, IntermediateField.algebraMap_apply]
      rw [this]; exact isIntegral_algebraMap
    -- Step 3: form Kβ := (↥Ka)⟮β⟯ : IntermediateField ↥Ka ℂ
    -- finrank ↥Ka ↥Kβ ≤ 2 via natDegree(minpoly ↥Ka β) bound
    let Kβ : IntermediateField ↥Ka ℂ := (↥Ka)⟮β⟯
    have hKβ_finrank_le : Module.finrank ↥Ka ↥Kβ ≤ 2 := by
      show Module.finrank ↥Ka ↥((↥Ka)⟮β⟯) ≤ 2
      rw [IntermediateField.adjoin.finrank hβ_integral]
      have hdvd : minpoly ↥Ka β ∣ X ^ 2 - C ⟨a, ha_Ka⟩ :=
        minpoly.dvd ↥Ka β (by
          simp only [map_sub, map_pow, aeval_X, aeval_C]
          show β ^ 2 - algebraMap ↥Ka ℂ ⟨a, ha_Ka⟩ = 0
          simp [hβ_sq, IntermediateField.algebraMap_apply])
      have hne : (X ^ 2 - C (⟨a, ha_Ka⟩ : ↥Ka) : (↥Ka)[X]) ≠ 0 :=
        (monic_X_pow_sub_C _ (by norm_num)).ne_zero
      calc (minpoly ↥Ka β).natDegree
          ≤ (X ^ 2 - C (⟨a, ha_Ka⟩ : ↥Ka)).natDegree :=
            Polynomial.natDegree_le_of_dvd hdvd hne
        _ = 2 := by simp
    -- FiniteDimensional instances required for finrank_pos and finrank_mul_finrank
    haveI hKa_finite : FiniteDimensional ℚ ↥Ka :=
      Module.finite_of_finrank_pos (hKa ▸ pow_pos (by norm_num : (0:ℕ) < 2) ja)
    haveI hKβ_fd : FiniteDimensional ↥Ka ↥Kβ :=
      adjoin.finiteDimensional hβ_integral
    -- Step 4: extract e with finrank ↥Ka ↥Kβ = 2^e (e ≤ 1)
    have hKβ_pos : 0 < Module.finrank ↥Ka ↥Kβ := Module.finrank_pos
    have hKβ_dvd : Module.finrank ↥Ka ↥Kβ ∣ 2 ^ 1 := by
      rw [pow_one]
      have hlo : 1 ≤ Module.finrank ↥Ka ↥Kβ := hKβ_pos
      have hhi : Module.finrank ↥Ka ↥Kβ ≤ 2 := hKβ_finrank_le
      interval_cases (Module.finrank ↥Ka ↥Kβ) <;> norm_num
    obtain ⟨e, he_le, hKβ_rel⟩ :=
      (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp hKβ_dvd
    -- Step 5: tower law — instances are automatic from Kβ : IntermediateField ↥Ka ℂ
    -- finrank ℚ ↥Kβ = finrank ℚ ↥Ka · finrank ↥Ka ↥Kβ = 2^ja · 2^e = 2^(ja+e)
    have hKβ_finrank : Module.finrank ℚ ↥Kβ = 2 ^ (ja + e) :=
      calc Module.finrank ℚ ↥Kβ
          = Module.finrank ℚ ↥Ka * Module.finrank ↥Ka ↥Kβ :=
            (Module.finrank_mul_finrank ℚ ↥Ka ↥Kβ).symm
        _ = 2 ^ ja * 2 ^ e := by rw [hKa, hKβ_rel]
        _ = 2 ^ (ja + e) := (pow_add 2 ja e).symm
    -- Step 5b: Kβ.restrictScalars ℚ : IntermediateField ℚ ℂ
    -- has finrank ℚ = finrank ℚ ↥Kβ = 2^(ja+e)
    have hKβRS_finrank : Module.finrank ℚ ↥(Kβ.restrictScalars ℚ) = 2 ^ (ja + e) :=
      hKβ_finrank
    -- Ka ≤ Kβ.restrictScalars ℚ (↥Ka is the base field of Kβ, hence every element of Ka ∈ Kβ)
    have hKa_KβRS : Ka ≤ Kβ.restrictScalars ℚ := by
      intro x hx
      simp only [IntermediateField.mem_restrictScalars]
      show x ∈ (↥Ka)⟮β⟯
      -- x ∈ Ka → algebraMap ↥Ka ℂ ⟨x,hx⟩ = x ∈ (↥Ka)⟮β⟯ (base field is always contained)
      have hmem := ((↥Ka)⟮β⟯).algebraMap_mem (⟨x, hx⟩ : ↥Ka)
      simp only [IntermediateField.algebraMap_apply] at hmem
      exact hmem
    -- β ∈ Kβ.restrictScalars ℚ
    have hβ_KβRS : (β : ℂ) ∈ (Kβ.restrictScalars ℚ : Set ℂ) := by
      change β ∈ Kβ
      exact IntermediateField.mem_adjoin_simple_self ↥Ka β
    -- Step 6: apply ih_b to Kβ.restrictScalars ℚ
    obtain ⟨Kb, jb, hKβRS_Kb, hb_Kb, hKb⟩ :=
      ih_b (Kβ.restrictScalars ℚ) (ja + e) hKβRS_finrank
    -- b + β ∈ Kb
    have hβ_Kb : (β : ℂ) ∈ (Kb : Set ℂ) := hKβRS_Kb hβ_KβRS
    exact ⟨Kb, jb,
           le_trans (le_trans hF_Ka hKa_KβRS) hKβRS_Kb,
           add_mem hb_Kb hβ_Kb, hKb⟩

/-- Constructible numbers are algebraic of 2-power degree.

    **Proof**: Apply `isConstructible_exists_2power_ext` with F = ⊥ (finrank = 1 = 2^0)
    to get G ≥ ⊥ with α ∈ G and finrank ℚ G = 2^m. Then:
    - FiniteDimensional ℚ ↥G → α algebraic (every element of a fin-dim extension is algebraic)
    - ℚ⟮α⟯ ≤ G → finrank ℚ ℚ⟮α⟯ ∣ 2^m → Nat.dvd_prime_pow gives exact power -/
private lemma isConstructible_algebraic_degree (α : ℂ) (h : IsConstructible α) :
    IsAlgebraic ℚ α ∧ ∃ n : ℕ, Module.finrank ℚ ℚ⟮α⟯ = 2 ^ n := by
  obtain ⟨G, m, _, hα_G, hGm⟩ :=
    isConstructible_exists_2power_ext α h ⊥ 0 (by
      simp [IntermediateField.finrank_bot])
  -- G is finite-dimensional over ℚ
  haveI hGfin : FiniteDimensional ℚ ↥G :=
    Module.finite_of_finrank_pos (hGm ▸ pow_pos (by norm_num : (0:ℕ) < 2) m)
  -- α ∈ G → α algebraic: every element of a fin-dim extension is integral
  have halg : IsAlgebraic ℚ α := by
    obtain ⟨p, hp_ne, hp_eval⟩ :=
      (Algebra.IsAlgebraic.of_finite ℚ ↥G).isAlgebraic (⟨α, hα_G⟩ : ↥G)
    refine ⟨p, hp_ne, ?_⟩
    -- G.val is the IntermediateField AlgHom (G.subtype resolves to Subsemiring.subtype)
    let φ : ↥G →ₐ[ℚ] ℂ := G.val
    -- aeval_algHom_apply : aeval (f x) p = f (aeval x p)
    have key := Polynomial.aeval_algHom_apply φ (⟨α, hα_G⟩ : ↥G) p
    -- key : aeval (φ ⟨α, hα_G⟩) p = φ (aeval ⟨α, hα_G⟩ p)
    rw [hp_eval, map_zero] at key
    -- key : aeval (φ ⟨α, hα_G⟩) p = 0; val_mk : G.val ⟨α, hα_G⟩ = α
    simp only [φ, IntermediateField.val_mk] at key
    exact key
  refine ⟨halg, ?_⟩
  -- ℚ⟮α⟯ ≤ G → finrank ℚ ℚ⟮α⟯ ∣ 2^m → extract power
  have hle : ℚ⟮α⟯ ≤ G := IntermediateField.adjoin_simple_le_iff.mpr hα_G
  have hdvd := hGm ▸ IntermediateField.finrank_dvd_of_le_right hle
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp hdvd
  exact ⟨k, hk⟩

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
    1. α constructible → α algebraic, finrank ℚ ℚ⟮α⟯ = 2^n.
    2. finrank ℚ ℚ⟮α⟯ = natDegree (minpoly ℚ α) (by `IntermediateField.adjoin.finrank`).
    3. minpoly ℚ α ∣ p (by `minpoly.dvd`).
    4. p irreducible → p associate to minpoly ℚ α → natDegree p = 2^n.
    Contradicts ¬ DegreePowerOfTwo p. -/
theorem not_constructible_of_bad_degree {p : ℚ[X]} (hp : Irreducible p)
    (hdeg : ¬ DegreePowerOfTwo p) :
    ∀ α : ℂ, Polynomial.aeval α p = 0 →
    ¬ IsConstructible α := by
  intro α hpα hcα
  -- Step 1: α algebraic, finrank ℚ ℚ⟮α⟯ = 2^n
  obtain ⟨halg, n, hn⟩ := isConstructible_algebraic_degree α hcα
  -- α is integral (algebraic over a field ↔ integral)
  have hint : IsIntegral ℚ α := isAlgebraic_iff_isIntegral.mp halg
  -- Step 2: natDegree (minpoly ℚ α) = Module.finrank ℚ ℚ⟮α⟯
  have hmind : (minpoly ℚ α).natDegree = Module.finrank ℚ ℚ⟮α⟯ :=
    (IntermediateField.adjoin.finrank hint).symm
  -- Step 3: minpoly ℚ α ∣ p
  have hdvd : minpoly ℚ α ∣ p := minpoly.dvd ℚ α hpα
  -- Step 4: p irreducible + minpoly ∣ p → natDegree p = 2^n
  obtain ⟨c, hc⟩ := hdvd
  rcases hp.isUnit_or_isUnit hc with h1 | h2
  · -- minpoly ℚ α is a unit: impossible since natDegree = finrank ≥ 1 (algebraic element)
    have hunit_zero : (minpoly ℚ α).natDegree = 0 :=
      Polynomial.natDegree_eq_zero_of_isUnit h1
    have h_fr_zero : Module.finrank ℚ ℚ⟮α⟯ = 0 := hmind ▸ hunit_zero
    rw [hn] at h_fr_zero
    exact absurd h_fr_zero (Nat.two_pow_pos n).ne'
  · -- c is a unit → natDegree p = natDegree (minpoly ℚ α) = 2^n
    apply hdeg; use n
    have hc_deg : c.natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit h2
    have hne : minpoly ℚ α ≠ 0 := minpoly.ne_zero hint
    have hcne : c ≠ 0 := IsUnit.ne_zero h2
    rw [hc, Polynomial.natDegree_mul hne hcne, hmind, hn, hc_deg, add_zero]

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

/-- **[SORRY 2/2] Wantzel-Galois Theorem**: α constructible ↔ Gal(minpoly(ℚ,α)) is a 2-group.

    Under the FIXED IsConstructible definition, this is a TRUE statement. Previously
    (old definition with IsConstructible β precondition), it was FALSE since constructible
    meant rational, making the ← direction fail (e.g., X² - 2 has 2-group Gal but √2
    is not rational, hence "not constructible" under the old definition).

    Proof requires:
    1. Full Fundamental Theorem of Galois Theory (FTGT)
    2. 2-power degree extensions ↔ towers of quadratics
    3. Connection between constructibility and such towers
    Estimated: 500+ lines. Out of scope for this session. -/
theorem wantzel_galois_iff {p : ℚ[X]} (hp : Irreducible p) (α : ℂ)
    (hα : Polynomial.aeval α p = 0) :
    IsConstructible α ↔ IsTwoGroup p.Gal := by
  sorry -- TRUE under fixed definition; requires FTGT + tower characterization

end AngleTrisectionOQ02OQ01OQ02Incomplete01
