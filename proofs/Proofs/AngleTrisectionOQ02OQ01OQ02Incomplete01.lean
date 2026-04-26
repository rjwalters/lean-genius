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

## Progress: 1 false sorry → 3 true sorries (2 targeted + 1 out-of-scope)

Session update: The single sorry in `isConstructible_algebraic_degree` has been replaced
with a structured proof skeleton (Steps A–E) that:
1. Proves a ∈ ℚ⟮β⟯ and ℚ⟮a⟯ ≤ ℚ⟮β⟯ (Step A)
2. Proves b+β ∈ ℚ⟮b⟯ ⊔ ℚ⟮β⟯ and ℚ⟮b+β⟯ ≤ ℚ⟮b⟯ ⊔ ℚ⟮β⟯ (Step B)
3. Reduces the finrank ∣ 2^(j+k+1) claim to two targeted sorries (Steps C, D)
4. Attempts to prove finrank ℚ⟮b+β⟯ ∣ finrank (join) via algebra instances (Step E)

## Remaining Sorries

1. `hβ_dvd` (line ~162): finrank ℚ ℚ⟮β⟯ ∣ 2^(j+1)
   Proof plan: ℚ⟮a⟯ ≤ ℚ⟮β⟯, tower law gives finrank_β = [ℚ⟮β⟯:ℚ⟮a⟯] * 2^j.
   β satisfies X²-a over ℚ⟮a⟯ → [ℚ⟮β⟯:ℚ⟮a⟯] ≤ 2 → [ℚ⟮β⟯:ℚ⟮a⟯] ∣ 2 → finrank_β ∣ 2^(j+1).
   Needs: Algebra (↥ℚ⟮a⟯) (↥ℚ⟮β⟯) instance from ha_le_β, bound on [ℚ⟮β⟯:ℚ⟮a⟯] via minpoly.

2. `hjoin_dvd` (line ~169): finrank ℚ (ℚ⟮b⟯ ⊔ ℚ⟮β⟯) ∣ 2^(j+k+1)
   Proof plan: tower via ℚ⟮β⟯ gives finrank_join = [join:ℚ⟮β⟯] * finrank_β.
   Need [join:ℚ⟮β⟯] ∣ 2^k. This requires STRONGER IH for b: not just finrank ℚ ℚ⟮b⟯ = 2^k,
   but "for any K/ℚ, finrank K K⟮b⟯ divides a power of 2". Current IH is too weak.
   Alternative: reformulate `isConstructible_algebraic_degree` with stronger induction.

3. `wantzel_galois_iff` (out-of-scope): Requires full Galois correspondence + 2-group structure.
   Estimated: 500+ lines of new Galois theory infrastructure. Out of scope.

## Key Mathematical Gap

The `hjoin_dvd` sorry reveals that the induction in `isConstructible_algebraic_degree` is
too weak. The statement "finrank ℚ ℚ⟮b⟯ = 2^k" does not imply that b's degree over any
extension of ℚ divides a power of 2. A STRONGER induction is needed, e.g.:
  "For all IsConstructible b and for any K/ℚ with 2-power degree, finrank K K⟮b⟯ ∣ 2^k"

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
-- PART 2: Key Structural Lemma (SORRY — tower degree property)
-- ============================================================

/-- Constructible numbers are algebraic of 2-power degree.

    If α is constructible (under the FIXED definition), then:
    1. α is algebraic over ℚ
    2. finrank ℚ ℚ⟮α⟯ = 2^n for some n

    **Proof**: Induction on IsConstructible.
    - `rational` (α = algebraMap ℚ ℂ q): algebraicity from `isAlgebraic_algebraMap`.
      finrank = 1 = 2^0 since q ∈ ⊥ implies ℚ⟮q⟯ = ⊥.
    - `sqrt_ext` (α = b + β, β² = a):
      · β algebraic: `IsAlgebraic.of_pow` from β^2 = a algebraic (IH on a).
      · b + β algebraic: `IsIntegral.add` (over a field, algebraic ↔ integral).
      · finrank: shown to divide 2^(j+k+1) via tower argument (sorry below),
        then `Nat.dvd_prime_pow` extracts the exact power.

    Remaining sorry: finrank ℚ ℚ⟮b+β⟯ ∣ 2^(j+k+1) (tower bound).
    Tower: ℚ ⊆ ℚ⟮a⟯ (2^j) ⊆ ℚ⟮a⟯⊔ℚ⟮β⟯ (×2, β²=a∈ℚ⟮a⟯) ⊆ (...)⊔ℚ⟮b⟯ (×2^k); b+β in top. -/
private lemma isConstructible_algebraic_degree (α : ℂ) (h : IsConstructible α) :
    IsAlgebraic ℚ α ∧ ∃ n : ℕ, Module.finrank ℚ ℚ⟮α⟯ = 2 ^ n := by
  induction h with
  | rational _ h_mem =>
    obtain ⟨q, rfl⟩ := h_mem
    refine ⟨isAlgebraic_algebraMap q, 0, ?_⟩
    rw [pow_zero]
    exact IntermediateField.finrank_adjoin_simple_eq_one_iff.mpr
      (IntermediateField.mem_bot.mpr ⟨q, rfl⟩)
  | sqrt_ext β a b _ _ hβ2 ih_a ih_b =>
    obtain ⟨halg_a, j, _hj⟩ := ih_a
    obtain ⟨halg_b, k, _hk⟩ := ih_b
    -- β is algebraic: β^2 = a with a algebraic
    have hβ_sq : β ^ 2 = a := by rw [sq]; exact hβ2
    have halg_β : IsAlgebraic ℚ β :=
      IsAlgebraic.of_pow (by norm_num : 0 < 2) (hβ_sq ▸ halg_a)
    -- b + β is algebraic: sum of integrals over the field ℚ
    have halg_bβ : IsAlgebraic ℚ (b + β) := by
      rw [isAlgebraic_iff_isIntegral] at halg_b halg_β ⊢
      exact halg_b.add halg_β
    refine ⟨halg_bβ, ?_⟩
    -- Show Module.finrank ℚ ℚ⟮b+β⟯ ∣ 2^(j+k+1), then Nat.dvd_prime_pow gives exact power
    suffices hdvd : Module.finrank ℚ ℚ⟮(b + β)⟯ ∣ 2 ^ (j + k + 1) by
      obtain ⟨m, _, hm⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp hdvd
      exact ⟨m, hm⟩
    -- Tower argument: show finrank ℚ ℚ⟮b+β⟯ ∣ 2^(j+k+1)
    --
    -- Step A: β² = a ∈ ℚ⟮a⟯ ⟹ a ∈ ℚ⟮β⟯ (close under ·), so ℚ⟮a⟯ ≤ ℚ⟮β⟯
    have ha_in_β : a ∈ (ℚ⟮β⟯ : IntermediateField ℚ ℂ) := by
      rw [← hβ2]
      exact mul_mem (mem_adjoin_simple_self ℚ β) (mem_adjoin_simple_self ℚ β)
    have ha_le_β : (ℚ⟮a⟯ : IntermediateField ℚ ℂ) ≤ ℚ⟮β⟯ :=
      adjoin_simple_le_iff.mpr ha_in_β
    -- Step B: b + β ∈ ℚ⟮b⟯ ⊔ ℚ⟮β⟯, hence ℚ⟮b+β⟯ ≤ ℚ⟮b⟯ ⊔ ℚ⟮β⟯
    have hmem : b + β ∈ (ℚ⟮b⟯ ⊔ ℚ⟮β⟯ : IntermediateField ℚ ℂ) :=
      add_mem (mem_sup_left (mem_adjoin_simple_self ℚ b))
              (mem_sup_right (mem_adjoin_simple_self ℚ β))
    have hle : (ℚ⟮(b + β)⟯ : IntermediateField ℚ ℂ) ≤ ℚ⟮b⟯ ⊔ ℚ⟮β⟯ :=
      adjoin_simple_le_iff.mpr hmem
    -- Step C: finrank ℚ ℚ⟮β⟯ ∣ 2^(j+1)
    -- Proof: ℚ⟮a⟯ ≤ ℚ⟮β⟯ gives tower law
    --   finrank ℚ ℚ⟮β⟯ = [ℚ⟮β⟯:ℚ⟮a⟯] * finrank ℚ ℚ⟮a⟯ = [ℚ⟮β⟯:ℚ⟮a⟯] * 2^j
    -- β satisfies X² - a over ℚ⟮a⟯ (since a = β² ∈ ℚ⟮a⟯), so [ℚ⟮β⟯:ℚ⟮a⟯] ≤ 2
    -- Therefore [ℚ⟮β⟯:ℚ⟮a⟯] ∣ 2, giving finrank ℚ ℚ⟮β⟯ ∣ 2 * 2^j = 2^(j+1)
    have hβ_dvd : Module.finrank ℚ ↥(ℚ⟮β⟯) ∣ 2 ^ (j + 1) := by
      sorry -- tower via ℚ⟮a⟯: [ℚ⟮β⟯:ℚ⟮a⟯] ≤ 2 from β²=a, [ℚ⟮β⟯:ℚ⟮a⟯] ∣ 2, finrank_β = [ℚ⟮β⟯:ℚ⟮a⟯] * 2^j
    -- Step D: finrank ℚ (ℚ⟮b⟯ ⊔ ℚ⟮β⟯) ∣ 2^(j+k+1)
    -- Proof: tower through ℚ⟮β⟯
    --   finrank_join = [join:ℚ⟮β⟯] * finrank_β ∣ 2^k * 2^(j+1) = 2^(j+k+1)
    -- where [join:ℚ⟮β⟯] ∣ 2^k because b has 2^k-power degree over ℚ
    -- (this uses the stronger IH: for any K/ℚ, finrank K K⟮b⟯ divides a power of 2)
    have hjoin_dvd : Module.finrank ℚ ↥(ℚ⟮b⟯ ⊔ ℚ⟮β⟯) ∣ 2 ^ (j + k + 1) := by
      sorry -- tower via ℚ⟮β⟯: [join:ℚ⟮β⟯] ∣ 2^k (needs stronger IH on b), finrank_β ∣ 2^(j+1)
    -- Step E: finrank ℚ⟮b+β⟯ ∣ finrank (ℚ⟮b⟯ ⊔ ℚ⟮β⟯) via hle (tower law for inclusions)
    -- ℚ⟮b+β⟯ ≤ ℚ⟮b⟯ ⊔ ℚ⟮β⟯ gives: finrank_join = [join:ℚ⟮b+β⟯] * finrank_{b+β}
    have hdvd_le : Module.finrank ℚ ↥(ℚ⟮b + β⟯) ∣
        Module.finrank ℚ ↥(ℚ⟮b⟯ ⊔ ℚ⟮β⟯) := by
      haveI hAlg : Algebra ↥(ℚ⟮b + β⟯) ↥(ℚ⟮b⟯ ⊔ ℚ⟮β⟯) :=
        (IntermediateField.inclusion hle).toAlgebra
      haveI hST : IsScalarTower ℚ ↥(ℚ⟮b + β⟯) ↥(ℚ⟮b⟯ ⊔ ℚ⟮β⟯) :=
        IsScalarTower.of_algebraMap_eq (fun r =>
          Subtype.ext (by simp [RingHom.algebraMap_toAlgebra]))
      exact ⟨Module.finrank ↥(ℚ⟮b + β⟯) ↥(ℚ⟮b⟯ ⊔ ℚ⟮β⟯),
             (Module.finrank_mul_finrank ℚ ↥(ℚ⟮b + β⟯) ↥(ℚ⟮b⟯ ⊔ ℚ⟮β⟯)).symm⟩
    exact hdvd_le.trans hjoin_dvd

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
