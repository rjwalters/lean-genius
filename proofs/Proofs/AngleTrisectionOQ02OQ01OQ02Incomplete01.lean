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

## Progress: Session 28 — eliminated tower divisibility sorry

1. `isConstructible_algebraic_degree` — PROVED (via `pow2_containing_field` sequential tower)
2. `wantzel_galois_iff`               — SORRY (full Galois correspondence, 500+ lines)

## Session 28 Changes

Added two helper lemmas before the structural theorem:
- `isConstructible_algebraic`: standalone algebraicity proof by induction
- `pow2_containing_field`: sequential tower — given IsConstructible α and a 2-power
  intermediate field F, extends F to a 2-power field G containing α. Uses the tower
  ℚ ≤ G_a ≤ G_ab ≤ G_ab(β) where [G_ab(β):G_ab] ∈ {1,2} → 2-power rank.

Replaced the sorry in `isConstructible_algebraic_degree` with: apply
`pow2_containing_field` starting from ⊥, get G with b+β ∈ G and [G:ℚ] = 2^n_G,
use `finrank_dvd_of_le_right` to get [ℚ(b+β):ℚ] ∣ 2^n_G, extract power via
`Nat.dvd_prime_pow`.

## Remaining Sorries

1. `wantzel_galois_iff`: Requires full Galois correspondence + 2-group structure.
   Estimated: 500+ lines of new Galois theory infrastructure. Out of scope.

## Status: 1 sorry (TRUE but out of scope), 0 axioms
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
-- PART 2: Helper Lemmas for Tower Degree
-- ============================================================

/-- Constructible numbers are algebraic over ℚ. -/
private lemma isConstructible_algebraic (α : ℂ) (h : IsConstructible α) :
    IsAlgebraic ℚ α := by
  induction h with
  | rational _ h_mem =>
    obtain ⟨q, rfl⟩ := h_mem
    exact isAlgebraic_algebraMap q
  | sqrt_ext β a b _ _ hβ2 ih_a ih_b =>
    have hβ_sq : β ^ 2 = a := by rw [sq]; exact hβ2
    have halg_β : IsAlgebraic ℚ β :=
      IsAlgebraic.of_pow (by norm_num : 0 < 2) (hβ_sq ▸ ih_a)
    rw [isAlgebraic_iff_isIntegral] at ih_b halg_β ⊢
    exact ih_b.add halg_β

/-- Sequential tower lemma: given a constructible α and a 2-power degree
    intermediate field F, there exists a 2-power degree extension G ≥ F with α ∈ G.

    **Proof**: Induction on IsConstructible, building the tower sequentially:
    - rational: α ∈ F already (rationals are in every intermediate field)
    - sqrt_ext (α = b+β, β²=a): extend F → G_a ∋ a → G_ab ∋ b → G_abβ ∋ β,
      using the tower law: [G_abβ : ℚ] = [G_abβ : G_ab] * [G_ab : ℚ] = d * 2^n_ab,
      where d = [G_ab(β) : G_ab] ≤ 2, so d ∈ {1,2} and [G_abβ : ℚ] = 2^l. -/
private lemma pow2_containing_field (α : ℂ) (h : IsConstructible α) :
    ∀ (F : IntermediateField ℚ ℂ) (m : ℕ),
    Module.finrank ℚ F = 2 ^ m →
    ∃ (G : IntermediateField ℚ ℂ) (n : ℕ),
      F ≤ G ∧ α ∈ G ∧ Module.finrank ℚ G = 2 ^ n := by
  induction h with
  | rational _ h_mem =>
    intro F m hFm
    obtain ⟨q, rfl⟩ := h_mem
    exact ⟨F, m, le_refl F, F.algebraMap_mem q, hFm⟩
  | sqrt_ext β a b ha hb hβ2 ih_a ih_b =>
    intro F m hFm
    -- Step 1: extend F to G_a containing a
    obtain ⟨G_a, n_a, hFGa, ha_in_Ga, hn_a⟩ := ih_a F m hFm
    -- Step 2: extend G_a to G_ab containing b
    obtain ⟨G_ab, n_ab, hGaGab, hb_in_Gab, hn_ab⟩ := ih_b G_a n_a hn_a
    -- a ∈ G_ab since a ∈ G_a and G_a ≤ G_ab
    have ha_in_Gab : a ∈ G_ab := hGaGab ha_in_Ga
    -- β² = a
    have hβ_sq : β ^ 2 = a := by rw [sq]; exact hβ2
    -- β satisfies X² - C(⟨a, ha_in_Gab⟩) over G_ab
    have hβ_root : Polynomial.aeval β
        (X ^ 2 - C (⟨a, ha_in_Gab⟩ : ↥G_ab) : (↥G_ab)[X]) = 0 := by
      have hcast : (algebraMap (↥G_ab) ℂ) ⟨a, ha_in_Gab⟩ = a := rfl
      simp only [map_sub, map_pow, aeval_X, aeval_C, hcast]
      rw [show β ^ 2 = a from hβ_sq, sub_self]
    have hXsq_ne : (X ^ 2 - C (⟨a, ha_in_Gab⟩ : ↥G_ab) : (↥G_ab)[X]) ≠ 0 :=
      X_pow_sub_C_ne_zero (by norm_num) _
    -- β is integral over G_ab (direct polynomial witness: β² - a = 0 over G_ab)
    have hint_β : IsIntegral (↥G_ab) β :=
      ⟨X ^ 2 - C (⟨a, ha_in_Gab⟩ : ↥G_ab),
       monic_X_pow_sub_C (⟨a, ha_in_Gab⟩ : ↥G_ab) (by norm_num), hβ_root⟩
    -- Establish FiniteDimensional and Module.Free instances explicitly (avoid typeclass timeouts)
    haveI hfin : FiniteDimensional (↥G_ab) ↥((↥G_ab)⟮β⟯) :=
      adjoin.finiteDimensional hint_β
    haveI hfree : Module.Free (↥G_ab) ↥((↥G_ab)⟮β⟯) := inferInstance
    -- minpoly(G_ab, β) ∣ X² - C(a), so natDegree ≤ 2
    have hminpoly_dvd : minpoly (↥G_ab) β ∣ X ^ 2 - C (⟨a, ha_in_Gab⟩ : ↥G_ab) :=
      minpoly.dvd (↥G_ab) β hβ_root
    have hdeg_le : (minpoly (↥G_ab) β).natDegree ≤ 2 :=
      (Polynomial.natDegree_le_of_dvd hminpoly_dvd hXsq_ne).trans
        (natDegree_X_pow_sub_C.le)
    -- Step 3: adjoin β to G_ab at the (↥G_ab)-level
    -- finrank(G_ab, (↥G_ab)⟮β⟯) = natDegree(minpoly) ≤ 2
    have hd_le : Module.finrank (↥G_ab) ↥((↥G_ab)⟮β⟯) ≤ 2 := by
      rw [adjoin.finrank hint_β]; exact hdeg_le
    have hd_pos : 0 < Module.finrank (↥G_ab) ↥((↥G_ab)⟮β⟯) := by
      rw [adjoin.finrank hint_β]; exact minpoly.natDegree_pos hint_β
    -- finrank(G_ab, (↥G_ab)⟮β⟯) ∈ {1, 2}, hence is a power of 2
    set d := Module.finrank (↥G_ab) ↥((↥G_ab)⟮β⟯) with hd_def
    have hd_pow2 : ∃ l : ℕ, d = 2 ^ l := by
      interval_cases d
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    obtain ⟨l, hl⟩ := hd_pow2
    -- Tower law: finrank ℚ (↥G_ab)⟮β⟯ = 2^n_ab * 2^l = 2^(n_ab + l)
    have htower_type : Module.finrank ℚ ↥((↥G_ab)⟮β⟯) = 2 ^ (n_ab + l) := by
      have h := Module.finrank_mul_finrank ℚ (↥G_ab) ↥((↥G_ab)⟮β⟯)
      rw [hn_ab, ← hd_def, hl, ← pow_add] at h
      exact h.symm
    -- Build G_abβ as the ℚ-intermediate field obtained by restricting scalars
    let G_abβ : IntermediateField ℚ ℂ := ((↥G_ab)⟮β⟯).restrictScalars ℚ
    -- finrank ℚ G_abβ = finrank ℚ (↥G_ab)⟮β⟯ (same type, same module structure)
    have htower : Module.finrank ℚ ↥G_abβ = 2 ^ (n_ab + l) := htower_type
    -- G_ab ≤ G_abβ (base field of (↥G_ab)⟮β⟯ is contained in it)
    have hGab_le_Gabβ : G_ab ≤ G_abβ := fun x hx => by
      change x ∈ ((↥G_ab)⟮β⟯).restrictScalars ℚ
      rw [mem_restrictScalars]
      have hcast : (algebraMap (↥G_ab) ℂ) ⟨x, hx⟩ = x := rfl
      rw [← hcast]
      exact ((↥G_ab)⟮β⟯).algebraMap_mem ⟨x, hx⟩
    -- β ∈ G_abβ (β is the generator of the adjunction)
    have hβ_in_Gabβ : β ∈ G_abβ := by
      change β ∈ ((↥G_ab)⟮β⟯).restrictScalars ℚ
      rw [mem_restrictScalars]
      exact mem_adjoin_simple_self (↥G_ab) β
    -- b + β ∈ G_abβ
    have hbβ_in_Gabβ : b + β ∈ G_abβ :=
      G_abβ.add_mem (hGab_le_Gabβ hb_in_Gab) hβ_in_Gabβ
    -- F ≤ G_abβ (via F ≤ G_a ≤ G_ab ≤ G_abβ)
    have hF_le_Gabβ : F ≤ G_abβ := hFGa.trans (hGaGab.trans hGab_le_Gabβ)
    exact ⟨G_abβ, n_ab + l, hF_le_Gabβ, hbβ_in_Gabβ, htower⟩

-- ============================================================
-- PART 2b: Key Structural Lemma (tower degree property)
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
  | sqrt_ext β a b ha hb hβ2 ih_a ih_b =>
    obtain ⟨halg_a, -⟩ := ih_a
    obtain ⟨halg_b, -⟩ := ih_b
    -- β is algebraic: β^2 = a with a algebraic
    have hβ_sq : β ^ 2 = a := by rw [sq]; exact hβ2
    have halg_β : IsAlgebraic ℚ β :=
      IsAlgebraic.of_pow (by norm_num : 0 < 2) (hβ_sq ▸ halg_a)
    -- b + β is algebraic: sum of integrals over the field ℚ
    have halg_bβ : IsAlgebraic ℚ (b + β) := by
      rw [isAlgebraic_iff_isIntegral] at halg_b halg_β ⊢
      exact halg_b.add halg_β
    refine ⟨halg_bβ, ?_⟩
    -- Use pow2_containing_field: find G with b+β ∈ G and finrank ℚ G = 2^n_G
    -- Starting from ⊥ (finrank ℚ ⊥ = 1 = 2^0), then ℚ⟮b+β⟯ ≤ G
    obtain ⟨G, n_G, _, hbβ_in_G, hn_G⟩ :=
      pow2_containing_field (b + β) (IsConstructible.sqrt_ext β a b ha hb hβ2)
        (⊥ : IntermediateField ℚ ℂ) 0
        (by simp [IntermediateField.finrank_bot])
    -- ℚ⟮b+β⟯ ≤ G (since b+β ∈ G)
    have hle : ℚ⟮(b + β)⟯ ≤ G :=
      adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hbβ_in_G)
    -- finrank ℚ ℚ⟮b+β⟯ ∣ finrank ℚ G = 2^n_G
    have hdvd : Module.finrank ℚ ℚ⟮(b + β)⟯ ∣ 2 ^ n_G :=
      hn_G ▸ finrank_dvd_of_le_right hle
    -- Extract the exact 2-power
    obtain ⟨m, _, hm⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp hdvd
    exact ⟨m, hm⟩

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
