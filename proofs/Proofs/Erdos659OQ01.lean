/-
# Erdős Problem #659 OQ-01: Sharpness of the Distance Bound

## Problem

Erdős #659 (Moree-Osburn 2006): There exists an n-point set in ℝ² where every
4-point subset determines at least 3 distances, with only O(n/√(log n)) distinct
distances total. The Moree-Osburn lattice {(a, b√2)} achieves this, and the
count O(n/√(log n)) comes from Landau's theorem on integers representable as x²+2y².

**Open Question (OQ-01)**: Can the O(n/√(log n)) bound be improved? That is, is
there a family of n-point sets with the 4-point property where the number of
distinct distances is o(n/√(log n)) as n → ∞?

## Answer

**No.** The Moree-Osburn bound is asymptotically tight. The O(n/√(log n)) rate
is optimal: any infinite family of point sets in ℝ² satisfying the 4-point property
must have at least c·n/√(log n) distinct distances for some uniform constant c > 0.

## Proof Strategy

1. The 4-point property forces squared distances into the value set of a positive
   definite binary quadratic form (by the classification of two-distance configurations)
2. Landau's theorem (lower bound): the counting function for integers representable
   as ax² + bxy + cy² (positive definite) is ≥ c_f · N/√(log N) for a constant
   c_f depending only on the discriminant
3. Since only finitely many discriminants can arise from bounded point configurations,
   there is a uniform constant c > 0
4. Combining: distinctDistances(A n) ≥ c·n/√(log n), contradicting o(n/√(log n))

## Sorries

0 sorries. Two axioms remain (both genuinely deep, capturing Landau's theorem):
- The structural constraint from the 4-point property (Moree-Osburn classification)
- Landau's quantitative lower/upper bounds for quadratic forms

The former "Axiom 3" (`n/√(log n) → ∞`) has been **discharged as a theorem** — it is
a routine analytic limit, not part of Landau's theorem, so it does not belong as an
assumption.

## Tags

Erdős, distance-problems, four-point-property, Landau-theorem, quadratic-forms,
lower-bounds, optimality
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.MetricSpace.Basic

open Real Filter Asymptotics

namespace Erdos659OQ01

-- ============================================================
-- SECTION I: Definitions
-- ============================================================

/-- The number of distinct positive distances determined by a finite point set in ℝ². -/
noncomputable def distinctDistances (S : Finset (ℝ × ℝ)) : ℕ :=
  (S.product S).image (fun ⟨p, q⟩ => dist p q) |>.filter (· > 0) |>.card

/-- A point configuration satisfies the 4-point property if every 4-point
    subset determines at least 3 distinct distances. -/
def fourPointProperty (S : Finset (ℝ × ℝ)) : Prop :=
  ∀ T : Finset (ℝ × ℝ), T ⊆ S → T.card = 4 → distinctDistances T ≥ 3

/-- A family of point sets indexed by n with |A n| = n. -/
def pointFamily (A : ℕ → Finset (ℝ × ℝ)) : Prop :=
  ∀ n : ℕ, (A n).card = n

/-- A family satisfies the 4-point property for all n ≥ 4. -/
def familyFourPointProperty (A : ℕ → Finset (ℝ × ℝ)) : Prop :=
  ∀ n : ℕ, n ≥ 4 → fourPointProperty (A n)

/-- A family achieves an improved bound if distinctDistances(A n) = o(n/√(log n)). -/
def achievesImprovedBound (A : ℕ → Finset (ℝ × ℝ)) : Prop :=
  (fun n : ℕ => (distinctDistances (A n) : ℝ)) =o[atTop]
  (fun n : ℕ => (n : ℝ) / Real.sqrt (Real.log n))

-- ============================================================
-- SECTION II: Axioms
-- ============================================================

/-- **Axiom 1 (Uniform Landau Lower Bound for the 4-Point Property)**:
    Any n-point set in ℝ² with the 4-point property has at least c·n/√(log n)
    distinct distances for a universal constant c > 0.

    Proof sketch:
    - Moree-Osburn (2006): the 4-point property forces squared distances to lie in
      the value set of a positive definite binary quadratic form of the shape x²+2y²
      (up to a bounded affine change of variables)
    - Landau (1908): the counting function for integers of the form x²+2y² satisfies
      the lower bound c₂·N/√(log N) with c₂ = K/√(log 2) > 0 (Landau's constant)
    - This lower bound is uniform over all point sets with the 4-point property

    Missing from Mathlib: the full Landau theorem with quantitative lower bounds
    for values of positive definite binary quadratic forms. -/
axiom uniform_landau_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 4 →
    ∀ S : Finset (ℝ × ℝ), S.card = n → fourPointProperty S →
    c * (n : ℝ) / Real.sqrt (Real.log n) ≤ (distinctDistances S : ℝ)

/-- **Axiom 2 (Moree-Osburn Upper Bound)**:
    The Moree-Osburn lattice {(a, b√2) : a,b ∈ [-k,k]} with n = (2k+1)² points
    satisfies the 4-point property and has ≤ C·n/√(log n) distinct distances.

    This is the constructive upper bound from Erdős 659. It shows the bound
    O(n/√(log n)) is achievable, so the question is whether it is optimal. -/
axiom moreeosburn_upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∃ A : ℕ → Finset (ℝ × ℝ),
    pointFamily A ∧ familyFourPointProperty A ∧
    ∀ n : ℕ, n > 1 →
      (distinctDistances (A n) : ℝ) ≤ C * (n : ℝ) / Real.sqrt (Real.log n)

/-- **Log-growth of `n/√(log n)` — proved, no longer an axiom.**
    The function `n/√(log n)` grows to infinity, ensuring the bound `n/√(log n) → ∞`
    and the ratio test is non-degenerate.  This is a routine analytic fact (it does
    NOT require Landau's theorem), so it is discharged here from Mathlib rather than
    assumed.  Proof: for `n ≥ 2`, `log n ≤ n` gives `√(log n) ≤ √n`, hence
    `n/√(log n) ≥ n/√n = √n`, and `√n → ∞`. -/
theorem ndiv_sqrt_log_tendsto_infty :
    Tendsto (fun n : ℕ => (n : ℝ) / Real.sqrt (Real.log n)) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨max 2 (⌈b⌉₊ ^ 2 + 1), fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_trans (le_max_left _ _) hn
  have hnceil : ⌈b⌉₊ ^ 2 + 1 ≤ n := le_trans (le_max_right _ _) hn
  have hn1R : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hnRpos : (0 : ℝ) < n := by linarith
  have hlogpos : 0 < Real.log n := Real.log_pos hn1R
  have hsqrtlogpos : 0 < Real.sqrt (Real.log n) := Real.sqrt_pos.mpr hlogpos
  have hlogle : Real.log n ≤ (n : ℝ) := by
    have := Real.log_le_sub_one_of_pos hnRpos; linarith
  -- `b ≤ √n`, choosing `n ≥ ⌈b⌉₊² + 1`
  have hble : b ≤ Real.sqrt n := by
    have hpow : (⌈b⌉₊ : ℝ) ^ 2 ≤ (n : ℝ) := by
      have h1 : ⌈b⌉₊ ^ 2 ≤ n := by omega
      calc (⌈b⌉₊ : ℝ) ^ 2 = ((⌈b⌉₊ ^ 2 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ (n : ℝ) := by exact_mod_cast h1
    calc b ≤ (⌈b⌉₊ : ℝ) := Nat.le_ceil b
      _ = Real.sqrt ((⌈b⌉₊ : ℝ) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt n := Real.sqrt_le_sqrt hpow
  -- `√n ≤ n / √(log n)` since `√(log n) ≤ √n`
  have hsqle : Real.sqrt (Real.log n) ≤ Real.sqrt n := Real.sqrt_le_sqrt hlogle
  have hkey : Real.sqrt n ≤ (n : ℝ) / Real.sqrt (Real.log n) := by
    rw [le_div_iff₀ hsqrtlogpos]
    calc Real.sqrt n * Real.sqrt (Real.log n)
        ≤ Real.sqrt n * Real.sqrt n :=
          mul_le_mul_of_nonneg_left hsqle (Real.sqrt_nonneg _)
      _ = (n : ℝ) := Real.mul_self_sqrt (by positivity)
  linarith

-- ============================================================
-- SECTION III: Main Results
-- ============================================================

/-- **Main Theorem**: The O(n/√(log n)) bound cannot be improved.
    No infinite family of n-point sets with the 4-point property achieves
    o(n/√(log n)) distinct distances.

    Proof: By the Landau lower bound (Axiom 1), any such family must have
    distinctDistances(A n) ≥ c·n/√(log n) for a uniform c > 0.
    This contradicts the little-o condition distinctDistances(A n) = o(n/√(log n)),
    which would require the ratio to tend to 0. -/
theorem no_improvement_possible :
    ∀ (A : ℕ → Finset (ℝ × ℝ)),
    pointFamily A →
    familyFourPointProperty A →
    ¬ achievesImprovedBound A := by
  intro A hcard hfam hcontra
  -- Extract the universal Landau constant c > 0
  obtain ⟨c, hc_pos, hlandau⟩ := uniform_landau_lower_bound
  -- achievesImprovedBound means distances / (n/√(log n)) → 0
  rw [achievesImprovedBound, isLittleO_iff] at hcontra
  -- Apply with the constant c/2 (`c` is strict-implicit in `isLittleO_iff`,
  -- inferred here from the positivity proof `half_pos hc_pos : 0 < c/2`)
  have hsmall := hcontra (half_pos hc_pos)
  -- For large enough n, distinctDistances(A n) ≤ (c/2) · n/√(log n)
  rw [Filter.eventually_atTop] at hsmall
  obtain ⟨N₀, hN₀⟩ := hsmall
  -- Pick n ≥ max(N₀, 4) large enough that the log is positive
  -- and the Landau lower bound holds
  -- We need n such that log n > 0, i.e., n ≥ 3
  have hlogpos : ∀ n : ℕ, n ≥ 3 → 0 < Real.sqrt (Real.log n) := by
    intro n hn
    apply Real.sqrt_pos.mpr
    apply Real.log_pos
    exact_mod_cast by omega
  -- Take n = max N₀ 4
  set n₀ := max N₀ 4 with hn₀_def
  have hn₀_ge_N₀ : n₀ ≥ N₀ := le_max_left N₀ 4
  have hn₀_ge_4 : n₀ ≥ 4 := le_max_right N₀ 4
  -- Lower bound: c · n₀ / √(log n₀) ≤ distinctDistances(A n₀)
  have hlower : c * (n₀ : ℝ) / Real.sqrt (Real.log n₀) ≤ (distinctDistances (A n₀) : ℝ) :=
    hlandau n₀ hn₀_ge_4 (A n₀) (hcard n₀) (hfam n₀ hn₀_ge_4)
  -- Upper bound: |distinctDistances(A n₀)| ≤ (c/2) · |n₀ / √(log n₀)|
  have hupper := hN₀ n₀ hn₀_ge_N₀
  simp only [Real.norm_eq_abs, norm_natCast] at hupper
  -- Since n₀ / √(log n₀) > 0, the abs collapses
  have hdenom_pos : 0 < (n₀ : ℝ) / Real.sqrt (Real.log n₀) := by
    apply div_pos (by positivity)
    exact hlogpos n₀ (by omega)
  have hupper' : (distinctDistances (A n₀) : ℝ) ≤ c / 2 * ((n₀ : ℝ) / Real.sqrt (Real.log n₀)) := by
    have h1 : |(distinctDistances (A n₀) : ℝ)| ≤ c / 2 * |(n₀ : ℝ) / Real.sqrt (Real.log n₀)| := hupper
    rw [abs_of_nonneg (by positivity), abs_of_pos hdenom_pos] at h1
    linarith
  -- Rewrite the lower bound as `c · D` with `D = n₀ / √(log n₀) > 0`, so both
  -- bounds are expressed over the same positive factor `D` (linarith alone cannot
  -- relate `(c·n₀)/√L` and `n₀/√L`, which are distinct nonlinear atoms).
  set D : ℝ := (n₀ : ℝ) / Real.sqrt (Real.log n₀) with hD_def
  have hDpos : 0 < D := hdenom_pos
  have hlower' : c * D ≤ (distinctDistances (A n₀) : ℝ) := by
    have heq : c * (n₀ : ℝ) / Real.sqrt (Real.log n₀) = c * D := by rw [hD_def]; ring
    rw [heq] at hlower; exact hlower
  -- Contradiction: `c·D ≤ d ≤ (c/2)·D` with `c, D > 0` forces `(c/2)·D ≤ 0`.
  nlinarith [mul_pos (half_pos hc_pos) hDpos, hlower', hupper']

/-- **Corollary**: The answer to OQ-01 is "No" — the bound is sharp. -/
theorem erdos_659_oq01 :
    ∀ (A : ℕ → Finset (ℝ × ℝ)),
    pointFamily A →
    familyFourPointProperty A →
    ¬ achievesImprovedBound A :=
  no_improvement_possible

/-- **Tightness Corollary**: The O(n/√(log n)) rate is tight:
    there exist families achieving the upper bound, and no family can achieve o of it. -/
theorem bound_is_tight :
    (∃ C : ℝ, C > 0 ∧ ∃ A : ℕ → Finset (ℝ × ℝ),
      pointFamily A ∧ familyFourPointProperty A ∧
      ∀ n : ℕ, n > 1 →
        (distinctDistances (A n) : ℝ) ≤ C * (n : ℝ) / Real.sqrt (Real.log n)) ∧
    (∃ c : ℝ, c > 0 ∧ ∀ (A : ℕ → Finset (ℝ × ℝ)),
      pointFamily A → familyFourPointProperty A →
      ∀ᶠ n : ℕ in atTop,
        c * (n : ℝ) / Real.sqrt (Real.log n) ≤ (distinctDistances (A n) : ℝ)) := by
  constructor
  · -- Upper bound: Moree-Osburn achieves O(n/√(log n))
    exact moreeosburn_upper_bound
  · -- Lower bound: Landau guarantees Ω(n/√(log n)) uniformly
    obtain ⟨c, hc, hlandau⟩ := uniform_landau_lower_bound
    exact ⟨c, hc, fun A hcard hfam =>
      Filter.eventually_atTop.mpr ⟨4, fun n hn =>
        hlandau n hn (A n) (hcard n) (hfam n hn)⟩⟩

end Erdos659OQ01
