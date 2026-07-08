import Mathlib

/-
# Brouwer Fixed Point: OQ-02 / OQ-02 / OQ-01
# Explicit Adversary Lower Bound for Fixed-Point Query Complexity

## Open Question (oq-02-oq-02-oq-01)
Can the adversary lower bound for fixed-point query complexity be *fully
formalized* with **explicit function constructions**?

## Context
The parent entry (OQ-02/OQ-02, `BrouwerFixedPointOQ02OQ02.lean`) proves the
information-theoretic *inequality* `2^n < 1/ε → 1/2^n > ε`, but the underlying
adversary argument is only stated in prose:

  "n binary-outcome queries distinguish at most 2^n scenarios. If 2^n < 1/ε,
   some pair of fixed point locations at distance > ε produces identical query
   outcomes."

No witnessing pair of functions is ever constructed. The sibling child
`BrouwerFixedPointOQ02OQ02OQ01.lean` instead develops a priori / a posteriori
error estimates, leaving the *adversary* question untouched. This entry supplies
the missing witness for the base case (one query): two **explicit** affine
contractions of [0,1] that are *indistinguishable* by a value query at the probe
point x = 0, yet whose fixed points are 1/2 apart. This turns the lower bound
from an asserted counting bound into a fully constructive theorem.

A striking consequence: even for *contractions* — the best-behaved class in the
hierarchy — a single value query cannot pin the fixed point down to any accuracy
better than 1/4. The adversary keeps two contractions with very different fixed
points perfectly consistent with the one observation the algorithm must answer.

## Results (0 sorries, 0 axioms)
1. `adversary_error_bound` — abstract adversary principle: for any answer `a`,
   the error against two solutions `p`, `q` is ≥ `|p - q| / 2` on at least one.
2. Explicit witnesses `f x = x/2 + 1/8`, `g x = (5/6)·x + 1/8`.
3. `f_contraction`, `g_contraction` — both are contractions of [0,1].
4. `f_mapsTo`, `g_mapsTo` — both are genuine self-maps of [0,1].
5. `fg_agree` — the two functions return the SAME value at the probe x = 0.
6. `f_unique_fixed`, `g_unique_fixed` — their unique fixed points are 1/4, 3/4.
7. `one_query_lower_bound` — no one-query algorithm resolves the fixed point
   below 1/4 (the main explicit adversary lower bound).
8. `no_one_query_epsilon` — for ε < 1/4 no one-query algorithm is ε-accurate.

Reference: Chen–Deng (2009) query complexity for Brouwer fixed points; the
adversary method of Aaronson / Ambainis; the parent OQ-02-OQ-02.
-/

set_option linter.unusedVariables false

namespace BrouwerOQ02OQ02OQ01Adversary

open Set

-- ============================================================
-- SECTION I: Function-class definitions (matching the parent entry)
-- ============================================================

/-- A function is L-Lipschitz on [0,1]. -/
def IsLipschitzOn01 (f : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, |f x - f y| ≤ L * |x - y|

/-- A function is an L-contraction on [0,1] (L < 1). -/
def IsContractionOn01 (f : ℝ → ℝ) (L : ℝ) : Prop :=
  0 ≤ L ∧ L < 1 ∧ IsLipschitzOn01 f L

/-- **A globally-contractive map has at most one fixed point.**
    (Reproved self-containedly; the argument is
    `|x₁ - x₂| = |f x₁ - f x₂| ≤ L·|x₁ - x₂|` with `L < 1`.) -/
theorem contraction_unique_fixed_point {f : ℝ → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hL1 : L < 1)
    (hlip : ∀ x y : ℝ, |f x - f y| ≤ L * |x - y|)
    {x₁ x₂ : ℝ} (hfx1 : f x₁ = x₁) (hfx2 : f x₂ = x₂) :
    x₁ = x₂ := by
  by_contra h
  have hne : |x₁ - x₂| > 0 := by
    have : x₁ - x₂ ≠ 0 := sub_ne_zero.mpr h
    positivity
  have h1 : |x₁ - x₂| ≤ L * |x₁ - x₂| := by
    calc |x₁ - x₂| = |f x₁ - f x₂| := by rw [hfx1, hfx2]
      _ ≤ L * |x₁ - x₂| := hlip x₁ x₂
  have : 1 ≤ L := by
    rwa [← div_le_iff hne, div_self (ne_of_gt hne)] at h1
  linarith

-- ============================================================
-- SECTION II: The abstract adversary principle
-- ============================================================

/-- **Adversary principle (triangle-inequality form).**
    Suppose two problem instances are *indistinguishable* to an algorithm, so it
    returns the same answer `a`, and their true solutions are `p` and `q`. Then
    the algorithm's error is at least `|p - q| / 2` on at least one of the two
    instances. This is the core of every query lower bound. -/
theorem adversary_error_bound (p q a : ℝ) :
    |p - q| / 2 ≤ max (|a - p|) (|a - q|) := by
  have hp : |a - p| ≤ max (|a - p|) (|a - q|) := le_max_left _ _
  have hq : |a - q| ≤ max (|a - p|) (|a - q|) := le_max_right _ _
  have htri : |p - q| ≤ |a - p| + |a - q| := by
    have h := abs_sub_le p a q
    rwa [abs_sub_comm p a] at h
  linarith

-- ============================================================
-- SECTION III: The explicit witness functions
-- ============================================================

/-- First witness: an affine contraction with slope 1/2 and fixed point 1/4. -/
def f (x : ℝ) : ℝ := x / 2 + 1 / 8

/-- Second witness: an affine contraction with slope 5/6 and fixed point 3/4. -/
def g (x : ℝ) : ℝ := (5 / 6) * x + 1 / 8

/-- Both witnesses return the **same value** `1/8` at the probe point `x = 0`.
    This is exactly what makes them indistinguishable to a one-query algorithm. -/
theorem fg_agree : f 0 = g 0 := by
  unfold f g; norm_num

/-- `f` is a contraction of [0,1] with rate 1/2. -/
theorem f_contraction : IsContractionOn01 f (1 / 2) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro x _ y _
  have e : f x - f y = (1 / 2) * (x - y) := by unfold f; ring
  rw [e, abs_mul, abs_of_nonneg (show (0:ℝ) ≤ 1 / 2 by norm_num)]

/-- `g` is a contraction of [0,1] with rate 5/6. -/
theorem g_contraction : IsContractionOn01 g (5 / 6) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro x _ y _
  have e : g x - g y = (5 / 6) * (x - y) := by unfold g; ring
  rw [e, abs_mul, abs_of_nonneg (show (0:ℝ) ≤ 5 / 6 by norm_num)]

/-- `f` is a genuine self-map of [0,1]: it maps the domain into itself. -/
theorem f_mapsTo : MapsTo f (Icc (0:ℝ) 1) (Icc (0:ℝ) 1) := by
  intro x hx
  obtain ⟨hx0, hx1⟩ := hx
  refine ⟨?_, ?_⟩ <;> · unfold f; constructor <;> nlinarith

/-- `g` is a genuine self-map of [0,1]: it maps the domain into itself. -/
theorem g_mapsTo : MapsTo g (Icc (0:ℝ) 1) (Icc (0:ℝ) 1) := by
  intro x hx
  obtain ⟨hx0, hx1⟩ := hx
  refine ⟨?_, ?_⟩ <;> · unfold g; constructor <;> nlinarith

-- ============================================================
-- SECTION IV: The fixed points are 1/4 and 3/4 — separation 1/2
-- ============================================================

/-- `1/4` is a fixed point of `f`. -/
theorem f_fixed : f (1 / 4) = 1 / 4 := by unfold f; norm_num

/-- `3/4` is a fixed point of `g`. -/
theorem g_fixed : g (3 / 4) = 3 / 4 := by unfold g; norm_num

/-- Global Lipschitz estimate for `f` (needed for uniqueness). -/
theorem f_global_lip : ∀ x y : ℝ, |f x - f y| ≤ (1 / 2) * |x - y| := by
  intro x y
  have e : f x - f y = (1 / 2) * (x - y) := by unfold f; ring
  rw [e, abs_mul, abs_of_nonneg (show (0:ℝ) ≤ 1 / 2 by norm_num)]

/-- Global Lipschitz estimate for `g` (needed for uniqueness). -/
theorem g_global_lip : ∀ x y : ℝ, |g x - g y| ≤ (5 / 6) * |x - y| := by
  intro x y
  have e : g x - g y = (5 / 6) * (x - y) := by unfold g; ring
  rw [e, abs_mul, abs_of_nonneg (show (0:ℝ) ≤ 5 / 6 by norm_num)]

/-- **`1/4` is the *unique* fixed point of `f`.** -/
theorem f_unique_fixed {x : ℝ} (hx : f x = x) : x = 1 / 4 :=
  contraction_unique_fixed_point (by norm_num) (by norm_num) f_global_lip hx f_fixed

/-- **`3/4` is the *unique* fixed point of `g`.** -/
theorem g_unique_fixed {x : ℝ} (hx : g x = x) : x = 3 / 4 :=
  contraction_unique_fixed_point (by norm_num) (by norm_num) g_global_lip hx g_fixed

/-- The two fixed points are exactly `1/2` apart. -/
theorem fixed_points_separated : |(1 / 4 : ℝ) - 3 / 4| = 1 / 2 := by norm_num

-- ============================================================
-- SECTION V: The explicit adversary lower bound
-- ============================================================

/-- **Explicit adversary lower bound (main theorem).**
    Model a *one-query algorithm* as a function `A : ℝ → ℝ` that observes the
    single value the oracle returns at the probe point `x = 0` and outputs an
    estimate of the fixed point. Since `f 0 = g 0`, the algorithm is handed the
    *same* observation for both `f` and `g`, so it must output the *same*
    estimate `A (f 0) = A (g 0)`. But the true fixed points are `1/4` (for `f`)
    and `3/4` (for `g`). Hence the estimate is off by at least `1/4` for at
    least one of the two functions.

    No one-query algorithm resolves the fixed point below accuracy `1/4`. -/
theorem one_query_lower_bound (A : ℝ → ℝ) :
    (1 / 4 : ℝ) ≤ max (|A (f 0) - 1 / 4|) (|A (g 0) - 3 / 4|) := by
  -- The algorithm sees the same value for f and g, so answers identically.
  have hsame : A (g 0) = A (f 0) := by rw [fg_agree]
  rw [hsame]
  -- Apply the adversary principle with p = 1/4, q = 3/4, a = A (f 0).
  have hadv := adversary_error_bound (1 / 4) (3 / 4) (A (f 0))
  have hgap : |(1 / 4 : ℝ) - 3 / 4| / 2 = 1 / 4 := by norm_num
  linarith [hadv, hgap]

/-- **Corollary: one query is not enough for any accuracy `ε < 1/4`.**
    If a one-query algorithm were ε-accurate on *both* witnesses, the two fixed
    points would lie within `2ε < 1/2` of each other — contradicting that they
    are exactly `1/2` apart. -/
theorem no_one_query_epsilon (A : ℝ → ℝ) {ε : ℝ} (hε : ε < 1 / 4) :
    ¬ (|A (f 0) - 1 / 4| ≤ ε ∧ |A (g 0) - 3 / 4| ≤ ε) := by
  rintro ⟨h1, h2⟩
  have hmax := one_query_lower_bound A
  rcases le_max_iff.mp hmax with h | h
  · linarith
  · linarith

end BrouwerOQ02OQ02OQ01Adversary
