import Mathlib

/-
# Brouwer Fixed Point: OQ-02 / OQ-02 / OQ-01
# Parametrized Adversary Family — Separation Arbitrarily Close to 1

## Open Question (oq-02-oq-02-oq-01), extension
The base entry `BrouwerFixedPointOQ02OQ02OQ01Adversary.lean` answers the open
question affirmatively by exhibiting ONE explicit indistinguishable pair of
contractions (fixed points 1/4, 3/4; separation 1/2) that no one-query algorithm
can resolve below accuracy 1/4. Its `knowledge.md` records — but does not
formalize — a stronger fact:

  "Arbitrary separation is achievable. Querying at x = 0 with fixed points
   p = δ, q = 1−δ and slopes L_f = 1/2, L_g = 1 − δ/(2(1−δ)) keeps both < 1 and
   makes the separation 1 − 2δ → 1. So one query gives essentially NO
   resolution."

This entry supplies that missing formalization: an explicit **one-parameter
family** of indistinguishable contraction pairs, parametrized by δ ∈ (0, 1/2),
and the limiting consequence that the one-query error lower bound has supremum
exactly 1/2 over the class — a single value query provides no worst-case
resolution of the fixed point at all.

The concrete base instance is recovered at δ = 1/4: then L_g = 1 − (1/4)/(2·3/4)
= 5/6 and the fixed points are 1/4, 3/4, matching `f`, `g` in the base file.

## Results (0 sorries, 0 axioms)
1. `adversary_error_bound` — abstract adversary principle (triangle inequality).
2. Explicit family `fδ δ x = x/2 + δ/2`, `gδ δ x = Lg δ · x + δ/2` with
   `Lg δ = 1 − δ/(2(1−δ))`.
3. `fδ_gδ_agree` — the pair agrees at the probe point x = 0.
4. `fδ_contraction`, `gδ_contraction` — both are contractions of [0,1].
5. `fδ_mapsTo`, `gδ_mapsTo` — both are genuine self-maps of [0,1].
6. `fδ_unique_fixed`, `gδ_unique_fixed` — unique fixed points δ and 1−δ.
7. `fixed_points_separation` — the fixed points are `1 − 2δ` apart.
8. `one_query_lower_bound_family` — no one-query algorithm resolves the fixed
   point below accuracy `(1 − 2δ)/2` for the pair at parameter δ.
9. `sup_lower_bound_is_half` — for every target accuracy ε < 1/2 there is a
   parameter δ in the class whose pair forces error strictly greater than ε.
   Hence one query cannot guarantee any accuracy below 1/2.

Reference: Chen–Deng (2009); adversary method (Aaronson / Ambainis); the base
entry `BrouwerFixedPointOQ02OQ02OQ01Adversary.lean`.
-/

set_option linter.unusedVariables false

namespace BrouwerOQ02OQ02OQ01AdversaryFamily

open Set

-- ============================================================
-- SECTION I: Function-class definitions and reusable core lemmas
-- ============================================================

/-- A function is L-Lipschitz on [0,1]. -/
def IsLipschitzOn01 (f : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ x ∈ Icc (0:ℝ) 1, ∀ y ∈ Icc (0:ℝ) 1, |f x - f y| ≤ L * |x - y|

/-- A function is an L-contraction on [0,1] (L < 1). -/
def IsContractionOn01 (f : ℝ → ℝ) (L : ℝ) : Prop :=
  0 ≤ L ∧ L < 1 ∧ IsLipschitzOn01 f L

/-- A globally-contractive map has at most one fixed point. -/
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
    by_contra hc
    push_neg at hc
    have hpos := mul_pos (sub_pos.mpr hc) hne
    nlinarith [h1, hpos]
  linarith

/-- **Adversary principle (triangle-inequality form).**
    For any answer `a`, the error against two solutions `p`, `q` is at least
    `|p - q| / 2` on at least one of them. -/
theorem adversary_error_bound (p q a : ℝ) :
    |p - q| / 2 ≤ max (|a - p|) (|a - q|) := by
  have hp : |a - p| ≤ max (|a - p|) (|a - q|) := le_max_left _ _
  have hq : |a - q| ≤ max (|a - p|) (|a - q|) := le_max_right _ _
  have htri : |p - q| ≤ |a - p| + |a - q| := by
    have h := abs_sub_le p a q
    rwa [abs_sub_comm p a] at h
  linarith

-- ============================================================
-- SECTION II: The explicit parametrized witness family
-- ============================================================

/-- Slope of the second witness at parameter `δ`: `1 − δ/(2(1−δ))`.
    For `δ ∈ (0, 1/2)` this lies strictly between `1/2` and `1`. -/
noncomputable def Lg (δ : ℝ) : ℝ := 1 - δ / (2 * (1 - δ))

/-- First witness: an affine contraction with slope `1/2` and fixed point `δ`. -/
noncomputable def fδ (δ x : ℝ) : ℝ := x / 2 + δ / 2

/-- Second witness: an affine contraction with slope `Lg δ` and fixed point
    `1 − δ`. Its constant term `δ/2 = (1−δ)(1 − Lg δ)` makes it agree with `fδ`
    at the probe point. -/
noncomputable def gδ (δ x : ℝ) : ℝ := Lg δ * x + δ / 2

/-- Both witnesses return the SAME value `δ/2` at the probe point `x = 0`;
    this is what makes them indistinguishable to a one-query algorithm. -/
theorem fδ_gδ_agree (δ : ℝ) : fδ δ 0 = gδ δ 0 := by
  unfold fδ gδ; ring

-- ============================================================
-- SECTION III: Slope bounds, contraction and self-map properties
-- ============================================================

/-- On the parameter range `0 < δ < 1/2`, the second slope is nonnegative. -/
theorem Lg_nonneg {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1 / 2) : 0 ≤ Lg δ := by
  have hd : (0:ℝ) < 2 * (1 - δ) := by linarith
  unfold Lg
  rw [sub_nonneg, div_le_one hd]
  linarith

/-- On the parameter range `0 < δ < 1/2`, the second slope is `< 1`. -/
theorem Lg_lt_one {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1 / 2) : Lg δ < 1 := by
  have hd : (0:ℝ) < 2 * (1 - δ) := by linarith
  unfold Lg
  have : 0 < δ / (2 * (1 - δ)) := div_pos h0 hd
  linarith

/-- `Lg δ ≤ 1 − δ/2` on the parameter range (needed for `gδ`'s self-map bound). -/
theorem Lg_le {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1 / 2) : Lg δ ≤ 1 - δ / 2 := by
  have hd : (0:ℝ) < 2 * (1 - δ) := by linarith
  have hne1 : (1 - δ) ≠ 0 := by intro h; nlinarith
  -- Clear the denominator once: the sign of `δ/(2(1-δ)) − δ/2` equals the sign
  -- of `δ²`, which is nonnegative.
  have key : (δ / (2 * (1 - δ)) - δ / 2) * (2 * (1 - δ)) = δ ^ 2 := by
    field_simp
    ring
  have hpos : 0 ≤ (δ / (2 * (1 - δ)) - δ / 2) * (2 * (1 - δ)) := by
    rw [key]; positivity
  have hstep : δ / 2 ≤ δ / (2 * (1 - δ)) := by nlinarith [hpos, hd]
  unfold Lg
  linarith

/-- `fδ` is a contraction of [0,1] with rate `1/2`. -/
theorem fδ_contraction (δ : ℝ) : IsContractionOn01 (fδ δ) (1 / 2) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro x _ y _
  have e : fδ δ x - fδ δ y = (1 / 2) * (x - y) := by unfold fδ; ring
  rw [e, abs_mul, abs_of_nonneg (show (0:ℝ) ≤ 1 / 2 by norm_num)]

/-- `gδ` is a contraction of [0,1] with rate `Lg δ`. -/
theorem gδ_contraction {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1 / 2) :
    IsContractionOn01 (gδ δ) (Lg δ) := by
  refine ⟨Lg_nonneg h0 h1, Lg_lt_one h0 h1, ?_⟩
  intro x _ y _
  have e : gδ δ x - gδ δ y = Lg δ * (x - y) := by unfold gδ; ring
  rw [e, abs_mul, abs_of_nonneg (Lg_nonneg h0 h1)]

/-- `fδ` is a genuine self-map of [0,1]. -/
theorem fδ_mapsTo {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1 / 2) :
    MapsTo (fδ δ) (Icc (0:ℝ) 1) (Icc (0:ℝ) 1) := by
  intro x hx
  rw [mem_Icc] at hx ⊢
  obtain ⟨hx0, hx1⟩ := hx
  unfold fδ
  constructor <;> linarith

/-- `gδ` is a genuine self-map of [0,1]. -/
theorem gδ_mapsTo {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1 / 2) :
    MapsTo (gδ δ) (Icc (0:ℝ) 1) (Icc (0:ℝ) 1) := by
  intro x hx
  rw [mem_Icc] at hx ⊢
  obtain ⟨hx0, hx1⟩ := hx
  have hLg0 := Lg_nonneg h0 h1
  have hLgle := Lg_le h0 h1
  unfold gδ
  constructor
  · have : 0 ≤ Lg δ * x := mul_nonneg hLg0 hx0
    linarith
  · -- Lg·x + δ/2 ≤ Lg + δ/2 ≤ (1 − δ/2) + δ/2 = 1
    have hmul : Lg δ * x ≤ Lg δ := mul_le_of_le_one_right hLg0 hx1
    linarith

-- ============================================================
-- SECTION IV: Fixed points δ and 1−δ, separation 1−2δ
-- ============================================================

/-- `δ` is a fixed point of `fδ`. -/
theorem fδ_fixed (δ : ℝ) : fδ δ δ = δ := by unfold fδ; ring

/-- `1 − δ` is a fixed point of `gδ`. -/
theorem gδ_fixed {δ : ℝ} (h1 : δ < 1 / 2) : gδ δ (1 - δ) = 1 - δ := by
  have hd : (1 - δ) ≠ 0 := by intro h; nlinarith
  unfold gδ Lg
  field_simp
  ring

/-- Global Lipschitz estimate for `fδ` (needed for uniqueness). -/
theorem fδ_global_lip (δ : ℝ) : ∀ x y : ℝ, |fδ δ x - fδ δ y| ≤ (1 / 2) * |x - y| := by
  intro x y
  have e : fδ δ x - fδ δ y = (1 / 2) * (x - y) := by unfold fδ; ring
  rw [e, abs_mul, abs_of_nonneg (show (0:ℝ) ≤ 1 / 2 by norm_num)]

/-- Global Lipschitz estimate for `gδ` (needed for uniqueness). -/
theorem gδ_global_lip {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1 / 2) :
    ∀ x y : ℝ, |gδ δ x - gδ δ y| ≤ Lg δ * |x - y| := by
  intro x y
  have e : gδ δ x - gδ δ y = Lg δ * (x - y) := by unfold gδ; ring
  rw [e, abs_mul, abs_of_nonneg (Lg_nonneg h0 h1)]

/-- **`δ` is the unique fixed point of `fδ`.** -/
theorem fδ_unique_fixed {δ x : ℝ} (hx : fδ δ x = x) : x = δ :=
  contraction_unique_fixed_point (by norm_num) (by norm_num)
    (fδ_global_lip δ) hx (fδ_fixed δ)

/-- **`1 − δ` is the unique fixed point of `gδ`.** -/
theorem gδ_unique_fixed {δ x : ℝ} (h0 : 0 < δ) (h1 : δ < 1 / 2) (hx : gδ δ x = x) :
    x = 1 - δ :=
  contraction_unique_fixed_point (Lg_nonneg h0 h1) (Lg_lt_one h0 h1)
    (gδ_global_lip h0 h1) hx (gδ_fixed h1)

/-- The two fixed points are exactly `1 − 2δ` apart (for `δ < 1/2`). -/
theorem fixed_points_separation {δ : ℝ} (h1 : δ < 1 / 2) :
    |δ - (1 - δ)| = 1 - 2 * δ := by
  rw [abs_of_nonpos (by linarith)]; ring

-- ============================================================
-- SECTION V: The parametrized adversary lower bound and its supremum
-- ============================================================

/-- **Parametrized adversary lower bound.**
    A one-query algorithm `A : ℝ → ℝ` observes the single oracle value at the
    probe `x = 0`. Since `fδ δ 0 = gδ δ 0`, it is handed the same observation for
    both witnesses and must answer identically, but the true fixed points are `δ`
    and `1 − δ`. Hence its error is at least `(1 − 2δ)/2` on one of the two. -/
theorem one_query_lower_bound_family {δ : ℝ} (h1 : δ < 1 / 2) (A : ℝ → ℝ) :
    (1 - 2 * δ) / 2 ≤ max (|A (fδ δ 0) - δ|) (|A (gδ δ 0) - (1 - δ)|) := by
  have hsame : A (gδ δ 0) = A (fδ δ 0) := by rw [fδ_gδ_agree]
  rw [hsame]
  have hadv := adversary_error_bound δ (1 - δ) (A (fδ δ 0))
  have hgap : |δ - (1 - δ)| = 1 - 2 * δ := fixed_points_separation h1
  rw [hgap] at hadv
  linarith

/-- **The one-query error lower bound has supremum exactly `1/2` over the class.**
    For every target accuracy `ε < 1/2` there is a parameter `δ ∈ (0, 1/2)` whose
    witness pair forces the one-query error to exceed `ε`. Thus no one-query
    algorithm can guarantee accuracy below `1/2`: a single value query provides no
    worst-case resolution of the fixed point. -/
theorem sup_lower_bound_is_half {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ε < (1 - 2 * δ) / 2 := by
  refine ⟨1 / 4 - ε / 2, by linarith, by linarith, ?_⟩
  have : (1 - 2 * (1 / 4 - ε / 2)) / 2 = 1 / 4 + ε / 2 := by ring
  rw [this]; linarith

/-- **Every one-query algorithm fails accuracy `ε` somewhere in the class**
    (contrapositive packaging of `sup_lower_bound_is_half`): for `ε < 1/2` there
    is a parameter `δ` and a witness on which the algorithm's error exceeds `ε`. -/
theorem no_one_query_uniform_accuracy (A : ℝ → ℝ) {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧
      ¬ (|A (fδ δ 0) - δ| ≤ ε ∧ |A (gδ δ 0) - (1 - δ)| ≤ ε) := by
  obtain ⟨δ, hδ0, hδ1, hδε⟩ := sup_lower_bound_is_half hε0 hε1
  refine ⟨δ, hδ0, hδ1, ?_⟩
  rintro ⟨h1, h2⟩
  have hmax := one_query_lower_bound_family hδ1 A
  rcases le_max_iff.mp hmax with h | h
  · linarith
  · linarith

end BrouwerOQ02OQ02OQ01AdversaryFamily
