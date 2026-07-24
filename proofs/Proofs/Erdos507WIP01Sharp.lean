/-
# Heilbronn's Triangle Problem — the sharp bound `heilbronn 3 = 3√3/4`

**Erdős Problem #507 (WIP satellite): sharp maximal-triangle bound.**

This file closes the `n = 3` sandwich of `Proofs/Erdos507WIP01.lean`: it proves
the sharp upper bound

    every triangle with vertices in the closed unit disk has area ≤ 3√3/4,

hence `heilbronn 3 ≤ 3√3/4`, which together with the inscribed-equilateral
lower bound `heilbronn_three_ge` pins the **exact value**

    heilbronn 3 = 3√3/4.

This is the first exact value in the Heilbronn ladder (previously
`heilbronn 3 ∈ [3√3/4, 3/2]`).  As corollaries every upper endpoint in the
ladder improves from `3/2` to `3√3/4 ≈ 1.299`:
`heilbronn 4 ∈ [1, 3√3/4]` and `heilbronn 5 ∈ [81/125, 3√3/4]`.

## Why the classical route was blocked, and the mechanism used instead

The classical proof parametrises the three vertices on the circle by central
angles and maximises `sin α + sin β + sin γ` under `α + β + γ = 2π` by Jensen
(concavity of `sin` on `[0, π]`), after a separate compactness/perturbation
argument moving the vertices to the boundary — several hundred lines of
friction-prone geometry.  A direct `nlinarith` attack on the six-variable
degree-4 optimisation also fails (the maximum sits at an irrational point).

The mechanism here avoids both obstacles by exploiting that the signed shoelace
sum `E = (p×q) + (q×r) + (r×p)` is **affine in each vertex**:

1. `E = p × (q − r) + q × r`, and Cauchy–Schwarz (via Lagrange's identity)
   bounds the `p`-part by `t := ‖q − r‖`, eliminating `p` entirely.
2. With `s := q × r` and `u := ⟨q, r⟩`, Lagrange gives `s² + u² ≤ 1` and the
   norm expansion gives `t² ≤ 2 − 2u`.
3. The square completion `(t − 2s)² ≥ 0` yields `(t+s)² ≤ (3/2)t² + 3s²`, and
   substituting the two bounds gives
   `(t+s)² ≤ 6 − 3u − 3u² = 27/4 − 3(u + 1/2)² ≤ 27/4 = (3√3/2)²`.

Every step is an exact polynomial certificate, so each is a small `nlinarith`
call; the irrational maximiser never has to be located.  Equality holds for the
inscribed equilateral triangle (`u = −1/2`, `t = √3`, `s = √3/2`), which is why
the bound is sharp.

All results are `0`-axiom / `0`-sorry.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Proofs.Erdos507WIP01

namespace Erdos507WIP01

/-! ## Lagrange's identity -/

/-- **Lagrange's identity in the plane.**  For vectors `a = (a₁, a₂)` and
`b = (b₁, b₂)`, the cross product and the inner product satisfy
`(a × b)² + ⟨a, b⟩² = |a|²·|b|²`.  This single algebraic identity powers both
Cauchy–Schwarz steps of the sharp bound below. -/
theorem cross_sq_add_dot_sq (a₁ a₂ b₁ b₂ : ℝ) :
    (a₁ * b₂ - a₂ * b₁) ^ 2 + (a₁ * b₁ + a₂ * b₂) ^ 2
      = (a₁ ^ 2 + a₂ ^ 2) * (b₁ ^ 2 + b₂ ^ 2) := by
  ring

/-! ## The master inequality -/

/-- **Sharp shoelace bound in the unit disk.**  For three points
`p = (p₁,p₂)`, `q = (q₁,q₂)`, `r = (r₁,r₂)` in the closed unit disk, the signed
shoelace sum satisfies `E ≤ 3√3/2` (so the triangle area `|E|/2` is at most
`3√3/4`).

The proof eliminates `p` first: `E = p × (q−r) + q × r ≤ ‖q−r‖ + q × r` by
Cauchy–Schwarz, and then the two-variable bound
`(‖q−r‖ + q×r)² ≤ 27/4` follows from Lagrange's identity plus two completed
squares (`(t−2s)² ≥ 0` and `(u+1/2)² ≥ 0`).  Equality: the inscribed
equilateral triangle. -/
theorem signed_shoelace_le_sharp (p₁ p₂ q₁ q₂ r₁ r₂ : ℝ)
    (hp : p₁ ^ 2 + p₂ ^ 2 ≤ 1) (hq : q₁ ^ 2 + q₂ ^ 2 ≤ 1)
    (hr : r₁ ^ 2 + r₂ ^ 2 ≤ 1) :
    p₁ * (q₂ - r₂) + q₁ * (r₂ - p₂) + r₁ * (p₂ - q₂) ≤ 3 * Real.sqrt 3 / 2 := by
  set t : ℝ := Real.sqrt ((q₁ - r₁) ^ 2 + (q₂ - r₂) ^ 2) with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = (q₁ - r₁) ^ 2 + (q₂ - r₂) ^ 2 := by
    rw [ht]; exact Real.sq_sqrt (by positivity)
  -- Cauchy–Schwarz: the p-part of the shoelace sum is at most t = ‖q − r‖
  have hx2 : (p₁ * (q₂ - r₂) - p₂ * (q₁ - r₁)) ^ 2 ≤ t ^ 2 := by
    rw [ht2]
    have hD : (0 : ℝ) ≤ (q₁ - r₁) ^ 2 + (q₂ - r₂) ^ 2 := by positivity
    have hPD : (p₁ ^ 2 + p₂ ^ 2) * ((q₁ - r₁) ^ 2 + (q₂ - r₂) ^ 2)
        ≤ (q₁ - r₁) ^ 2 + (q₂ - r₂) ^ 2 := by nlinarith [hp, hD]
    nlinarith [sq_nonneg (p₁ * (q₁ - r₁) + p₂ * (q₂ - r₂)), hPD]
  have hx : p₁ * (q₂ - r₂) - p₂ * (q₁ - r₁) ≤ t := by nlinarith [hx2, ht0]
  -- Lagrange data for q, r: with s = q × r and u = ⟨q, r⟩, s² + u² ≤ 1
  have hprodpos : (0 : ℝ) ≤ q₁ ^ 2 + q₂ ^ 2 := by positivity
  have hprod : (q₁ ^ 2 + q₂ ^ 2) * (r₁ ^ 2 + r₂ ^ 2) ≤ 1 := by
    nlinarith [hq, hr, hprodpos]
  have hsu : (q₁ * r₂ - q₂ * r₁) ^ 2 + (q₁ * r₁ + q₂ * r₂) ^ 2 ≤ 1 := by
    nlinarith [hprod]
  -- norm expansion: t² ≤ 2 − 2u
  have ht2u : t ^ 2 ≤ 2 - 2 * (q₁ * r₁ + q₂ * r₂) := by
    rw [ht2]; nlinarith [hq, hr]
  -- completed squares: (t + s)² ≤ 27/4, exact certificate
  --   27/4 − (t+s)² = ½(t−2s)² + 3(u+½)² + (3/2)(2−2u−t²) + 3(1−s²−u²)
  have hts : (t + (q₁ * r₂ - q₂ * r₁)) ^ 2 ≤ 27 / 4 := by
    nlinarith [sq_nonneg (t - 2 * (q₁ * r₂ - q₂ * r₁)),
      sq_nonneg ((q₁ * r₁ + q₂ * r₂) + 1 / 2), ht2u, hsu]
  -- convert the squared bound into t + s ≤ 3√3/2
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hc0 : (0 : ℝ) < 3 * Real.sqrt 3 / 2 := by positivity
  have hc2 : (3 * Real.sqrt 3 / 2) ^ 2 = 27 / 4 := by
    rw [div_pow, mul_pow, h3]; norm_num
  have hkey : t + (q₁ * r₂ - q₂ * r₁) ≤ 3 * Real.sqrt 3 / 2 := by
    nlinarith [hts, hc0, hc2]
  -- assemble: E = (p-part) + s ≤ t + s ≤ 3√3/2
  have hE : p₁ * (q₂ - r₂) + q₁ * (r₂ - p₂) + r₁ * (p₂ - q₂)
      = (p₁ * (q₂ - r₂) - p₂ * (q₁ - r₁)) + (q₁ * r₂ - q₂ * r₁) := by ring
  rw [hE]
  linarith [hx, hkey]

/-! ## The sharp area bound -/

/-- **Sharp uniform area bound `area ≤ 3√3/4`.**  Any triangle with all three
vertices in the closed unit disk has area at most `3√3/4` — the area of the
inscribed equilateral triangle.  Applying `signed_shoelace_le_sharp` to the
vertex orders `(p,q,r)` and `(p,r,q)` bounds the shoelace sum and its negation,
hence its absolute value, by `3√3/2`.  This sharpens
`triangleArea_le_three_halves` to the optimal constant. -/
theorem triangleArea_le_sharp {P : Finset (ℝ × ℝ)} (h : IsInUnitDisk P)
    {p q r : ℝ × ℝ} (hp : p ∈ P) (hq : q ∈ P) (hr : r ∈ P) :
    triangleArea p q r ≤ 3 * Real.sqrt 3 / 4 := by
  have hdp := h p hp
  have hdq := h q hq
  have hdr := h r hr
  have h₁ := signed_shoelace_le_sharp p.1 p.2 q.1 q.2 r.1 r.2 hdp hdq hdr
  have h₂ := signed_shoelace_le_sharp p.1 p.2 r.1 r.2 q.1 q.2 hdp hdr hdq
  have hneg : p.1 * (r.2 - q.2) + r.1 * (q.2 - p.2) + q.1 * (p.2 - r.2)
      = -(p.1 * (q.2 - r.2) + q.1 * (r.2 - p.2) + r.1 * (p.2 - q.2)) := by ring
  rw [hneg] at h₂
  have habs : |p.1 * (q.2 - r.2) + q.1 * (r.2 - p.2) + r.1 * (p.2 - q.2)|
      ≤ 3 * Real.sqrt 3 / 2 := abs_le.mpr ⟨by linarith, h₁⟩
  unfold triangleArea
  linarith [habs]

/-- **`heilbronn n ≤ 3√3/4` for `n ≥ 3` — the sharp uniform upper bound.**
Every admissible bound `α` in the defining `sSup` is `≤` the area of some
distinct triple of the witness configuration, and every unit-disk triangle has
area `≤ 3√3/4` (`triangleArea_le_sharp`).  Improves
`heilbronn_le_three_halves`, and is optimal at `n = 3`. -/
theorem heilbronn_le_sharp (n : ℕ) (hn : 3 ≤ n) :
    heilbronn n ≤ 3 * Real.sqrt 3 / 4 := by
  unfold heilbronn
  apply Real.sSup_le
  · rintro α ⟨P, hcard, hdisk, hbound⟩
    have hcard3 : 2 < P.card := by omega
    obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ := Finset.two_lt_card_iff.mp hcard3
    have h1 : α ≤ triangleArea p q r := hbound p hp q hq r hr hpq hqr hpr
    have h2 : triangleArea p q r ≤ 3 * Real.sqrt 3 / 4 := triangleArea_le_sharp hdisk hp hq hr
    linarith
  · positivity

/-- The sharp constant really improves the Lagrange bound:
`3√3/4 ≈ 1.299 < 3/2`. -/
theorem sharp_lt_three_halves : 3 * Real.sqrt 3 / 4 < 3 / 2 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  nlinarith [h3, Real.sqrt_nonneg 3]

/-! ## The exact value `heilbronn 3 = 3√3/4` -/

/-- **Heilbronn's constant for three points: `heilbronn 3 = 3√3/4`.**  The
first exact value in the ladder.  Lower bound: the inscribed equilateral
triangle (`heilbronn_three_ge`).  Upper bound: the sharp maximal-triangle
bound (`heilbronn_le_sharp`).  The extremal configuration is the equilateral
triangle inscribed in the unit circle, of area `3√3/4 ≈ 1.299`. -/
theorem heilbronn_three_eq : heilbronn 3 = 3 * Real.sqrt 3 / 4 :=
  le_antisymm (heilbronn_le_sharp 3 (by norm_num)) heilbronn_three_ge

/-! ## Improved ladder sandwiches -/

/-- **Improved sandwich for `heilbronn 4`:** `heilbronn 4 ∈ [1, 3√3/4]`.
The upper endpoint improves from `3/2` (`heilbronn_four_mem_Icc`) to
`3√3/4 ≈ 1.299`, shrinking the interval width from `1/2` to `≈ 0.299`. -/
theorem heilbronn_four_mem_Icc_sharp :
    heilbronn 4 ∈ Set.Icc (1 : ℝ) (3 * Real.sqrt 3 / 4) :=
  ⟨heilbronn_four_ge, heilbronn_le_sharp 4 (by norm_num)⟩

/-- **Improved sandwich for `heilbronn 5`:** `heilbronn 5 ∈ [81/125, 3√3/4]`.
The upper endpoint improves from `3/2` (`heilbronn_five_mem_Icc`) to
`3√3/4 ≈ 1.299`. -/
theorem heilbronn_five_mem_Icc_sharp :
    heilbronn 5 ∈ Set.Icc (81 / 125 : ℝ) (3 * Real.sqrt 3 / 4) :=
  ⟨heilbronn_five_ge, heilbronn_le_sharp 5 (by norm_num)⟩

end Erdos507WIP01
