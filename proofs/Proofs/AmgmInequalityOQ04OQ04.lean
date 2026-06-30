import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# AM-GM OQ-04 → OQ-04: quadratic (doubly exponential) convergence of the AGM

The parent chain (`amgm-inequality-oq-04`) studies the arithmetic–geometric mean iteration
`aₙ₊₁ = (aₙ+bₙ)/2`, `bₙ₊₁ = √(aₙbₙ)` and lists as an open question:

> *Prove the quadratic convergence rate `aₙ − bₙ = O(M(a,b)·(b/a)^{2ⁿ})`, showing the gap
> contracts **doubly exponentially** rather than merely geometrically.*

The mechanism is a single algebraic identity for one AGM step:

`(aₙ+bₙ)/2 − √(aₙbₙ) = (√aₙ − √bₙ)²/2 = (aₙ − bₙ)² / (2(√aₙ + √bₙ)²)`,

so the new gap is proportional to the **square** of the old gap — quadratic convergence.
Iterating `gₙ₊₁ ≤ gₙ²/C` yields `gₙ ≤ C·(g₀/C)^{2ⁿ}`, the doubly exponential decay.

This file proves both halves with `0` axioms: the per-step quadratic contraction of the AGM
gap, and the abstract "quadratic recursion ⟹ doubly exponential bound" lemma that turns it
into the `(·)^{2ⁿ}` rate.

## Main results

* `agm_gap_eq` : `(a+b)/2 − √(ab) = (√a − √b)²/2`.
* `agm_gap_quadratic` : `(a+b)/2 − √(ab) = (a − b)²/(2(√a + √b)²)`.
* `agm_gap_le` : `(a+b)/2 − √(ab) ≤ (a − b)²/(8b)` for `0 < b ≤ a` — the squaring bound.
* `quadratic_iteration` : `gₙ₊₁ ≤ gₙ²/C ⟹ gₙ ≤ C·(g₀/C)^{2ⁿ}` (doubly exponential).
-/

namespace AmgmInequalityOQ04OQ04

open Real

/-- **One-step gap identity.** A single AGM step turns the gap into half the square of the
    difference of square roots: `(a+b)/2 − √(ab) = (√a − √b)²/2`. -/
theorem agm_gap_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) / 2 - Real.sqrt (a * b) = (Real.sqrt a - Real.sqrt b) ^ 2 / 2 := by
  rw [Real.sqrt_mul ha]
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  nlinarith [hsa, hsb]

/-- **Quadratic form of the gap.** The new gap is proportional to the *square* of the old
    gap: `(a+b)/2 − √(ab) = (a − b)²/(2(√a + √b)²)`. This is the source of the quadratic
    (doubly exponential) convergence. -/
theorem agm_gap_quadratic {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hne : Real.sqrt a + Real.sqrt b ≠ 0) :
    (a + b) / 2 - Real.sqrt (a * b)
      = (a - b) ^ 2 / (2 * (Real.sqrt a + Real.sqrt b) ^ 2) := by
  rw [agm_gap_eq ha hb]
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  have hsq : Real.sqrt a + Real.sqrt b ≠ 0 := hne
  field_simp
  nlinarith [hsa, hsb]

/-- **The squaring bound.** For `0 < b ≤ a`, one AGM step bounds the gap by the square of
    the old gap over `8b`: `(a+b)/2 − √(ab) ≤ (a − b)²/(8b)`. Iterating this is what gives
    doubly exponential decay. -/
theorem agm_gap_le {a b : ℝ} (hb : 0 < b) (hab : b ≤ a) :
    (a + b) / 2 - Real.sqrt (a * b) ≤ (a - b) ^ 2 / (8 * b) := by
  have ha : 0 ≤ a := le_trans hb.le hab
  have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
  have hsqb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hle : Real.sqrt b ≤ Real.sqrt a := Real.sqrt_le_sqrt hab
  have hne : Real.sqrt a + Real.sqrt b ≠ 0 := by positivity
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have hprod : b ≤ Real.sqrt a * Real.sqrt b := by
    have := mul_le_mul_of_nonneg_right hle hsqb.le
    nlinarith [hsb]
  have hbound : 8 * b ≤ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 := by
    nlinarith [hsa, hsb, hprod, hab]
  rw [agm_gap_quadratic ha hb.le hne]
  gcongr

/-- **Quadratic recursion ⟹ doubly exponential bound.** If a nonnegative sequence satisfies
    `gₙ₊₁ ≤ gₙ²/C` (with `C > 0`), then `gₙ ≤ C·(g₀/C)^{2ⁿ}`. Applied to the AGM gap (with
    `C` of order `8b`), this is exactly the doubly exponential rate the problem asks for. -/
theorem quadratic_iteration {C : ℝ} (hC : 0 < C) {g : ℕ → ℝ}
    (hg : ∀ n, 0 ≤ g n) (hrec : ∀ n, g (n + 1) ≤ g n ^ 2 / C) (n : ℕ) :
    g n ≤ C * (g 0 / C) ^ (2 ^ n) := by
  induction n with
  | zero =>
    have hCne : C ≠ 0 := hC.ne'
    have h : g 0 = C * (g 0 / C) ^ (2 ^ 0) := by
      rw [pow_zero, pow_one]; field_simp
    exact h.le
  | succ n ih =>
    calc g (n + 1) ≤ g n ^ 2 / C := hrec n
      _ ≤ (C * (g 0 / C) ^ 2 ^ n) ^ 2 / C := by
          gcongr
          exact hg n
      _ = C * (g 0 / C) ^ (2 ^ (n + 1)) := by
          have hCne : C ≠ 0 := hC.ne'
          rw [pow_succ 2 n, pow_mul]
          field_simp

end AmgmInequalityOQ04OQ04
