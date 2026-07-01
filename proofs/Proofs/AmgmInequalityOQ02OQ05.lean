/-
  Newton's Inequalities for Four Variables — the n=4 Log-Concavity, Axiom-Free
  Open Question: amgm-inequality-oq-02-oq-05

  Parent: amgm-inequality-oq-02 (Maclaurin's Inequalities via Elementary Symmetric
  Polynomials), which proves the k=1 Newton inequality from scratch but AXIOMATIZES
  the general `newton_log_concavity` (Newton's inequalities pₖ² ≥ pₖ₋₁·pₖ₊₁) and,
  through it, the full Maclaurin chain Mₖ ≥ Mₖ₊₁.

  Sibling: amgm-inequality-oq-02-oq-04 discharges that axiom for n = 3 (both Newton
  inequalities plus the radical Maclaurin chain M₁ ≥ M₂ ≥ M₃).

  This file DISCHARGES the axiom for the next case, n = 4. There the normalized
  sequence has FIVE entries p₀, p₁, p₂, p₃, p₄ and log-concavity is THREE distinct
  inequalities — including a genuine *interior* one (k=2) with no reciprocal symmetry
  to lean on. All three are proved with zero axioms as exact sum-of-squares
  certificates, and each holds for ALL real inputs (the parent axiom only asked for
  non-negative ones — this is strictly stronger). From the endpoints we recover the
  four-variable AM–GM (a+b+c+d)⁴ ≥ 256·abcd.

  Elementary symmetric polynomials of a, b, c, d:
    e₁ = a+b+c+d
    e₂ = ab+ac+ad+bc+bd+cd
    e₃ = abc+abd+acd+bcd
    e₄ = abcd
  Normalized means (pₖ = eₖ / C(4,k),  with C(4,·) = 1,4,6,4,1):
    p₀ = 1,  p₁ = e₁/4,  p₂ = e₂/6,  p₃ = e₃/4,  p₄ = e₄.

  Newton's inequalities (n = 4), each equivalent to a log-concavity step pₖ² ≥ pₖ₋₁pₖ₊₁:
    (N1)  p₁² ≥ p₀·p₂   ⟺   3·e₁² ≥ 8·e₂
    (N2)  p₂² ≥ p₁·p₃   ⟺   4·e₂² ≥ 9·e₁·e₃      (the interior inequality)
    (N3)  p₃² ≥ p₂·p₄   ⟺   3·e₃² ≥ 8·e₂·e₄
  Sum-of-squares certificates (all valid for arbitrary reals):
    3e₁² − 8e₂ = Σ_{i<j}(xᵢ − xⱼ)²
    3e₃² − 8e₂e₄ = Σ_{i<j}(xᵢ' − xⱼ')²   with xᵢ' the four triple products (dual of N1)
    4e₂² − 9e₁e₃ = a Gram/Schur combination of the (products-of-two) differences.

  References:
  - Newton, I. (1707): Arithmetica Universalis.
  - Maclaurin, C. (1729): A Second Letter to Martin Folkes, Esq.
  - Hardy–Littlewood–Pólya, "Inequalities" (1934) §2.22.
  - Brändén–Huh (2020), "Lorentzian polynomials", Ann. of Math. 192 — the modern
    framework in which Newton log-concavity is the n=4 shadow of a Lorentzian form.
-/

import Mathlib

namespace AmgmOQ0205

variable (a b c d : ℝ)

/-- First elementary symmetric polynomial e₁ = a+b+c+d. -/
def e1 : ℝ := a + b + c + d

/-- Second elementary symmetric polynomial e₂ = ab+ac+ad+bc+bd+cd. -/
def e2 : ℝ := a*b + a*c + a*d + b*c + b*d + c*d

/-- Third elementary symmetric polynomial e₃ = abc+abd+acd+bcd. -/
def e3 : ℝ := a*b*c + a*b*d + a*c*d + b*c*d

/-- Fourth elementary symmetric polynomial e₄ = abcd. -/
def e4 : ℝ := a*b*c*d

/-! ### Newton's inequalities as exact sum-of-squares (valid for ALL reals) -/

/-- **Newton N1** (log-concavity at k=1): `3·e₁² ≥ 8·e₂`.
    Certificate: `3e₁² − 8e₂ = Σ_{i<j}(xᵢ−xⱼ)² ≥ 0`. Holds for all reals. -/
theorem newton_N1 : 3 * (e1 a b c d)^2 ≥ 8 * (e2 a b c d) := by
  unfold e1 e2
  nlinarith [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (a-d),
             sq_nonneg (b-c), sq_nonneg (b-d), sq_nonneg (c-d)]

/-- **Newton N2** (log-concavity at k=2, the interior inequality): `4·e₂² ≥ 9·e₁·e₃`.
    No reciprocal symmetry reduces this to N1/N3; it is a genuine degree-4 SOS.
    Holds for all reals. -/
theorem newton_N2 : 4 * (e2 a b c d)^2 ≥ 9 * (e1 a b c d) * (e3 a b c d) := by
  unfold e1 e2 e3
  nlinarith [sq_nonneg (a*b - c*d), sq_nonneg (a*c - b*d), sq_nonneg (a*d - b*c),
             sq_nonneg (a*b + c*d - a*c - b*d), sq_nonneg (a*b + c*d - a*d - b*c),
             sq_nonneg (a*c + b*d - a*d - b*c),
             sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (a-d),
             sq_nonneg (b-c), sq_nonneg (b-d), sq_nonneg (c-d),
             sq_nonneg (a*b - a*c), sq_nonneg (a*b - a*d)]

/-- **Newton N3** (log-concavity at k=3): `3·e₃² ≥ 8·e₂·e₄`.
    Reciprocal dual of N1 under xᵢ ↦ 1/xᵢ (which reverses e₀,…,e₄); certificate is
    the sum of squares of differences of the four triple products. Holds for all reals. -/
theorem newton_N3 : 3 * (e3 a b c d)^2 ≥ 8 * (e2 a b c d) * (e4 a b c d) := by
  unfold e2 e3 e4
  nlinarith [sq_nonneg (a*b*c - a*b*d), sq_nonneg (a*b*c - a*c*d), sq_nonneg (a*b*c - b*c*d),
             sq_nonneg (a*b*d - a*c*d), sq_nonneg (a*b*d - b*c*d), sq_nonneg (a*c*d - b*c*d)]

/-! ### Normalized means and the log-concavity form pₖ² ≥ pₖ₋₁·pₖ₊₁ -/

/-- p₀ = e₀/C(4,0) = 1. -/
def p0 : ℝ := 1
/-- p₁ = e₁/C(4,1) = e₁/4. -/
noncomputable def p1 : ℝ := (e1 a b c d) / 4
/-- p₂ = e₂/C(4,2) = e₂/6. -/
noncomputable def p2 : ℝ := (e2 a b c d) / 6
/-- p₃ = e₃/C(4,3) = e₃/4. -/
noncomputable def p3 : ℝ := (e3 a b c d) / 4
/-- p₄ = e₄/C(4,4) = e₄. -/
def p4 : ℝ := e4 a b c d

/-- **Newton log-concavity, k=1**: `p₁² ≥ p₀·p₂`, the normalized form of N1. -/
theorem logConcave_1 : (p1 a b c d)^2 ≥ p0 * (p2 a b c d) := by
  have h := newton_N1 a b c d
  unfold p0 p1 p2
  nlinarith [h]

/-- **Newton log-concavity, k=2**: `p₂² ≥ p₁·p₃`, the normalized form of N2. -/
theorem logConcave_2 : (p2 a b c d)^2 ≥ (p1 a b c d) * (p3 a b c d) := by
  have h := newton_N2 a b c d
  unfold p1 p2 p3
  nlinarith [h]

/-- **Newton log-concavity, k=3**: `p₃² ≥ p₂·p₄`, the normalized form of N3. -/
theorem logConcave_3 : (p3 a b c d)^2 ≥ (p2 a b c d) * (p4 a b c d) := by
  have h := newton_N3 a b c d
  unfold p2 p3 p4
  nlinarith [h]

/-! ### Equality characterization for the boundary step N1 -/

/-- The N1 defect is the exact sum of the six squared pairwise differences. -/
theorem newton_N1_identity :
    3 * (e1 a b c d)^2 - 8 * (e2 a b c d)
      = (a-b)^2 + (a-c)^2 + (a-d)^2 + (b-c)^2 + (b-d)^2 + (c-d)^2 := by
  unfold e1 e2; ring

/-- Equality in N1 (`3e₁² = 8e₂`, i.e. `p₁² = p₀p₂`) holds **iff** all four inputs
    coincide — the Lorentzian/log-concavity boundary case. -/
theorem newton_N1_eq_iff :
    3 * (e1 a b c d)^2 = 8 * (e2 a b c d) ↔ a = b ∧ a = c ∧ a = d := by
  have hsq : (2 : ℕ) ≠ 0 := by norm_num
  constructor
  · intro h
    have hkey : (a-b)^2 + (a-c)^2 + (a-d)^2 + (b-c)^2 + (b-d)^2 + (c-d)^2 = 0 := by
      have hid := newton_N1_identity a b c d
      linarith
    have hab : a = b := by
      have hz : (a-b)^2 = 0 := le_antisymm (by nlinarith [sq_nonneg (a-c), sq_nonneg (a-d), sq_nonneg (b-c), sq_nonneg (b-d), sq_nonneg (c-d)]) (sq_nonneg _)
      exact sub_eq_zero.mp ((pow_eq_zero_iff hsq).mp hz)
    have hac : a = c := by
      have hz : (a-c)^2 = 0 := le_antisymm (by nlinarith [sq_nonneg (a-b), sq_nonneg (a-d), sq_nonneg (b-c), sq_nonneg (b-d), sq_nonneg (c-d)]) (sq_nonneg _)
      exact sub_eq_zero.mp ((pow_eq_zero_iff hsq).mp hz)
    have had : a = d := by
      have hz : (a-d)^2 = 0 := le_antisymm (by nlinarith [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (b-c), sq_nonneg (b-d), sq_nonneg (c-d)]) (sq_nonneg _)
      exact sub_eq_zero.mp ((pow_eq_zero_iff hsq).mp hz)
    exact ⟨hab, hac, had⟩
  · rintro ⟨hab, hac, had⟩
    subst hab; subst hac; subst had
    unfold e1 e2; ring

/-! ### Endpoint corollary: four-variable AM–GM from the Newton chain -/

/-- **Four-variable AM–GM** (Maclaurin endpoint p₁⁴ ≥ p₄): for non-negative inputs,
    `(a+b+c+d)⁴ ≥ 256·abcd`. This is the concrete payoff of the log-concavity chain:
    Newton's inequalities interpolate between it and the trivial p₁ ≥ p₁. -/
theorem amgm_four (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (e1 a b c d)^4 ≥ 256 * (e4 a b c d) := by
  unfold e1 e4
  nlinarith [sq_nonneg (a-b), sq_nonneg (c-d), sq_nonneg (a+b-c-d),
             mul_nonneg ha hb, mul_nonneg hc hd,
             mul_nonneg (mul_nonneg ha hb) (mul_nonneg hc hd), sq_nonneg (a*b - c*d),
             mul_nonneg (add_nonneg ha hb) (add_nonneg hc hd)]

/-- AM–GM in mean form: the arithmetic mean p₁ = (a+b+c+d)/4 dominates the fourth
    root of the geometric-mean-to-the-fourth p₄ = abcd, without extracting roots. -/
theorem amgm_four_mean (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (p1 a b c d)^4 ≥ p4 a b c d := by
  have h := amgm_four a b c d ha hb hc hd
  unfold p1 p4 e1 e4 at *
  nlinarith [h]

end AmgmOQ0205
