/-
  The Golden Ratio is Badly Approximable: Dirichlet's 1/q² Exponent is Sharp
  (research problem: dirichlet-approximation-theorem-oq-05)

  The parent entry `dirichlet-approximation-theorem` and its open-question siblings all
  prove the EXISTENCE of good rational approximations: for every real α there are
  infinitely many p/q with |α − p/q| < 1/q² (Dirichlet's theorem; oq-01 counts them,
  oq-03 re-derives the bound via Minkowski's geometry of numbers).  This file proves the
  dual, sharpness statement, which lives nowhere in the gallery:

  **Main result.** The golden ratio φ = (1+√5)/2 is *badly approximable*: there is a
  constant c > 0 such that for every integer p and every q > 0,

        c / q²  ≤  |φ − p/q|.

  In other words, the exponent 2 in Dirichlet's theorem cannot be improved for φ — no
  rational approximates φ faster than 1/q² up to a constant.  φ (and its `GL₂(ℤ)`-orbit)
  is the *worst*-approximable real number; this is the prototypical lower bound in the
  theory of continued fractions and the Lagrange/Markov spectrum.

  **Proof idea (elementary, no continued fractions).**  φ and its conjugate ψ = (1−√5)/2
  are the two roots of x² − x − 1, so φ + ψ = 1 and φ·ψ = −1.  Hence for any p ∈ ℤ, q > 0,

        q²·(p/q − φ)(p/q − ψ) = p² − pq − q²  ∈  ℤ,

  the norm form of ℤ[φ].  This integer is never 0 (else p/q would equal the irrational φ
  or ψ), so its absolute value is ≥ 1, giving

        |φ − p/q| · |ψ − p/q|  ≥  1/q².

  When |φ − p/q| < 1 the second factor is bounded: |ψ − p/q| ≤ |φ − p/q| + |φ − ψ|
  = |φ − p/q| + √5 < 4, so |φ − p/q| ≥ 1/(4q²).  When |φ − p/q| ≥ 1 the bound is trivial.
  Either way c = 1/4 works.

  What is established here, sorry-free and axiom-free:

  * `norm_form_identity`  — q²·(p/q − φ)(p/q − ψ) = p² − pq − q² as a real identity.
  * `norm_form_ne_zero`   — p² − pq − q² ≠ 0 for q > 0 (irrationality of φ, ψ).
  * `goldenRatio_badly_approximable` — the headline lower bound with explicit c = 1/4.

  Built on Mathlib's `Real.goldenRatio` API
  (`goldenRatio_add_goldenConj`, `goldenRatio_mul_goldenConj`, `goldenRatio_sub_goldenConj`,
  `goldenRatio_irrational`, `goldenConj_irrational`) and `Irrational.ne_rational`.
-/
import Mathlib

open Real

namespace DirichletApproximationOQ05

/-- **Norm-form identity.**  Because φ, ψ are the roots of `x² − x − 1`
(`φ + ψ = 1`, `φ·ψ = −1`), the product `(p/q − φ)(p/q − ψ)` is the integer
`p² − pq − q²` divided by `q²`.  This is the value of the `ℤ[φ]`-norm form at `p − qφ`. -/
theorem norm_form_identity (p : ℤ) (q : ℕ) (hq : 0 < q) :
    ((p : ℝ) / q - goldenRatio) * ((p : ℝ) / q - goldenConj)
      = ((p ^ 2 - p * (q : ℤ) - (q : ℤ) ^ 2 : ℤ) : ℝ) / (q : ℝ) ^ 2 := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have expand : ((p : ℝ) / q - goldenRatio) * ((p : ℝ) / q - goldenConj)
      = ((p : ℝ) / q) ^ 2 - ((p : ℝ) / q) - 1 := by
    have hsum : goldenRatio + goldenConj = 1 := goldenRatio_add_goldenConj
    have hmul : goldenRatio * goldenConj = -1 := goldenRatio_mul_goldenConj
    linear_combination (-(p : ℝ) / (q : ℝ)) * hsum + hmul
  rw [expand]
  push_cast
  field_simp

/-- **Non-vanishing of the norm form.**  For `q > 0` the integer `p² − pq − q²` is never
zero, because otherwise `p/q` would equal one of the irrational roots `φ`, `ψ`. -/
theorem norm_form_ne_zero (p : ℤ) (q : ℕ) (hq : 0 < q) :
    p ^ 2 - p * (q : ℤ) - (q : ℤ) ^ 2 ≠ 0 := by
  intro h
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hid := norm_form_identity p q hq
  rw [h] at hid
  rw [show (((0 : ℤ)) : ℝ) / (q : ℝ) ^ 2 = 0 by simp] at hid
  rcases mul_eq_zero.mp hid with h1 | h1
  · have hval : goldenRatio = (p : ℝ) / ((q : ℤ) : ℝ) := by push_cast; linarith
    exact goldenRatio_irrational.ne_rational p (q : ℤ) hval
  · have hval : goldenConj = (p : ℝ) / ((q : ℤ) : ℝ) := by push_cast; linarith
    exact goldenConj_irrational.ne_rational p (q : ℤ) hval

/-- **The golden ratio is badly approximable.**  There is a constant `c > 0` (here
`c = 1/4`) so that no rational `p/q` approximates `φ` to within `c/q²`: for all `p ∈ ℤ`
and `q > 0`, `c/q² ≤ |φ − p/q|`.  Equivalently, Dirichlet's exponent `2` is sharp for `φ`.

This is the gallery's first Diophantine *lower* bound, dual to the existence statements in
the rest of the family. -/
theorem goldenRatio_badly_approximable :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : ℤ) (q : ℕ), 0 < q →
      c / (q : ℝ) ^ 2 ≤ |goldenRatio - (p : ℝ) / q| := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro p q hq
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
  set A := |(p : ℝ) / q - goldenRatio| with hA
  set B := |(p : ℝ) / q - goldenConj| with hB
  have hid := norm_form_identity p q hq
  -- |p² − pq − q²| ≥ 1
  have hmne : p ^ 2 - p * (q : ℤ) - (q : ℤ) ^ 2 ≠ 0 := norm_form_ne_zero p q hq
  have hpos : (0 : ℤ) < |p ^ 2 - p * (q : ℤ) - (q : ℤ) ^ 2| := abs_pos.mpr hmne
  have hone : (1 : ℤ) ≤ |p ^ 2 - p * (q : ℤ) - (q : ℤ) ^ 2| := by omega
  have hm1 : (1 : ℝ) ≤ |((p ^ 2 - p * (q : ℤ) - (q : ℤ) ^ 2 : ℤ) : ℝ)| := by
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|p ^ 2 - p * (q : ℤ) - (q : ℤ) ^ 2| : ℤ) : ℝ) := by exact_mod_cast hone
      _ = |((p ^ 2 - p * (q : ℤ) - (q : ℤ) ^ 2 : ℤ) : ℝ)| := by rw [Int.cast_abs]
  -- A·B = |m|/q²  and  A·B·q² ≥ 1
  have hAB : A * B = |((p ^ 2 - p * (q : ℤ) - (q : ℤ) ^ 2 : ℤ) : ℝ)| / (q : ℝ) ^ 2 := by
    rw [hA, hB, ← abs_mul, hid, abs_div, abs_of_pos hq2]
  have hq2ne : (q : ℝ) ^ 2 ≠ 0 := ne_of_gt hq2
  have hge1 : (1 : ℝ) ≤ A * B * (q : ℝ) ^ 2 := by
    rw [hAB]
    rw [div_mul_cancel₀ _ hq2ne]
    exact hm1
  -- reduce the goal's absolute value to A
  have hgoalabs : |goldenRatio - (p : ℝ) / q| = A := by rw [hA]; exact abs_sub_comm _ _
  rw [hgoalabs]
  have hAnn : 0 ≤ A := abs_nonneg _
  have hBnn : 0 ≤ B := abs_nonneg _
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  rcases le_or_gt 1 A with hbig | hsmall
  · -- |φ − p/q| ≥ 1: bound is trivial since (1/4)/q² ≤ 1/4 ≤ 1
    have hq1 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith [hq1R]
    have : (1 / 4 : ℝ) / (q : ℝ) ^ 2 ≤ 1 / 4 := div_le_self (by norm_num) hq1
    linarith
  · -- |φ − p/q| < 1: then |ψ − p/q| < 4, and A·B·q² ≥ 1 forces A ≥ 1/(4q²)
    have hsqrt5 : Real.sqrt 5 < 3 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), Real.sqrt_nonneg 5]
    have htri : B ≤ A + Real.sqrt 5 := by
      rw [hA, hB]
      have key2 : |goldenRatio - goldenConj| = Real.sqrt 5 := by
        rw [goldenRatio_sub_goldenConj, abs_of_nonneg (Real.sqrt_nonneg 5)]
      calc |(p : ℝ) / q - goldenConj|
          = |((p : ℝ) / q - goldenRatio) + (goldenRatio - goldenConj)| := by congr 1; ring
        _ ≤ |(p : ℝ) / q - goldenRatio| + |goldenRatio - goldenConj| := abs_add_le _ _
        _ = |(p : ℝ) / q - goldenRatio| + Real.sqrt 5 := by rw [key2]
    have hB4 : B < 4 := by linarith
    rw [div_le_iff₀ hq2]
    nlinarith [hge1, hB4, hAnn, hBnn, hq2,
      mul_nonneg (sub_nonneg.mpr (le_of_lt hB4)) (mul_nonneg hAnn (le_of_lt hq2))]

end DirichletApproximationOQ05
