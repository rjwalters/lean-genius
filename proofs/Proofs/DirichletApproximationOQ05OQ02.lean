/-
  Every Quadratic Surd √d is Badly Approximable: the Norm-Form Argument, Uniformly
  (research problem: dirichlet-approximation-theorem-oq-05-oq-02)

  The parent entry `dirichlet-approximation-theorem-oq-05` proves that the golden ratio
  φ = (1+√5)/2 is *badly approximable*: there is a constant c > 0 with c/q² ≤ |φ − p/q|
  for all integers p and q > 0.  Its proof is the elementary norm-form argument: φ and its
  conjugate ψ are the roots of x² − x − 1, so q²(p/q − φ)(p/q − ψ) = p² − pq − q² is a
  nonzero integer, hence ≥ 1 in absolute value, which forces |φ − p/q| ≥ 1/(4q²).

  Its open follow-up asks whether the *same* norm-form argument extends to other quadratic
  irrationals — √2, √3, √5, … — to yield explicit badly-approximable constants.  This entry
  answers YES, and does so at full generality with a single structural theorem:

  **Main result** (`badly_approximable_sqrt`).  Let `d : ℕ` and let `x : ℝ` be any
  *positive irrational* square root of `d` (`x² = d`).  Then `x` is badly approximable with
  the explicit constant `c = 1/(1 + 2x)`: for every integer `p` and every `q > 0`,

        (1 / (1 + 2x)) / q²  ≤  |x − p/q|.

  The conjugate of `x = √d` is simply `−x = −√d` (the two roots of `X² − d`), so the norm
  form is `q²(p/q − x)(p/q + x) = p² − d·q² ∈ ℤ`.  It is nonzero because `x` is irrational,
  hence `|p² − d·q²| ≥ 1`, giving `|x − p/q|·|x + p/q| ≥ 1/q²`.  When `|x − p/q| < 1` the
  second factor is bounded by `|x − p/q| + 2x < 1 + 2x`, and the bound follows; when
  `|x − p/q| ≥ 1` it is trivial.

  Unlike the golden-ratio proof this needs *no* dedicated `Real.goldenRatio` API — only the
  hypothesis `x² = d` and irrationality of `x`.  The irrationality input is completely
  decoupled from the analytic core, so any source of irrational square roots specializes it.

  **Specializations proved here.**

  * `sqrtTwo_badly_approximable`   — √2 is badly approximable (`irrational_sqrt_two`).
  * `sqrtThree_badly_approximable` — √3 (`Nat.Prime.irrational_sqrt` at p = 3).
  * `sqrtFive_badly_approximable`  — √5 (`Nat.Prime.irrational_sqrt` at p = 5).

  More generally the theorem applies to `√n` for *any* non-square `n : ℕ`, since
  `irrational_sqrt_natCast_iff : Irrational (√n) ↔ ¬IsSquare n` supplies the irrationality
  hypothesis (so e.g. the non-prime squarefree √6 is covered too).

  Everything is proved sorry-free and axiom-free (no `native_decide`).
-/
import Mathlib

open Real

namespace DirichletApproximationOQ05OQ02

section General

variable {d : ℕ} {x : ℝ}

/-- **Norm-form identity.**  For a square root `x` of `d` (`x² = d`), the conjugate is
`−x`, and the product `(p/q − x)(p/q + x)` is the integer `p² − d·q²` divided by `q²`.
This is the value of the `ℤ[x]`-norm form `N(p − qx) = p² − d·q²` at `p − qx`. -/
theorem norm_form_identity (hx2 : x ^ 2 = (d : ℝ)) (p : ℤ) (q : ℕ) (hq : 0 < q) :
    ((p : ℝ) / q - x) * ((p : ℝ) / q + x)
      = ((p ^ 2 - (d : ℤ) * (q : ℤ) ^ 2 : ℤ) : ℝ) / (q : ℝ) ^ 2 := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have expand : ((p : ℝ) / q - x) * ((p : ℝ) / q + x) = ((p : ℝ) / q) ^ 2 - x ^ 2 := by
    ring
  rw [expand, hx2]
  push_cast
  field_simp

/-- **Non-vanishing of the norm form.**  For `q > 0` the integer `p² − d·q²` is never zero,
because otherwise `p/q` would equal one of the irrational roots `x`, `−x`. -/
theorem norm_form_ne_zero (hx2 : x ^ 2 = (d : ℝ)) (hirr : Irrational x)
    (p : ℤ) (q : ℕ) (hq : 0 < q) :
    p ^ 2 - (d : ℤ) * (q : ℤ) ^ 2 ≠ 0 := by
  intro h
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hid := norm_form_identity hx2 p q hq
  rw [h] at hid
  rw [show (((0 : ℤ)) : ℝ) / (q : ℝ) ^ 2 = 0 by simp] at hid
  rcases mul_eq_zero.mp hid with h1 | h1
  · -- p/q − x = 0 ⇒ x = p/q, contradicting irrationality
    have hval : x = ((p : ℤ) : ℝ) / ((q : ℤ) : ℝ) := by push_cast; linarith
    exact hirr.ne_rational p (q : ℤ) hval
  · -- p/q + x = 0 ⇒ x = (−p)/q, contradicting irrationality
    have hval : x = ((-p : ℤ) : ℝ) / ((q : ℤ) : ℝ) := by
      have hxeq : x = -((p : ℝ) / (q : ℝ)) := by linarith
      rw [hxeq]; push_cast; ring
    exact hirr.ne_rational (-p) (q : ℤ) hval

/-- **Every quadratic surd is badly approximable.**  If `x > 0` is an irrational square
root of a natural number `d` (`x² = d`), then no rational `p/q` approximates `x` faster
than `1/q²` up to the explicit constant `c = 1/(1 + 2x)`:

    `(1/(1 + 2x)) / q² ≤ |x − p/q|`  for all `p ∈ ℤ`, `q > 0`.

This is the sharpness (Diophantine lower-bound) counterpart to Dirichlet's theorem for the
entire family of real quadratic irrationals `√d`, proved by the same norm-form argument that
handles the golden ratio in the parent entry. -/
theorem badly_approximable_sqrt (hx2 : x ^ 2 = (d : ℝ)) (hxpos : 0 < x)
    (hirr : Irrational x) :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : ℤ) (q : ℕ), 0 < q →
      c / (q : ℝ) ^ 2 ≤ |x - (p : ℝ) / q| := by
  have h1p2x : (0 : ℝ) < 1 + 2 * x := by linarith
  refine ⟨1 / (1 + 2 * x), div_pos one_pos h1p2x, ?_⟩
  intro p q hq
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
  set A := |(p : ℝ) / q - x| with hA
  set B := |(p : ℝ) / q + x| with hB
  have hid := norm_form_identity hx2 p q hq
  have hmne := norm_form_ne_zero hx2 hirr p q hq
  have hpos : (0 : ℤ) < |p ^ 2 - (d : ℤ) * (q : ℤ) ^ 2| := abs_pos.mpr hmne
  have hone : (1 : ℤ) ≤ |p ^ 2 - (d : ℤ) * (q : ℤ) ^ 2| := by omega
  have hm1 : (1 : ℝ) ≤ |((p ^ 2 - (d : ℤ) * (q : ℤ) ^ 2 : ℤ) : ℝ)| := by
    calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
      _ ≤ ((|p ^ 2 - (d : ℤ) * (q : ℤ) ^ 2| : ℤ) : ℝ) := by exact_mod_cast hone
      _ = |((p ^ 2 - (d : ℤ) * (q : ℤ) ^ 2 : ℤ) : ℝ)| := by rw [Int.cast_abs]
  have hq2ne : (q : ℝ) ^ 2 ≠ 0 := ne_of_gt hq2
  have hAB : A * B = |((p ^ 2 - (d : ℤ) * (q : ℤ) ^ 2 : ℤ) : ℝ)| / (q : ℝ) ^ 2 := by
    rw [hA, hB, ← abs_mul, hid, abs_div, abs_of_pos hq2]
  have hge1 : (1 : ℝ) ≤ A * B * (q : ℝ) ^ 2 := by
    rw [hAB, div_mul_cancel₀ _ hq2ne]; exact hm1
  have hgoalabs : |x - (p : ℝ) / q| = A := by rw [hA]; exact abs_sub_comm _ _
  rw [hgoalabs]
  have hAnn : 0 ≤ A := abs_nonneg _
  have hBnn : 0 ≤ B := abs_nonneg _
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  rcases le_or_gt 1 A with hbig | hsmall
  · -- |x − p/q| ≥ 1: the bound c/q² ≤ c ≤ 1 ≤ A is trivial
    have hq1 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith [hq1R]
    have hcle1 : (1 / (1 + 2 * x)) ≤ 1 := by rw [div_le_one h1p2x]; linarith
    have : (1 / (1 + 2 * x)) / (q : ℝ) ^ 2 ≤ 1 / (1 + 2 * x) :=
      div_le_self (by positivity) hq1
    linarith
  · -- |x − p/q| < 1: then |x + p/q| < 1 + 2x, and A·B·q² ≥ 1 forces A ≥ c/q²
    have htri : B ≤ A + 2 * x := by
      rw [hA, hB]
      calc |(p : ℝ) / q + x|
          = |((p : ℝ) / q - x) + 2 * x| := by congr 1; ring
        _ ≤ |(p : ℝ) / q - x| + |2 * x| := abs_add_le _ _
        _ = |(p : ℝ) / q - x| + 2 * x := by
            rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * x)]
    have hBlt : B < 1 + 2 * x := by linarith
    rw [div_le_iff₀ hq2, div_le_iff₀ h1p2x]
    nlinarith [hge1, hBlt, hAnn, hBnn, hq2,
      mul_nonneg (mul_nonneg hAnn (le_of_lt hq2)) (sub_nonneg.mpr (le_of_lt hBlt))]

end General

/-! ### Specializations to concrete quadratic surds

Each just supplies the two hypotheses `x² = d` (via `Real.sq_sqrt`) and `Irrational x`. -/

/-- **√2 is badly approximable.**  `c = 1/(1 + 2√2)` works. -/
theorem sqrtTwo_badly_approximable :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : ℤ) (q : ℕ), 0 < q →
      c / (q : ℝ) ^ 2 ≤ |Real.sqrt 2 - (p : ℝ) / q| := by
  refine badly_approximable_sqrt (d := 2) (x := Real.sqrt 2) ?_ ?_ irrational_sqrt_two
  · rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num
  · exact Real.sqrt_pos.mpr (by norm_num)

/-- **√3 is badly approximable.** -/
theorem sqrtThree_badly_approximable :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : ℤ) (q : ℕ), 0 < q →
      c / (q : ℝ) ^ 2 ≤ |Real.sqrt 3 - (p : ℝ) / q| := by
  have hirr : Irrational (Real.sqrt 3) := by
    simpa using Nat.Prime.irrational_sqrt (show Nat.Prime 3 by norm_num)
  refine badly_approximable_sqrt (d := 3) (x := Real.sqrt 3) ?_ ?_ hirr
  · rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; norm_num
  · exact Real.sqrt_pos.mpr (by norm_num)

/-- **√5 is badly approximable.**  (The golden ratio lives in `ℚ(√5)`; here √5 itself.) -/
theorem sqrtFive_badly_approximable :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : ℤ) (q : ℕ), 0 < q →
      c / (q : ℝ) ^ 2 ≤ |Real.sqrt 5 - (p : ℝ) / q| := by
  have hirr : Irrational (Real.sqrt 5) := by
    simpa using Nat.Prime.irrational_sqrt (show Nat.Prime 5 by norm_num)
  refine badly_approximable_sqrt (d := 5) (x := Real.sqrt 5) ?_ ?_ hirr
  · rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]; norm_num
  · exact Real.sqrt_pos.mpr (by norm_num)

end DirichletApproximationOQ05OQ02
