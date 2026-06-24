import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic

/-
# The General n-Argument Tangent Addition Law

## What This Proves

The parent entry `TangentAdditionFormulaOQ01` establishes the **three-argument**
tangent law `tan (x + y + z) = (e₁ - e₃)/(1 - e₂)` in the elementary symmetric
polynomials `e₁, e₂, e₃` of the three tangents, and lists as its first open
question the genuinely general statement

> `tan (x₁ + … + xₙ) = (e₁ - e₃ + e₅ - …)/(e₀ - e₂ + e₄ - …)`,

with `eₖ` the `k`-th elementary symmetric polynomial of the tangents
`tan x₁, …, tan xₙ`. This follow-up proves exactly that, for an arbitrary finite
family of angles, none of which is a right angle and whose sum is not a right
angle. Neither the statement nor a proof is in Mathlib.

## Method

The cleanest route is via the complex exponential rather than an induction on the
two-argument formula. For each angle,
`cos xⱼ + sin xⱼ · I = exp (xⱼ · I)`, so the product telescopes through
`Complex.exp_sum`:
`∏ⱼ (cos xⱼ + sin xⱼ · I) = exp ((∑ xⱼ) · I) = cos S + sin S · I`,  where `S = ∑ xⱼ`.

Factoring `cos xⱼ` out of each factor (legitimate since `cos xⱼ ≠ 0`) turns the
left side into `(∏ⱼ cos xⱼ) · ∏ⱼ (1 + tan xⱼ · I)`, whence the **tangent product
identity**
`∏ⱼ (1 + tan xⱼ · I) = (cos S + sin S · I) / ∏ⱼ cos xⱼ`.

* Taking real and imaginary parts gives `tan S = Im / Re` of that product — the
  ratio form of the addition law (`tan_sum_eq_im_div_re`).
* Expanding the same product by **Vieta's formulas** (`prod_X_add_C_eq_sum_esymm`
  together with `Multiset.pow_smul_esymm`) gives
  `∏ⱼ (1 + tan xⱼ · I) = ∑ₖ Iᵏ · eₖ`,
  whose real part is `e₀ - e₂ + e₄ - …` and whose imaginary part is
  `e₁ - e₃ + e₅ - …`. This is the elementary-symmetric content of the open
  question (`prod_one_add_tan_mul_I_eq_sum_esymm`).
-/

open scoped BigOperators

namespace TangentNArg

variable {ι : Type*} (s : Finset ι) (x : ι → ℝ)

/-- **Complex exponential identity.** The product of `cos xⱼ + sin xⱼ · I` over a
finite family equals `cos S + sin S · I` where `S = ∑ xⱼ`. This is `exp_sum`
dressed up through `exp (θ · I) = cos θ + sin θ · I`. -/
theorem prod_cos_add_sin_mul_I :
    ∏ i ∈ s, ((Real.cos (x i) : ℂ) + (Real.sin (x i) : ℂ) * Complex.I)
      = (Real.cos (∑ i ∈ s, x i) : ℂ) + (Real.sin (∑ i ∈ s, x i) : ℂ) * Complex.I := by
  have hfac : ∀ i ∈ s, ((Real.cos (x i) : ℂ) + (Real.sin (x i) : ℂ) * Complex.I)
      = Complex.exp ((x i : ℂ) * Complex.I) := by
    intro i _; rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [Finset.prod_congr rfl hfac, ← Complex.exp_sum, ← Finset.sum_mul, ← Complex.ofReal_sum,
    Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]

/-- **Factoring the cosines out.** Each factor `cos xⱼ + sin xⱼ · I` equals
`cos xⱼ · (1 + tan xⱼ · I)` when `cos xⱼ ≠ 0`. -/
theorem prod_eq_prod_cos_mul_prod_one_add_tan (hcos : ∀ i ∈ s, Real.cos (x i) ≠ 0) :
    ∏ i ∈ s, ((Real.cos (x i) : ℂ) + (Real.sin (x i) : ℂ) * Complex.I)
      = (∏ i ∈ s, (Real.cos (x i) : ℂ))
          * ∏ i ∈ s, (1 + (Real.tan (x i) : ℂ) * Complex.I) := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro i hi
  have hc : (Real.cos (x i) : ℂ) ≠ 0 := by exact_mod_cast hcos i hi
  rw [Real.tan_eq_sin_div_cos, Complex.ofReal_div]
  field_simp

/-- **Tangent product identity.** For angles with `cos xⱼ ≠ 0`,
`∏ⱼ (1 + tan xⱼ · I) = (cos S + sin S · I) / ∏ⱼ cos xⱼ`, equivalently
`= cos S / C + (sin S / C) · I` with `C = ∏ⱼ cos xⱼ`. -/
theorem prod_one_add_tan_mul_I (hcos : ∀ i ∈ s, Real.cos (x i) ≠ 0) :
    ∏ i ∈ s, (1 + (Real.tan (x i) : ℂ) * Complex.I)
      = ((Real.cos (∑ i ∈ s, x i) / ∏ i ∈ s, Real.cos (x i) : ℝ) : ℂ)
        + ((Real.sin (∑ i ∈ s, x i) / ∏ i ∈ s, Real.cos (x i) : ℝ) : ℂ) * Complex.I := by
  have hCne : (∏ i ∈ s, Real.cos (x i)) ≠ 0 := Finset.prod_ne_zero_iff.2 hcos
  have hC2 : (↑(∏ i ∈ s, Real.cos (x i)) : ℂ) ≠ 0 := by exact_mod_cast hCne
  have key := (prod_eq_prod_cos_mul_prod_one_add_tan s x hcos).symm.trans
    (prod_cos_add_sin_mul_I s x)
  rw [← Complex.ofReal_prod] at key
  -- key : ↑C * ∏(1 + tan·I) = ↑cosS + ↑sinS·I
  rw [Complex.ofReal_div, Complex.ofReal_div]
  field_simp
  linear_combination key

/-- **The n-argument tangent addition law (ratio form).** For a finite family of
angles, none a right angle and whose sum `S` is not a right angle,
`tan S = Im P / Re P`, where `P = ∏ⱼ (1 + tan xⱼ · I)`. Combined with the
elementary-symmetric expansion below (`Re P = e₀ - e₂ + e₄ - …`,
`Im P = e₁ - e₃ + e₅ - …`) this is the general addition law. Not in Mathlib. -/
theorem tan_sum_eq_im_div_re (hcos : ∀ i ∈ s, Real.cos (x i) ≠ 0)
    (hS : Real.cos (∑ i ∈ s, x i) ≠ 0) :
    Real.tan (∑ i ∈ s, x i)
      = (∏ i ∈ s, (1 + (Real.tan (x i) : ℂ) * Complex.I)).im
        / (∏ i ∈ s, (1 + (Real.tan (x i) : ℂ) * Complex.I)).re := by
  have hCne : (∏ i ∈ s, Real.cos (x i)) ≠ 0 := Finset.prod_ne_zero_iff.2 hcos
  rw [prod_one_add_tan_mul_I s x hcos]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
    sub_zero, add_zero, zero_add]
  rw [Real.tan_eq_sin_div_cos]
  field_simp

/-- **Elementary-symmetric expansion of the tangent product.** By Vieta's
formulas, `∏ⱼ (1 + tan xⱼ · I) = ∑ₖ Iᵏ · eₖ`, where `eₖ` is the `k`-th
elementary symmetric polynomial of the tangents `tan xⱼ`. Since `Iᵏ` cycles
`1, I, -1, -I`, the real part of the right-hand side is `e₀ - e₂ + e₄ - …` and
the imaginary part is `e₁ - e₃ + e₅ - …`: exactly the alternating elementary
symmetric sums of the open question. -/
theorem prod_one_add_tan_mul_I_eq_sum_esymm :
    ∏ i ∈ s, (1 + (Real.tan (x i) : ℂ) * Complex.I)
      = ∑ k ∈ Finset.range (s.card + 1),
          Complex.I ^ k * ((s.val.map (fun i => (Real.tan (x i) : ℂ))).esymm k) := by
  classical
  -- `T` = multiset of complex tangents.  Work with the `I`-scaled multiset `T.map (I·)`.
  have hcardT : Multiset.card (s.val.map (fun i => (Real.tan (x i) : ℂ))) = s.card := by
    rw [Multiset.card_map]; rfl
  -- Step A: rewrite the finite product as `∏_{c} (1 + c)` over the scaled multiset.
  have hA : ∏ i ∈ s, (1 + (Real.tan (x i) : ℂ) * Complex.I)
      = (((s.val.map (fun i => (Real.tan (x i) : ℂ))).map (fun c => Complex.I * c)).map
          (fun r => 1 + r)).prod := by
    rw [Finset.prod, Multiset.map_map, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro i _; simp [mul_comm]
  -- Step B: that product is the evaluation at `1` of `∏ (X + C r)`.
  have hB : (((s.val.map (fun i => (Real.tan (x i) : ℂ))).map (fun c => Complex.I * c)).map
          (fun r => 1 + r)).prod
      = Polynomial.eval 1
          ((((s.val.map (fun i => (Real.tan (x i) : ℂ))).map (fun c => Complex.I * c)).map
            (fun r => Polynomial.X + Polynomial.C r)).prod) := by
    conv_rhs => rw [Polynomial.eval_multiset_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro c _; simp
  rw [hA, hB, Multiset.prod_X_add_C_eq_sum_esymm, Polynomial.eval_finset_sum,
    Multiset.card_map, hcardT]
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    one_pow, mul_one]
  -- Pull `Iʲ` out of the `j`-th elementary symmetric polynomial.
  have h := Multiset.pow_smul_esymm (Complex.I) j (s.val.map (fun i => (Real.tan (x i) : ℂ)))
  simp only [smul_eq_mul] at h
  rw [← h]

/-- **The general n-argument tangent addition law, elementary-symmetric form.**
This is the statement of the parent's first open question: for a finite family of
angles, none a right angle and whose sum `S` is not a right angle,
`tan S` is the ratio of the imaginary and real parts of `∑ₖ Iᵏ eₖ`, where `eₖ` is
the `k`-th elementary symmetric polynomial of the tangents `tan xⱼ`. Because `Iᵏ`
cycles `1, I, -1, -I`, the imaginary part is the alternating odd sum
`e₁ - e₃ + e₅ - …` and the real part is the alternating even sum
`e₀ - e₂ + e₄ - …`. Not in Mathlib. -/
theorem tan_sum_eq_esymm_ratio (hcos : ∀ i ∈ s, Real.cos (x i) ≠ 0)
    (hS : Real.cos (∑ i ∈ s, x i) ≠ 0) :
    Real.tan (∑ i ∈ s, x i)
      = (∑ k ∈ Finset.range (s.card + 1),
            Complex.I ^ k * ((s.val.map (fun i => (Real.tan (x i) : ℂ))).esymm k)).im
        / (∑ k ∈ Finset.range (s.card + 1),
            Complex.I ^ k * ((s.val.map (fun i => (Real.tan (x i) : ℂ))).esymm k)).re := by
  rw [tan_sum_eq_im_div_re s x hcos hS, prod_one_add_tan_mul_I_eq_sum_esymm s x]

end TangentNArg
