import Mathlib

/-
# Hurwitz's Theorem (oq-03, WIP-01): The Anticommuting-Determinant Obstruction

The Hurwitz–Radon classification of `n`-square identities (`n ∈ {1,2,4,8}`) hinges,
for the non-admissible dimensions, on the linear algebra of a family of
**anticommuting complex structures** `M₁, …, M_{n-1}` on `ℝⁿ`:

* `Mᵢᵀ = -Mᵢ`            (skew-symmetric)
* `Mᵢᵀ Mᵢ = I`          (orthogonal)
* `Mᵢ² = -I`            (complex structure)
* `Mᵢ Mⱼ + Mⱼ Mᵢ = 0`   (anticommuting, `i ≠ j`)

The `HurwitzTheorem.lean` gallery proof (`hurwitz-theorem-oq-03`) discharges the
**odd** case `n ≥ 3` with an elementary determinant argument (`no_odd_nsquare`:
`M² = -I` gives `det(M)² = (-1)ⁿ = -1`, impossible over `ℝ`), but leaves the even
non-admissible case (`n ≡ 0 mod 4`, `n ∉ {4,8}`) blocked on Clifford-algebra
representation theory (Bott periodicity + Artin–Wedderburn), which is not in Mathlib.

This file isolates and **verifies the reusable algebraic engine** that pushes the
elementary argument one full residue class further, into `n ≡ 2 (mod 4)`.

## The obstruction

Over a field of characteristic `≠ 2`, **two anticommuting invertible matrices force
the dimension to be even**:

  `det(A·B) = det A · det B = det B · det A = det(B·A)`,   but   `A·B = -(B·A)`
  gives `det(A·B) = (-1)^m · det(B·A)`, so `(1 - (-1)^m)·det A·det B = 0`.
  With `det A, det B ≠ 0` and `2 ≠ 0`, this forces `(-1)^m = 1`, i.e. `m` even.

## Why this advances Hurwitz oq-03

For `n ≡ 2 (mod 4)`, the product `P = M₁ ⋯ M_{n-1}` of the (odd number `n-1` of)
anticommuting complex structures is itself a complex structure (`P² = -I`) that
**commutes** with every `Mᵢ`. Regarding `(ℝⁿ, P)` as a complex vector space of
complex dimension `m = n/2` (which is *odd* when `n ≡ 2 mod 4`), the matrices
`M₁, M₂` become `ℂ`-linear, anticommuting and invertible. The theorem below,
applied over `K = ℂ` with `m` odd, yields the contradiction — exactly mirroring the
existing real odd-case argument one level up. Only the residual class `n ≡ 0 (mod 4)`
then remains genuinely blocked on Clifford theory.

The main result is a clean, field-agnostic statement: fully machine-checked,
zero incomplete proofs, zero extra axioms.
-/

namespace HurwitzOQ03WIP01

open Matrix

variable {K : Type*} [Field K] {m : ℕ}

/-- **The anticommuting–determinant obstruction.**
Over a field of characteristic `≠ 2`, two anticommuting invertible `m × m` matrices
force the dimension `m` to be even. This is the field-agnostic engine behind the
elementary Hurwitz argument: over `ℝ` it drives the odd case, and over `ℂ` (through a
commuting complex structure) it drives the `n ≡ 2 (mod 4)` case. -/
theorem anticommuting_invertible_forces_even
    (hchar : (2 : K) ≠ 0)
    (A B : Matrix (Fin m) (Fin m) K)
    (hA : IsUnit A.det) (hB : IsUnit B.det)
    (hanti : A * B = -(B * A)) : Even m := by
  -- Take determinants of both sides of `A*B = -(B*A)`.
  have hdet : A.det * B.det = (-1) ^ m * (B.det * A.det) := by
    have h := congrArg Matrix.det hanti
    rw [Matrix.det_mul] at h
    rw [Matrix.det_neg, Matrix.det_mul, Fintype.card_fin] at h
    exact h
  -- Rearrange to `(1 - (-1)^m) * (det A * det B) = 0`, using commutativity of `K`.
  have hcomm : B.det * A.det = A.det * B.det := mul_comm _ _
  rw [hcomm] at hdet
  -- `det A * det B` is a unit, hence nonzero.
  have hunit : IsUnit (A.det * B.det) := hA.mul hB
  have hne : A.det * B.det ≠ 0 := hunit.ne_zero
  -- From `x = (-1)^m * x` with `x ≠ 0`, deduce `(-1)^m = 1`.
  have hpow : ((-1 : K)) ^ m = 1 := by
    have : ((-1 : K)) ^ m * (A.det * B.det) = 1 * (A.det * B.det) := by
      rw [one_mul]; exact hdet.symm
    exact mul_right_cancel₀ hne this
  -- `(-1)^m = 1` iff `m` even, provided `-1 ≠ 1` (char ≠ 2).
  have hnegone : (-1 : K) ≠ 1 := by
    intro h
    -- `-1 = 1 ⇒ 2 = 0`, contradicting `hchar`.
    exact hchar (by linear_combination -h)
  exact (neg_one_pow_eq_one_iff_even hnegone).mp hpow

/-- Contrapositive form: over a field of characteristic `≠ 2`, in **odd** dimension
there are no two anticommuting invertible matrices. This is the shape used to derive
the Hurwitz contradiction in the odd and `n ≡ 2 (mod 4)` cases. -/
theorem no_anticommuting_invertible_of_odd
    (hchar : (2 : K) ≠ 0) (hodd : Odd m)
    (A B : Matrix (Fin m) (Fin m) K)
    (hA : IsUnit A.det) (hB : IsUnit B.det) : A * B ≠ -(B * A) := by
  intro hanti
  have : Even m := anticommuting_invertible_forces_even hchar A B hA hB hanti
  exact (Nat.not_even_iff_odd.mpr hodd) this

/-- **Complex-structure specialization.** A single complex structure (`M² = -I`,
`M` invertible) is a self-anticommuting-up-to-sign object; combined with a second
anticommuting complex structure it triggers the obstruction. This packages the exact
hypotheses produced by the `crossMat` infrastructure in `HurwitzTheorem.lean`
(`crossMat_sq_neg_one`, `crossMat_anticommute`) as an invertibility + anticommuting
pair, over any field of characteristic `≠ 2`. -/
theorem no_anticommuting_complex_structures_of_odd
    (hchar : (2 : K) ≠ 0) (hodd : Odd m)
    (A B : Matrix (Fin m) (Fin m) K)
    (hAsq : A * A = -1) (hBsq : B * B = -1)
    (hanti : A * B = -(B * A)) : False := by
  -- `A² = -1` makes `A` a unit: `A * (-A) = 1`.
  have hAunit : IsUnit A.det := by
    have hAinv : A * (-A) = 1 := by rw [mul_neg, hAsq, neg_neg]
    have hdet1 : A.det * (-A).det = 1 := by
      rw [← Matrix.det_mul, hAinv, Matrix.det_one]
    exact (left_ne_zero_of_mul_eq_one hdet1).isUnit
  have hBunit : IsUnit B.det := by
    have hBinv : B * (-B) = 1 := by rw [mul_neg, hBsq, neg_neg]
    have hdet1 : B.det * (-B).det = 1 := by
      rw [← Matrix.det_mul, hBinv, Matrix.det_one]
    exact (left_ne_zero_of_mul_eq_one hdet1).isUnit
  exact no_anticommuting_invertible_of_odd hchar hodd A B hAunit hBunit hanti

/-- Sanity check: the engine specialized to `ℝ`. In odd dimension, no pair of
anticommuting real complex structures exists. -/
example (hodd : Odd m)
    (A B : Matrix (Fin m) (Fin m) ℝ)
    (hAsq : A * A = -1) (hBsq : B * B = -1)
    (hanti : A * B = -(B * A)) : False :=
  no_anticommuting_complex_structures_of_odd (by norm_num) hodd A B hAsq hBsq hanti

/-- Specialization to `ℂ`, the field used for the `n ≡ 2 (mod 4)` reduction. -/
example (hodd : Odd m)
    (A B : Matrix (Fin m) (Fin m) ℂ)
    (hAsq : A * A = -1) (hBsq : B * B = -1)
    (hanti : A * B = -(B * A)) : False :=
  no_anticommuting_complex_structures_of_odd (by norm_num) hodd A B hAsq hBsq hanti

-- ═══════════════════════════════════════════════════════════════════
-- THE PRODUCT ENGINE: moving an anticommuting element through `P = M₁⋯M_k`
-- ═══════════════════════════════════════════════════════════════════
--
-- The `n ≡ 2 (mod 4)` reduction (see `HurwitzTheorem.lean`) forms the product
-- `P = M₁ ⋯ M_{n-1}` of the anticommuting complex structures and studies how a
-- fresh structure `a` (one of the `Mᵢ`, or a probe) moves through it. The single
-- algebraic fact behind that whole step is: **an element that anticommutes with
-- every factor of a product acquires the sign `(-1)^(length)` when moved across
-- the entire product.** These lemmas are stated over an arbitrary ring, so they
-- apply verbatim to the real `crossMat` family and to its complexification.

section ProductEngine

variable {R : Type*} [Ring R]

/-- **Move-through sign.** If `a` anticommutes with every entry of the list `t`,
    then moving `a` across the whole product `t.prod` picks up the sign
    `(-1)^(t.length)`:

      `a * t.prod = (-1)^(t.length) * (t.prod * a)`.

    This is the reusable engine behind the `P = M₁⋯M_{n-1}` construction in the
    `n ≡ 2 (mod 4)` Hurwitz reduction: with all factors pairwise anticommuting,
    parity of the length controls whether `a` commutes or anticommutes with `P`. -/
theorem mul_prod_anticomm {a : R} :
    ∀ {t : List R}, (∀ x ∈ t, a * x = -(x * a)) →
      a * t.prod = (-1 : R) ^ t.length * (t.prod * a) := by
  intro t
  induction t with
  | nil => intro _; simp
  | cons b s ih =>
    intro h
    have hb : a * b = -(b * a) := h b (by simp)
    have hs : ∀ x ∈ s, a * x = -(x * a) := fun x hx => h x (by simp [hx])
    have hcb : b * (-1 : R) ^ s.length = (-1 : R) ^ s.length * b :=
      ((Commute.neg_one_left b).pow_left s.length).eq.symm
    calc a * (b :: s).prod
        = -(b * (a * s.prod)) := by
          rw [List.prod_cons, ← mul_assoc, hb, neg_mul, mul_assoc]
      _ = -(b * ((-1 : R) ^ s.length * (s.prod * a))) := by rw [ih hs]
      _ = -((-1 : R) ^ s.length * (b * (s.prod * a))) := by
          rw [← mul_assoc, hcb, mul_assoc]
      _ = (-1 : R) ^ (b :: s).length * ((b :: s).prod * a) := by
          rw [List.length_cons, List.prod_cons, pow_succ]
          noncomm_ring

/-- **Even length ⇒ commutes.** If `a` anticommutes with every factor of `L` and
    `L` has even length, then `a` commutes with the whole product `L.prod`. -/
theorem commute_prod_of_anticomm_of_even {a : R} {L : List R}
    (h : ∀ x ∈ L, a * x = -(x * a)) (hlen : Even L.length) :
    a * L.prod = L.prod * a := by
  rw [mul_prod_anticomm h, hlen.neg_one_pow, one_mul]

/-- **Odd length ⇒ anticommutes.** If `a` anticommutes with every factor of `L`
    and `L` has odd length, then `a` anticommutes with the product `L.prod`. This
    is the shape used on the `M₁⋯M_{n-1}` product (odd for even `n`): a fresh
    complex structure anticommuting with each factor also anticommutes with `P`. -/
theorem anticommute_prod_of_anticomm_of_odd {a : R} {L : List R}
    (h : ∀ x ∈ L, a * x = -(x * a)) (hlen : Odd L.length) :
    a * L.prod = -(L.prod * a) := by
  rw [mul_prod_anticomm h, hlen.neg_one_pow, neg_one_mul]

end ProductEngine

end HurwitzOQ03WIP01
