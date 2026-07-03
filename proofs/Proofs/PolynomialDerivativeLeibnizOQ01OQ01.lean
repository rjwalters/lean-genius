/-
  The Discriminant Identity for a Split Polynomial
  Open Question: polynomial-derivative-leibniz-oq-01-oq-01

  The parent entry `polynomial-derivative-leibniz-oq-01` established, axiom-free over
  any commutative ring, the value of the derivative of a split polynomial at one of its
  roots:

    `eval_derivative_prod_X_sub_C` :
        p'(rᵢ₀) = ∏_{j ∈ s.erase i₀} (rᵢ₀ − rⱼ),   where p = ∏_{i∈s} (X − rᵢ),

  the leave-one-out product of node differences (the Lagrange-interpolation denominator).

  This entry answers the first open question left there: relate the **product of the
  derivative values over all roots** to the **discriminant** ∏_{i<j}(rᵢ − rⱼ)². Working
  over a linearly ordered index type we prove, over any commutative ring:

    `prod_eval_derivative_eq` :
        ∏_{i∈s} p'(rᵢ) = ∏_{i∈s} ∏_{j∈s.erase i} (rᵢ − rⱼ)                 (full off-diagonal product)

    `prod_eval_derivative_eq_sign_mul_sq` :
        ∏_{i∈s} p'(rᵢ) = (−1)^N · ( ∏_{i∈s} ∏_{j∈s, i<j} (rᵢ − rⱼ) )²
      where N = ∑_{i∈s} #{ j ∈ s : i < j } is the number of unordered pairs of s
      (equivalently N = C(#s, 2)).

  The square being multiplied is exactly the Vandermonde product of node differences,
  so the right-hand side is the discriminant of the split polynomial up to the sign
  (−1)^N.  The proof is elementary: split the erased index set `s.erase i` into the
  elements below and above `i`; the "below" half, after swapping the two summation
  indices (`Finset.prod_comm'`), pairs term-by-term with the "above" half, and each
  pair `(rᵢ − rⱼ)(rⱼ − rᵢ) = −(rᵢ − rⱼ)²` contributes a square and a factor of −1.

  Zero axioms, zero sorries; only `[CommRing R]` and `[LinearOrder ι]` are used.

  References:
  - Lang, S., Algebra, 3rd ed., §IV.1 (formal derivative and the discriminant).
  - The discriminant of a monic split polynomial ∏(X − rᵢ) is ∏_{i<j}(rᵢ − rⱼ)²; the
    derivative-at-a-root value p'(rᵢ) = ∏_{j≠i}(rᵢ − rⱼ) is the standard route to it.
-/

import Mathlib
import Proofs.PolynomialDerivativeLeibnizOQ01

namespace PolyDerivLeibnizOQ01OQ01

open Polynomial Finset

variable {R : Type*} [CommRing R] {ι : Type*} [LinearOrder ι]

/-- **Splitting an erased index set by order.** For a linear order, the product over
    `s.erase i` factors as the product over the elements strictly below `i` times the
    product over the elements strictly above `i`, since `j ≠ i ↔ j < i ∨ i < j`. -/
theorem prod_erase_eq_prod_lt_mul_prod_gt (s : Finset ι) (i : ι) (g : ι → R) :
    ∏ j ∈ s.erase i, g j
      = (∏ j ∈ s.filter (fun j => j < i), g j) * ∏ j ∈ s.filter (fun j => i < j), g j := by
  have hdisj : Disjoint (s.filter (fun j => j < i)) (s.filter (fun j => i < j)) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    simp only [Finset.mem_filter] at ha hb
    exact absurd hb.2 (lt_asymm ha.2)
  have hunion : s.erase i = s.filter (fun j => j < i) ∪ s.filter (fun j => i < j) := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hji, hjs⟩
      rcases lt_or_gt_of_ne hji with h | h
      · exact Or.inl ⟨hjs, h⟩
      · exact Or.inr ⟨hjs, h⟩
    · rintro (⟨hjs, h⟩ | ⟨hjs, h⟩)
      · exact ⟨ne_of_lt h, hjs⟩
      · exact ⟨(ne_of_lt h).symm, hjs⟩
  rw [hunion, Finset.prod_union hdisj]

/-- **Product of the derivative values over all roots = full off-diagonal product.**
    For `p = ∏_{i∈s}(X − rᵢ)`, by the parent entry's `eval_derivative_prod_X_sub_C`
    each factor is a leave-one-out product, so
    `∏_{i∈s} p'(rᵢ) = ∏_{i∈s} ∏_{j∈s.erase i} (rᵢ − rⱼ)`. -/
theorem prod_eval_derivative_eq (s : Finset ι) (r : ι → R) :
    ∏ i ∈ s, (derivative (∏ x ∈ s, (X - C (r x)))).eval (r i)
      = ∏ i ∈ s, ∏ j ∈ s.erase i, (r i - r j) := by
  apply Finset.prod_congr rfl
  intro i hi
  exact PolyDerivLeibnizOQ01.eval_derivative_prod_X_sub_C s r hi

/-- **The discriminant identity.** Over any commutative ring with a linearly ordered
    index type, the product of the derivative values of the split polynomial
    `p = ∏_{i∈s}(X − rᵢ)` over all its roots equals, up to the sign `(−1)^N`, the square
    of the Vandermonde product of node differences:
      `∏_{i∈s} p'(rᵢ) = (−1)^N · (∏_{i∈s} ∏_{j∈s, i<j} (rᵢ − rⱼ))²`,
    where `N = ∑_{i∈s} #{j ∈ s : i < j}` is the number of unordered pairs of `s`. -/
theorem prod_eval_derivative_eq_sign_mul_sq (s : Finset ι) (r : ι → R) :
    ∏ i ∈ s, (derivative (∏ x ∈ s, (X - C (r x)))).eval (r i)
      = (-1) ^ (∑ i ∈ s, (s.filter (fun j => i < j)).card)
        * (∏ i ∈ s, ∏ j ∈ s.filter (fun j => i < j), (r i - r j)) ^ 2 := by
  rw [prod_eval_derivative_eq]
  -- Split each `erase i` into the below-`i` and above-`i` halves.
  have hsplit : ∏ i ∈ s, ∏ j ∈ s.erase i, (r i - r j)
      = (∏ i ∈ s, ∏ j ∈ s.filter (fun j => j < i), (r i - r j))
        * (∏ i ∈ s, ∏ j ∈ s.filter (fun j => i < j), (r i - r j)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    exact prod_erase_eq_prod_lt_mul_prod_gt s i (fun j => r i - r j)
  rw [hsplit]
  -- Swap the summation indices in the below-`i` (lower-triangular) product.
  have hlower : (∏ i ∈ s, ∏ j ∈ s.filter (fun j => j < i), (r i - r j))
      = ∏ j ∈ s, ∏ i ∈ s.filter (fun i => j < i), (r i - r j) := by
    apply Finset.prod_comm'
    intro i j
    simp only [Finset.mem_filter]
    tauto
  rw [hlower]
  -- Pair the two triangular products term by term.
  have key : (∏ j ∈ s, ∏ i ∈ s.filter (fun i => j < i), (r i - r j))
           * (∏ i ∈ s, ∏ j ∈ s.filter (fun j => i < j), (r i - r j))
      = ∏ i ∈ s, ∏ j ∈ s.filter (fun j => i < j), ((r j - r i) * (r i - r j)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Finset.prod_mul_distrib]
  rw [key]
  -- Each paired factor is `−(rᵢ − rⱼ)²`; collect the signs and the square.
  have hpt : ∀ i j : ι, (r j - r i) * (r i - r j) = (-1) * (r i - r j) ^ 2 := by
    intro i j; ring
  simp_rw [hpt, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_pow]
  rw [Finset.prod_pow_eq_pow_sum]

end PolyDerivLeibnizOQ01OQ01
