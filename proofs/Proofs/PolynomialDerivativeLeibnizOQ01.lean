/-
  The Leibniz Product Rule for Formal Polynomial Derivatives — Finite Products
  Open Question: polynomial-derivative-leibniz-oq-01

  Mathlib's `Polynomial.derivative` is the formal derivative of a polynomial over
  any commutative ring, and it satisfies the two-factor Leibniz rule
  `derivative (p * q) = derivative p * q + p * derivative q`
  (`Polynomial.derivative_mul`) and, for a `Multiset`, `Polynomial.derivative_prod`.
  What is missing from Mathlib is the clean **Finset** form of the product rule and
  its standard consequence for the split polynomial ∏ᵢ (X − rᵢ).

  This file supplies both, axiom-free:

  1. `derivative_finset_prod` — the Leibniz product rule over a `Finset`:
        d/dX ∏_{i∈s} fᵢ  =  ∑_{i∈s} (fᵢ' · ∏_{j∈s\{i}} fⱼ).
     (Proved by `Finset.induction` from the two-factor rule.)

  2. `derivative_prod_X_sub_C` — specializing fᵢ = X − rᵢ (whose derivative is 1):
        d/dX ∏_{i∈s} (X − rᵢ)  =  ∑_{i∈s} ∏_{j∈s\{i}} (X − rⱼ).

  3. `eval_derivative_prod_X_sub_C` — evaluating that derivative at a root rᵢ₀:
        p'(rᵢ₀)  =  ∏_{j∈s\{i₀}} (rᵢ₀ − rⱼ),
     because every other summand carries the factor (rᵢ₀ − rᵢ₀) = 0. This is the
     Lagrange-interpolation denominator and the building block of the discriminant.

  4. `eval_derivative_prod_X_sub_C_ne_zero` — over an integral domain, when the rᵢ are
     distinct on s the value above is a product of nonzero factors, so p'(rᵢ₀) ≠ 0:
     **simple roots of a split polynomial are not roots of its derivative.**

  The higher-order Leibniz rule (nth derivative of a product) is already in Mathlib as
  `Polynomial.iterate_derivative_mul`
    `derivative^[n] (p*q) = ∑ k ∈ range n.succ, n.choose k • (derivative^[n-k] p * derivative^[k] q)`;
  we build the finite-product first-order rule that complements it.

  References:
  - Lang, S., Algebra, 3rd ed., §IV.1 (formal derivative and the product rule).
  - Any account of Lagrange interpolation / the discriminant of ∏(X − rᵢ).
-/

import Mathlib

namespace PolyDerivLeibnizOQ01

open Polynomial Finset

variable {R : Type*} [CommRing R] {ι : Type*} [DecidableEq ι]

/-- **Leibniz product rule over a `Finset`.** The formal derivative of a finite
    product of polynomials is the sum, over each factor, of that factor's derivative
    times the product of the remaining factors:
    `d/dX ∏_{i∈s} fᵢ = ∑_{i∈s} fᵢ' · ∏_{j∈s\{i}} fⱼ`.
    This is the Finset counterpart of Mathlib's `Polynomial.derivative_prod`
    (stated for `Multiset`), proved directly by induction on `s`. -/
theorem derivative_finset_prod (s : Finset ι) (f : ι → R[X]) :
    derivative (∏ i ∈ s, f i) = ∑ i ∈ s, (derivative (f i) * ∏ j ∈ s.erase i, f j) := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, derivative_mul, ih, Finset.sum_insert ha, Finset.mul_sum]
    congr 1
    · rw [Finset.erase_insert ha]
    · apply Finset.sum_congr rfl
      intro i hi
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      rw [Finset.erase_insert_of_ne hia.symm,
          Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
      ring

/-- The two-factor rule `derivative (f * g) = f' * g + f * g'` is the `s = {a, b}`
    case of `derivative_finset_prod`, recovering `Polynomial.derivative_mul`. -/
theorem derivative_prod_pair {a b : ι} (hab : a ≠ b) (f : ι → R[X]) :
    derivative (∏ i ∈ ({a, b} : Finset ι), f i) = derivative (f a) * f b + f a * derivative (f b) := by
  rw [derivative_finset_prod]
  rw [Finset.sum_pair hab]
  rw [Finset.erase_insert (by simp [hab]), Finset.pair_comm,
      Finset.erase_insert (by simp [hab.symm])]
  simp [Finset.prod_singleton, mul_comm]

/-- **Derivative of a split polynomial.** Specializing the Leibniz rule to the linear
    factors `fᵢ = X − C rᵢ` (each with derivative `1`):
    `d/dX ∏_{i∈s} (X − rᵢ) = ∑_{i∈s} ∏_{j∈s\{i}} (X − rⱼ)`. -/
theorem derivative_prod_X_sub_C (s : Finset ι) (r : ι → R) :
    derivative (∏ i ∈ s, (X - C (r i))) = ∑ i ∈ s, ∏ j ∈ s.erase i, (X - C (r j)) := by
  rw [derivative_finset_prod]
  apply Finset.sum_congr rfl
  intro i _
  simp [derivative_sub, derivative_X, derivative_C]

/-- **Value of the derivative of a split polynomial at one of its roots.**
    For `p = ∏_{i∈s} (X − rᵢ)` and `i₀ ∈ s`,
    `p'(rᵢ₀) = ∏_{j∈s\{i₀}} (rᵢ₀ − rⱼ)`.
    Every summand except `i = i₀` contains the factor `(rᵢ₀ − rᵢ₀) = 0` and drops out.
    (No injectivity of `r` is needed for this identity.) This product is exactly the
    Lagrange-interpolation denominator at the node `rᵢ₀`. -/
theorem eval_derivative_prod_X_sub_C (s : Finset ι) (r : ι → R) {i₀ : ι} (hi₀ : i₀ ∈ s) :
    (derivative (∏ i ∈ s, (X - C (r i)))).eval (r i₀)
      = ∏ j ∈ s.erase i₀, (r i₀ - r j) := by
  rw [derivative_prod_X_sub_C, eval_finset_sum, Finset.sum_eq_single i₀]
  · simp [eval_prod, eval_sub, eval_X, eval_C]
  · intro i _ hne
    rw [eval_prod]
    apply Finset.prod_eq_zero (i := i₀)
    · exact Finset.mem_erase.mpr ⟨fun h => hne h.symm, hi₀⟩
    · simp
  · intro h; exact absurd hi₀ h

/-- **Simple roots are not roots of the derivative.** Over an integral domain, if the
    `rᵢ` are pairwise distinct on `s`, then for `p = ∏_{i∈s} (X − rᵢ)` the derivative
    does not vanish at any root: `p'(rᵢ₀) ≠ 0`. Consequently every root of a split
    polynomial with distinct roots is a *simple* root — the derivative test for
    multiplicity. -/
theorem eval_derivative_prod_X_sub_C_ne_zero {R : Type*} [CommRing R] [IsDomain R]
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (r : ι → R)
    (hinj : Set.InjOn r s) {i₀ : ι} (hi₀ : i₀ ∈ s) :
    (derivative (∏ i ∈ s, (X - C (r i)))).eval (r i₀) ≠ 0 := by
  rw [eval_derivative_prod_X_sub_C s r hi₀, Finset.prod_ne_zero_iff]
  intro j hj
  have hjs : j ∈ s := Finset.mem_of_mem_erase hj
  have hji : j ≠ i₀ := (Finset.mem_erase.mp hj).1
  rw [sub_ne_zero]
  intro h
  exact hji (hinj (Finset.mem_coe.mpr hjs) (Finset.mem_coe.mpr hi₀) h.symm)

end PolyDerivLeibnizOQ01
