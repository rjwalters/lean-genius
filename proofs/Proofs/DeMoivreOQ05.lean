/-
Sum of the n-th roots of unity is zero (n > 1)

Source: Open question from the de-moivre gallery family (de-moivre-oq-05)
Status: VERIFIED (0 axioms, 0 sorries)

Classical fact: for `n > 1` the `n` complex `n`-th roots of unity sum to zero.
The standard one-line argument is a geometric series with ratio a primitive
root `ζ`:

      ∑_{i=0}^{n-1} ζ^i = (ζ^n − 1)/(ζ − 1) = 0      (ζ^n = 1, ζ ≠ 1).

Mathlib records exactly this single-primitive-root *geometric-series* statement,
`IsPrimitiveRoot.geom_sum_eq_zero`:

      1 < k  →  ∑ i ∈ range k, ζ^i = 0.

What Mathlib does **not** record is the statement about the *set of all roots*:
that the sum over the finite set `nthRootsFinset n` of every `n`-th root of unity
(without privileging a generator) vanishes. The geometric form sums the powers
`ζ^0, …, ζ^{n-1}` *as an indexed list*; the set form sums the underlying roots
themselves. The two are connected by the (also absent) structural identity

      nthRootsFinset n  =  (range n).image (ζ ^ ·),

i.e. the `n`-th roots of unity are exactly the `n` distinct powers of a single
primitive root. We supply that bridge and deduce the vanishing-sum identity in
the coordinate-free `nthRootsFinset` form, over any integral domain possessing a
primitive root, then specialise to `ℂ`.

Finally we give the explicit de Moivre form

      ∑_{k=0}^{n-1} exp(2πik/n) = 0,

the version that appears in discrete Fourier analysis (the `n` sampling phases
sum to zero), obtained by recognising `exp(2πik/n) = (exp(2πi/n))^k`.

We prove:
1. `nthRootsFinset_eq_image`        — the n-th roots are exactly the powers of a primitive root
2. `sum_nthRootsFinset_eq_zero`     — coordinate-free vanishing sum over a domain
3. `sum_complex_nthRootsFinset_eq_zero` — the ℂ specialisation
4. `sum_exp_eq_zero`                — explicit de Moivre / DFT form  ∑ exp(2πik/n) = 0
-/

import Mathlib

open Finset Polynomial

namespace DeMoivreOQ05

variable {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]

/-- **The n-th roots of unity are exactly the powers of a primitive root.**
If `ζ` is a primitive `n`-th root of unity in an integral domain, then the finite
set of all `n`-th roots of unity is the image of `{0, …, n-1}` under `i ↦ ζ^i`.
Both sides have cardinality `n` (the powers are distinct by primitivity, and a
degree-`n` polynomial `Xⁿ - 1` has at most `n` roots), and the image is contained
in the root set, so they coincide. This structural identity is what lets us pass
between the geometric-series form and the coordinate-free set form of the
vanishing-sum identity; Mathlib does not record it. -/
theorem nthRootsFinset_eq_image {ζ : R} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) :
    nthRootsFinset n (1 : R) = (range n).image (fun i => ζ ^ i) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  -- The image is contained in the root set: each `ζ^i` satisfies `xⁿ = 1`.
  have hsub : (range n).image (fun i => ζ ^ i) ⊆ nthRootsFinset n (1 : R) := by
    intro x hx
    simp only [mem_image, mem_range] at hx
    obtain ⟨i, _, rfl⟩ := hx
    rw [mem_nthRootsFinset hn]
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  -- Both sides have cardinality `n`, so the containment is an equality.
  refine (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [hζ.card_nthRootsFinset, Finset.card_image_of_injOn hζ.injOn_pow, card_range]

/-- **Coordinate-free vanishing sum of the n-th roots of unity.**
For `n > 1`, the sum over the set of all `n`-th roots of unity in an integral
domain (possessing a primitive root) is zero. Reindexing the set as the powers
of a primitive root turns the sum into the geometric series `∑ i ∈ range n, ζ^i`,
which vanishes. -/
theorem sum_nthRootsFinset_eq_zero {ζ : R} {n : ℕ} (hζ : IsPrimitiveRoot ζ n)
    (hn : 1 < n) : ∑ x ∈ nthRootsFinset n (1 : R), x = 0 := by
  rw [nthRootsFinset_eq_image hζ, Finset.sum_image hζ.injOn_pow]
  exact hζ.geom_sum_eq_zero hn

/-- **The complex n-th roots of unity sum to zero** (`n > 1`).
Specialisation of `sum_nthRootsFinset_eq_zero` to `ℂ`, which has the primitive
root `exp(2πi/n)`. -/
theorem sum_complex_nthRootsFinset_eq_zero {n : ℕ} (hn : 1 < n) :
    ∑ x ∈ nthRootsFinset n (1 : ℂ), x = 0 :=
  sum_nthRootsFinset_eq_zero (Complex.isPrimitiveRoot_exp n (by omega)) hn

/-- **Explicit de Moivre / discrete-Fourier form.**
For `n > 1` the `n` equally spaced complex phases `exp(2πik/n)`, `k = 0, …, n-1`,
sum to zero. These are precisely the `n`-th roots of unity written via de Moivre's
formula; recognising `exp(2πik/n) = (exp(2πi/n))^k` reduces the claim to the
geometric series for the primitive root `exp(2πi/n)`. This is the identity behind
the vanishing of a full period of a discrete Fourier sampling sum. -/
theorem sum_exp_eq_zero {n : ℕ} (hn : 1 < n) :
    ∑ k ∈ range n, Complex.exp (2 * ↑Real.pi * Complex.I * ↑k / ↑n) = 0 := by
  have h := (Complex.isPrimitiveRoot_exp n (by omega)).geom_sum_eq_zero hn
  rw [← h]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

end DeMoivreOQ05
