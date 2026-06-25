import Mathlib
import Proofs.ArithmeticSeriesOQ02OQ01OQ01

/-
# Dual and symmetric forms of the q-Vandermonde identity
  (arithmetic-series-oq-02-oq-01-oq-01-oq-03)

The parent entry `arithmetic-series-oq-02-oq-01-oq-01` proves the **Gauss
q-Vandermonde convolution identity**

  `[m+n choose r]_q = ∑_{k=0}^{r} q^{k(m+k−r)} · [m choose r−k]_q · [n choose k]_q`.   (V)

The Gaussian binomial `[n choose k]_q = qBinom q n k` is symmetric in its two
*summand* roles in a way the single form (V) hides: it is invariant under the
involutions `m ↔ n` and `k ↦ r−k`. This file makes both symmetries explicit and
proves the resulting **dual / reflected forms equivalent to (V)** — answering the
open question *"derive the dual/symmetric forms of the q-Vandermonde identity
(swap m↔n, or reflect r↦m+n−r) and prove their equivalence, exposing the
symmetry of the q-exponent q^{k(m+k−r)}."*

## What is proved

* `qVandermonde_swap` — the **dual form** obtained by swapping the two factors
  `m ↔ n`. The convolution is symmetric because `m+n = n+m`, so the left-hand
  side is unchanged while the roles of `[m choose ·]` and `[n choose ·]` (and the
  q-exponent `k(m+k−r) ↦ k(n+k−r)`) are exchanged.

* `qVandermonde_sum_symm` — the **equivalence of the two convolution sums**: the
  original sum of (V) and the `m↔n`-swapped sum are *equal as ring elements*
  (both compute `[m+n choose r]_q`). This is the precise statement that the
  q-exponent symmetry `k(m+k−r) ↔ k(n+k−r)` is a genuine identity, not just a
  cosmetic relabelling.

* `qVandermonde_reflect` — the **reflected-index form** obtained by the
  involution `k ↦ r−k` on the summation range. It re-exposes (V) with the
  q-exponent in the dual shape `(r−k)(m−k)` and the two binomial factors
  index-reflected:
  `[m+n choose r]_q = ∑_{k=0}^{r} q^{(r−k)(m−k)} · [m choose k]_q · [n choose r−k]_q`.

* `qVandermonde_reflect_sum_symm` — the corresponding **sum equivalence** for the
  reflected form.

All four results are corollaries of the parent's `qVandermonde` (no new spectral
or analytic input); the only manipulations are `add_comm` on `ℕ` and
`Finset.sum_range_reflect`. The Gaussian binomial `qBinom` and the identity (V)
are imported unchanged from the parent files.

Research file — intentionally NOT registered in `Proofs.lean`.
-/

open GaussianBinomial qVandermondeProof Finset BigOperators

namespace qVandermondeDual

variable {R : Type*} [CommRing R]

/-- **Dual q-Vandermonde (swap `m ↔ n`).** Because the binomial argument `m + n`
is symmetric, the convolution may be written with the roles of `m` and `n`
exchanged; the q-exponent transforms `k(m+k−r) ↦ k(n+k−r)`. -/
theorem qVandermonde_swap (q : R) (m n r : ℕ) :
    qBinom q (m + n) r =
      ∑ k ∈ Finset.range (r + 1),
        q ^ (k * (n + k - r)) * qBinom q n (r - k) * qBinom q m k := by
  rw [show m + n = n + m from Nat.add_comm m n]
  exact qVandermonde q n m r

/-- **Symmetry of the convolution sum.** The original q-Vandermonde sum and its
`m ↔ n`-swap are equal ring elements (both equal `[m+n choose r]_q`). This is the
exact statement that the q-exponent symmetry `k(m+k−r) ↔ k(n+k−r)` is an
identity. -/
theorem qVandermonde_sum_symm (q : R) (m n r : ℕ) :
    (∑ k ∈ Finset.range (r + 1),
        q ^ (k * (m + k - r)) * qBinom q m (r - k) * qBinom q n k) =
      ∑ k ∈ Finset.range (r + 1),
        q ^ (k * (n + k - r)) * qBinom q n (r - k) * qBinom q m k := by
  rw [← qVandermonde q m n r]
  exact qVandermonde_swap q m n r

/-- **Reflected-index q-Vandermonde (involution `k ↦ r−k`).** Reflecting the
summation index re-expresses (V) with the q-exponent in the dual shape
`(r−k)(m−k)` and the two binomial factors index-reflected. -/
theorem qVandermonde_reflect (q : R) (m n r : ℕ) :
    qBinom q (m + n) r =
      ∑ k ∈ Finset.range (r + 1),
        q ^ ((r - k) * (m - k)) * qBinom q m k * qBinom q n (r - k) := by
  rw [qVandermonde q m n r,
    ← Finset.sum_range_reflect
      (fun k => q ^ (k * (m + k - r)) * qBinom q m (r - k) * qBinom q n k) (r + 1)]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hk
  have h1 : r + 1 - 1 - k = r - k := by omega
  have h2 : m + (r - k) - r = m - k := by omega
  have h3 : r - (r - k) = k := by omega
  simp only [h1, h2, h3]

/-- **Symmetry of the reflected convolution sum.** The original q-Vandermonde sum
and its `k ↦ r−k` reflection are equal ring elements. -/
theorem qVandermonde_reflect_sum_symm (q : R) (m n r : ℕ) :
    (∑ k ∈ Finset.range (r + 1),
        q ^ (k * (m + k - r)) * qBinom q m (r - k) * qBinom q n k) =
      ∑ k ∈ Finset.range (r + 1),
        q ^ ((r - k) * (m - k)) * qBinom q m k * qBinom q n (r - k) := by
  rw [← qVandermonde q m n r]
  exact qVandermonde_reflect q m n r

end qVandermondeDual
