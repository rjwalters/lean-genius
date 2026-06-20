import Mathlib

/-
# Chebyshev's sum inequality in classical monotone-sequence form

Mathlib states Chebyshev's sum inequality through the order-correlation predicates
`MonovaryOn` / `AntivaryOn` (`Mathlib/Algebra/Order/Chebyshev.lean`):

* `MonovaryOn.sum_mul_sum_le_card_mul_sum`
* `AntivaryOn.card_mul_sum_le_sum_mul_sum`

These are the right level of generality, but they are *not* the form in which the
inequality is usually quoted: for two sequences sorted **the same way**

  a₁ ≤ a₂ ≤ ⋯ ≤ aₙ   and   b₁ ≤ b₂ ≤ ⋯ ≤ bₙ

one has

  (∑ aᵢ)(∑ bᵢ) ≤ n · ∑ aᵢbᵢ,

and the inequality **reverses** when the sequences are sorted oppositely. This file
packages exactly that classical statement — over `Finset.range n` for real sequences
and over an arbitrary finite index set for `MonotoneOn` data — by feeding the
`Monotone`/`Antitone` ⇒ `Monovary`/`Antivary` bridges into the Mathlib lemmas. It also
records the Cauchy–Schwarz-type square corollary and the equivalent statement about
arithmetic means (the mean of the products dominates the product of the means).

All results are fully verified with no extra axioms.
-/

namespace ChebyshevSumMonotone

open Finset

/-! ## Real sequences indexed by `range n` -/

section Sequences

variable {n : ℕ} {f g : ℕ → ℝ}

/-- **Chebyshev's sum inequality** (similarly sorted sequences). If `f` and `g` are both
monotone, then the product of their partial sums is at most `n` times the sum of their
pointwise products. -/
theorem chebyshev_monotone (hf : Monotone f) (hg : Monotone g) :
    (∑ i ∈ range n, f i) * (∑ i ∈ range n, g i) ≤ n * ∑ i ∈ range n, f i * g i := by
  have h : MonovaryOn f g ↑(range n) := (hf.monovary hg).monovaryOn _
  simpa using h.sum_mul_sum_le_card_mul_sum

/-- **Reverse Chebyshev sum inequality** (oppositely sorted sequences). If `f` is monotone
and `g` is antitone, the inequality reverses. -/
theorem chebyshev_antitone (hf : Monotone f) (hg : Antitone g) :
    (n : ℝ) * ∑ i ∈ range n, f i * g i ≤ (∑ i ∈ range n, f i) * ∑ i ∈ range n, g i := by
  have h : AntivaryOn f g ↑(range n) := (hf.antivary hg).antivaryOn _
  simpa using h.card_mul_sum_le_sum_mul_sum

/-- Cauchy–Schwarz-type corollary: the square of a partial sum is at most `n` times the
sum of the squares (the self-monovarying special case of Chebyshev). -/
theorem sq_sum_le (f : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ range n, f i) ^ 2 ≤ n * ∑ i ∈ range n, (f i) ^ 2 := by
  simpa using sq_sum_le_card_mul_sum_sq (s := range n) (f := f)

/-- Averaged form of Chebyshev's sum inequality: for similarly sorted sequences, the mean
of the products dominates the product of the means. -/
theorem chebyshev_mean (hf : Monotone f) (hg : Monotone g) (hn : 0 < n) :
    (∑ i ∈ range n, f i) / n * ((∑ i ∈ range n, g i) / n)
      ≤ (∑ i ∈ range n, f i * g i) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have key := chebyshev_monotone (n := n) hf hg
  rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hn']
  nlinarith [key, hn']

end Sequences

/-! ## Arbitrary finite index sets via `MonotoneOn` -/

section General

variable {ι : Type*} [LinearOrder ι] {s : Finset ι} {f g : ι → ℝ}

/-- Chebyshev's sum inequality for functions monotone on a finite set `s`. -/
theorem chebyshev_monotoneOn (hf : MonotoneOn f ↑s) (hg : MonotoneOn g ↑s) :
    (∑ i ∈ s, f i) * (∑ i ∈ s, g i) ≤ (#s : ℝ) * ∑ i ∈ s, f i * g i :=
  (hf.monovaryOn hg).sum_mul_sum_le_card_mul_sum

/-- Reverse Chebyshev's sum inequality for `f` monotone and `g` antitone on a finite set. -/
theorem chebyshev_antitoneOn (hf : MonotoneOn f ↑s) (hg : AntitoneOn g ↑s) :
    (#s : ℝ) * ∑ i ∈ s, f i * g i ≤ (∑ i ∈ s, f i) * ∑ i ∈ s, g i :=
  (hf.antivaryOn hg).card_mul_sum_le_sum_mul_sum

end General

/-! ## Worked instance -/

/-- A concrete instance with the increasing sequence `0, 1, 2`:
`(0 + 1 + 2)² ≤ 3 · (0² + 1² + 2²)`, i.e. `9 ≤ 15`, obtained from `sq_sum_le`. -/
example : ((0 : ℝ) + 1 + 2) ^ 2 ≤ 3 * ((0 : ℝ) ^ 2 + 1 ^ 2 + 2 ^ 2) := by
  have h := sq_sum_le (fun i : ℕ => (i : ℝ)) 3
  simpa [Finset.sum_range_succ] using h

end ChebyshevSumMonotone
