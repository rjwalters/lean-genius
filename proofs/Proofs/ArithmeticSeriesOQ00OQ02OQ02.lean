import Mathlib

/-!
# A uniform recurrence generating every Faulhaber power-sum closed form

This file answers the open question raised by `arithmetic-series-oq-00-oq-02`
(the Nicomachus generalization study):

> *Can the Nicomachus identity be generalized to power sums:
>  ∑ₖ kʳ = f(n, r) for some pattern?*

The gallery already records the **closed forms** for individual exponents
(`arithmetic-series-oq-04` proves p = 1, 2, 3 via Bernoulli numbers and
`arithmetic-series-oq-04-oq-01` extends to p = 4, 5, 6 plus the triangular
structure of odd powers).  Those entries answer the question one exponent at a
time.

Here we give the complementary, **uniform** answer: a single recurrence, valid
for *all* exponents simultaneously, that mechanically generates each closed form
from the lower ones.  Writing `S p n = ∑_{k=0}^{n-1} kᵖ`, the recurrence is

  ∑_{j=0}^{p}  C(p+1, j) · S_j(n)  =  n^{p+1}.                         (★)

Solving (★) for its top term gives the standard descent

  (p+1) · S_p(n)  =  n^{p+1}  −  ∑_{j=0}^{p-1} C(p+1, j) · S_j(n),

which determines `S_p` from `S_0, …, S_{p-1}`.  Thus the answer to "is there a
pattern?" is: **yes — the pattern is exactly (★)**, and the closed forms in the
sibling entries are its first few outputs.

The proof of (★) is elementary and Bernoulli-free.  It is the telescoping
identity `∑_{k<n} ((k+1)^{p+1} − k^{p+1}) = n^{p+1}` combined with the binomial
expansion of the forward difference `(k+1)^{p+1} − k^{p+1}`, followed by an
interchange of summation.

All results are over `ℚ` with 0 sorries and 0 axioms.
-/

namespace ArithmeticSeriesOQ00OQ02OQ02

open Finset

/-- The power sum `S p n = 0ᵖ + 1ᵖ + ⋯ + (n-1)ᵖ`, taken over `ℚ`. -/
def S (p n : ℕ) : ℚ := ∑ k ∈ range n, (k : ℚ) ^ p

@[simp] lemma S_def (p n : ℕ) : S p n = ∑ k ∈ range n, (k : ℚ) ^ p := rfl

/-- The forward difference `(k+1)^{p+1} − k^{p+1}` expands, by the binomial
theorem, as a `C(p+1, j)`-weighted combination of the powers `kʲ` for `j ≤ p`.
The top binomial term `k^{p+1}` cancels against the subtracted `k^{p+1}`. -/
lemma diff_pow_expand (p k : ℕ) :
    ((k : ℚ) + 1) ^ (p + 1) - (k : ℚ) ^ (p + 1)
      = ∑ j ∈ range (p + 1), (Nat.choose (p + 1) j : ℚ) * (k : ℚ) ^ j := by
  have hb := add_pow (k : ℚ) 1 (p + 1)
  -- hb : (k+1)^(p+1) = ∑ m ∈ range (p+2), k^m * 1^(p+1-m) * C(p+1, m)
  simp only [one_pow, mul_one] at hb
  rw [Finset.sum_range_succ, Nat.choose_self, Nat.cast_one, mul_one] at hb
  -- hb : (k+1)^(p+1) = (∑ m ∈ range (p+1), k^m * C(p+1, m)) + k^(p+1)
  rw [hb, add_sub_cancel_right]
  exact Finset.sum_congr rfl (fun m _ => mul_comm _ _)

/-- **Power-sum recurrence (★).**  For every exponent `p` and bound `n`,
`∑_{j=0}^{p} C(p+1, j) · S_j(n) = n^{p+1}`.

This single identity holds for *all* `p` at once; the individual Faulhaber
closed forms are recovered by reading it as a recurrence for the top term
(see `power_sum_solved` and the corollaries below). -/
theorem power_sum_recurrence (p n : ℕ) :
    ∑ j ∈ range (p + 1), (Nat.choose (p + 1) j : ℚ) * S j n = (n : ℚ) ^ (p + 1) := by
  -- Rewrite the single sum over `j` as a double sum over `(j, k)`.
  have h1 : ∑ j ∈ range (p + 1), (Nat.choose (p + 1) j : ℚ) * S j n
      = ∑ j ∈ range (p + 1), ∑ k ∈ range n,
          (Nat.choose (p + 1) j : ℚ) * (k : ℚ) ^ j := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [S, Finset.mul_sum]
  rw [h1, Finset.sum_comm]
  -- Collapse the inner sum over `j` via the binomial expansion of the difference.
  have h2 : ∀ k : ℕ, ∑ j ∈ range (p + 1), (Nat.choose (p + 1) j : ℚ) * (k : ℚ) ^ j
      = ((k : ℚ) + 1) ^ (p + 1) - (k : ℚ) ^ (p + 1) :=
    fun k => (diff_pow_expand p k).symm
  rw [Finset.sum_congr rfl (fun k _ => h2 k)]
  -- What remains is a telescoping sum.
  have h3 := Finset.sum_range_sub (fun k => (k : ℚ) ^ (p + 1)) n
  simpa using h3

/-- **Descent form of the recurrence.**  Isolating the top term of (★) expresses
`S_p` in terms of the strictly lower power sums:
`(p+1) · S_p(n) = n^{p+1} − ∑_{j<p} C(p+1, j) · S_j(n)`. -/
theorem power_sum_solved (p n : ℕ) :
    ((p : ℚ) + 1) * S p n
      = (n : ℚ) ^ (p + 1) - ∑ j ∈ range p, (Nat.choose (p + 1) j : ℚ) * S j n := by
  have h := power_sum_recurrence p n
  rw [Finset.sum_range_succ, Nat.choose_succ_self_right] at h
  push_cast at h
  linarith

/-! ## The recurrence in action

The corollaries below run (★) for `p = 0, 1, 2`, recovering the familiar closed
forms.  Each is derived purely from `power_sum_solved` and the previous case —
no separate induction — illustrating that the recurrence is a self-contained
generator of the Faulhaber polynomials. -/

/-- Base case `p = 0`: `S₀(n) = n` (there are `n` terms, each equal to `1`). -/
@[simp] theorem S_zero (n : ℕ) : S 0 n = (n : ℚ) := by
  simp [S]

/-- `p = 1`: the recurrence yields the triangular number `S₁(n) = n(n-1)/2`. -/
theorem S_one (n : ℕ) : S 1 n = ((n : ℚ) ^ 2 - n) / 2 := by
  have h := power_sum_solved 1 n
  rw [Finset.sum_range_one, Nat.choose_zero_right, Nat.cast_one, one_mul, S_zero] at h
  push_cast at h
  linarith

/-- `p = 2`: the recurrence yields `S₂(n) = n(n-1)(2n-1)/6 = (2n³ − 3n² + n)/6`. -/
theorem S_two (n : ℕ) : S 2 n = (2 * (n : ℚ) ^ 3 - 3 * (n : ℚ) ^ 2 + n) / 6 := by
  have h := power_sum_solved 2 n
  rw [Finset.sum_range_succ, Finset.sum_range_one] at h
  -- the two surviving terms are `C(3,0)·S₀ + C(3,1)·S₁`
  rw [Nat.choose_zero_right, Nat.cast_one, one_mul, S_zero] at h
  rw [show Nat.choose 3 1 = 3 from rfl, S_one] at h
  push_cast at h
  linarith

/-- Sanity check: the descent (★) is consistent with the standard Nicomachus
companion `S₂` being a genuine cubic with leading coefficient `1/3`, matching the
general fact that `S_p` has leading term `n^{p+1}/(p+1)` read off from the top of
(★). -/
theorem S_two_leading (n : ℕ) :
    3 * S 2 n - (n : ℚ) ^ 3 = (-3 * (n : ℚ) ^ 2 + n) / 2 := by
  rw [S_two]; ring

end ArithmeticSeriesOQ00OQ02OQ02
