import Proofs.TetrahedralNumberFormulaOQ01
import Mathlib.Combinatorics.Enumerative.Stirling

/-
# The Rising Factorial in the Power Basis via Stirling Numbers of the First Kind

## What This Proves

The companion file `TetrahedralNumberFormulaOQ01Moments` expands **powers** in the
falling-factorial basis using the Stirling numbers of the *second* kind:

    xᵐ = ∑_{r=0}^{m} S(m,r) · (x)_r                        (`pow_eq_sum_stirlingSecond_descFactorial`)

This file establishes the **dual** change of basis — the *rising factorial* expanded in the
**power** basis using the (unsigned) Stirling numbers of the *first* kind:

    x^(n)  =  x(x+1)⋯(x+n-1)  =  ∑_{k=0}^{n} c(n,k) · xᵏ    (`ascFactorial_eq_sum_stirlingFirst_pow`)

where `x^(n) = x.ascFactorial n` is the rising factorial and `c(n,k) = Nat.stirlingFirst n k`
is the unsigned Stirling number of the first kind (the number of permutations of `n` elements
with exactly `k` cycles).  This is the identity that *characterises* the Stirling numbers of
the first kind; Mathlib defines `Nat.stirlingFirst` and proves its recurrence but **not** this
polynomial expansion, so it is built here — exactly mirroring the second-kind expansion in the
sibling file.

Two consequences are recorded:

* `sum_stirlingFirst_eq_factorial` — the **row-sum** identity `∑_{k} c(n,k) = n!`
  (specialising `x = 1`, since a permutation of `n` elements has *some* number of cycles).

* `factorial_mul_simplexNumber_eq_sum_stirlingFirst_pow` — the payoff for the figurate theme
  of this problem: combining the dual with the parent's division-free closed form
  `d! · P_d(n) = (n+1)^(d)` (`factorial_mul_simplexNumber`) exhibits the figurate number as an
  **explicit degree-`d` polynomial in `n+1`** with Stirling-first coefficients:

    d! · P_d(n) = ∑_{k=0}^{d} c(d,k) · (n+1)ᵏ.

  This is the concrete "the `d`-dimensional simplex number is a polynomial of degree `d`"
  statement, with its coefficients named.

## Approach

The main identity is proved by induction on `n`, structurally identical to the second-kind
proof in the sibling file:

* Base `n = 0`: `x^(0) = 1 = c(0,0)·x⁰`.
* Step: multiply the hypothesis by the leading factor `x + n` of `x^(n+1) = (x+n)·x^(n)`
  (`Nat.ascFactorial_succ`), split into `x·(…) + n·(…)`, and match against the target
  `∑_k c(n+1,k)·xᵏ`.  Peeling the `k = 0` term (`c(n+1,0) = 0`) and applying the Stirling
  recurrence `c(n+1,k+1) = n·c(n,k+1) + c(n,k)` (`Nat.stirlingFirst_succ_succ`) reduces the
  match to the reindexing identity
  `∑_k n·c(n,k+1)·x^{k+1} = ∑_k n·c(n,k)·xᵏ`, whose boundary terms vanish via
  `c(n,n+1) = 0` and `n·c(n,0) = 0`.

## Honesty Note

This is exact, axiom-free discrete combinatorics.  The change-of-basis identity is the genuine
missing Mathlib lemma (the first-kind dual of the sibling file's second-kind lemma); the
row-sum and figurate-polynomial statements are its direct consequences.  It touches no open
analytic content.
-/

namespace TetrahedralNumberFormulaOQ01

open Finset Nat

/-! ### The rising-factorial-to-power change of basis (Stirling first kind) -/

/-- **The rising factorial in the power basis (Stirling first kind).** The unsigned Stirling
numbers of the first kind are the coefficients expanding the rising factorial as an ordinary
polynomial:

    x^(n) = x(x+1)⋯(x+n-1) = ∑_{k=0}^{n} c(n,k) · xᵏ,

with `c(n,k) = Nat.stirlingFirst n k` and `x^(n) = x.ascFactorial n`.  This is the defining
property of the Stirling numbers of the first kind; Mathlib provides `Nat.stirlingFirst` and
its recurrence but not this expansion, so it is established here by induction on `n` — the
exact dual of `pow_eq_sum_stirlingSecond_descFactorial`, which expands powers in the
falling-factorial basis with the second-kind numbers.

The step multiplies the hypothesis by the leading factor `x + n` of `x^(n+1) = (x+n)·x^(n)`,
producing `∑ c(n,k)·x^{k+1} + ∑ n·c(n,k)·xᵏ`, and matches this against the target
`∑_k c(n+1,k)·xᵏ`.  Peeling the `k = 0` term (`c(n+1,0) = 0`) and applying the Stirling
recurrence `c(n+1,k+1) = n·c(n,k+1) + c(n,k)` splits the target into exactly those two sums,
once the reindexing identity `∑ n·c(n,k+1)·x^{k+1} = ∑ n·c(n,k)·xᵏ` (whose boundary terms
vanish via `c(n,n+1) = 0`) is discharged. -/
theorem ascFactorial_eq_sum_stirlingFirst_pow (x n : ℕ) :
    x.ascFactorial n = ∑ k ∈ range (n + 1), stirlingFirst n k * x ^ k := by
  induction n with
  | zero => simp
  | succ n ih =>
    -- The `k = 0` boundary of the lower-order sum: `n · c(n,0) = 0` for every `n`
    -- (either `n = 0`, or `c(n,0) = 0` for `n ≥ 1`).
    have hz : n * stirlingFirst n 0 = 0 := by
      cases n with
      | zero => simp
      | succ m => simp [stirlingFirst_succ_zero]
    -- Reindexing identity for the "lower-order" sum: shifting the index up by one matches the
    -- `n·c(n,k)` weighting; both boundary terms vanish (`c(n,n+1) = 0` on the left, `n·c(n,0)`
    -- on the right).
    have key : (∑ k ∈ range (n + 1), n * stirlingFirst n (k + 1) * x ^ (k + 1))
        = ∑ k ∈ range (n + 1), n * stirlingFirst n k * x ^ k := by
      rw [Finset.sum_range_succ
            (fun k => n * stirlingFirst n (k + 1) * x ^ (k + 1)) n,
          Finset.sum_range_succ'
            (fun k => n * stirlingFirst n k * x ^ k) n]
      simp only [stirlingFirst_eq_zero_of_lt (Nat.lt_succ_self n), Nat.mul_zero, Nat.zero_mul,
        Nat.add_zero, pow_zero, Nat.mul_one, hz]
    -- Expand `x^(n+1) = (x + n) · x^(n)` via the hypothesis, splitting `(x + n)`.
    have expand : x.ascFactorial (n + 1)
        = (∑ k ∈ range (n + 1), stirlingFirst n k * x ^ (k + 1))
          + ∑ k ∈ range (n + 1), n * stirlingFirst n k * x ^ k := by
      rw [Nat.ascFactorial_succ, Nat.add_mul, ih, Finset.mul_sum, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro k _
        rw [pow_succ]
        ring
      · apply Finset.sum_congr rfl
        intro k _
        ring
    -- Transform the target `∑_{k ≤ n+1} c(n+1,k)·xᵏ` into the same two sums.
    rw [expand,
        Finset.sum_range_succ'
          (fun k => stirlingFirst (n + 1) k * x ^ k) (n + 1)]
    have hrhs : (∑ k ∈ range (n + 1), stirlingFirst (n + 1) (k + 1) * x ^ (k + 1))
        = (∑ k ∈ range (n + 1), stirlingFirst n k * x ^ (k + 1))
          + ∑ k ∈ range (n + 1), n * stirlingFirst n (k + 1) * x ^ (k + 1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [stirlingFirst_succ_succ]
      ring
    rw [hrhs, key]
    simp [stirlingFirst_succ_zero]

/-! ### The row-sum identity -/

/-- **Row sum of the Stirling numbers of the first kind.** Summing `c(n,k)` over all cycle
counts `k` gives `n!`: every permutation of `n` elements has *some* number of cycles, and
`n!` counts all permutations.  Formally this is the `x = 1` specialisation of
`ascFactorial_eq_sum_stirlingFirst_pow`, using `Nat.one_ascFactorial : 1^(n) = n!`. -/
theorem sum_stirlingFirst_eq_factorial (n : ℕ) :
    ∑ k ∈ range (n + 1), stirlingFirst n k = n ! := by
  have h := ascFactorial_eq_sum_stirlingFirst_pow 1 n
  rw [Nat.one_ascFactorial] at h
  simpa using h.symm

/-! ### The figurate number as an explicit Stirling-first polynomial -/

/-- **The figurate number as a Stirling-first polynomial in `n + 1`.** Feeding the parent's
division-free closed form `d! · P_d(n) = (n+1)^(d)` (`factorial_mul_simplexNumber`) through the
dual change of basis exhibits `d! · P_d(n)` as an explicit degree-`d` polynomial in `n + 1`
whose coefficients are the unsigned Stirling numbers of the first kind:

    d! · P_d(n) = ∑_{k=0}^{d} c(d,k) · (n+1)ᵏ.

This is the quantitative form of "the `d`-dimensional simplex number is a polynomial of degree
`d` in `n`", with the coefficients named.  For example `d = 3` gives
`6·P_3(n) = 2·(n+1) + 3·(n+1)² + (n+1)³` (Stirling row `c(3,·) = 0, 2, 3, 1`), the classical
`n(n+1)(n+2)` written in the shifted-power basis. -/
theorem factorial_mul_simplexNumber_eq_sum_stirlingFirst_pow (d n : ℕ) :
    d ! * simplexNumber d n
      = ∑ k ∈ range (d + 1), stirlingFirst d k * (n + 1) ^ k := by
  rw [factorial_mul_simplexNumber, ascFactorial_eq_sum_stirlingFirst_pow]

end TetrahedralNumberFormulaOQ01
