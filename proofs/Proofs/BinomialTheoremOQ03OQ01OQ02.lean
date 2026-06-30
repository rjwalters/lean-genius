/-
# The Alternating (Signed) Falling-Factorial Moment — Finite Differences (OQ-03-OQ-01-OQ-02)

Research Question (follow-up to OQ-03-OQ-01 "Combinatorial Moments of the
Binomial Coefficients").  The parent computes the *unsigned* moments

    Σ_{k=0}^{n} k·C(n,k)      = n·2ⁿ⁻¹,
    Σ_{k=0}^{n} k(k-1)·C(n,k) = n(n-1)·2ⁿ⁻²,   …

— the values of `(d/dx)^r (1+x)ⁿ` at `x = +1`.  What happens at the *other*
natural evaluation point `x = -1`, i.e. what are the **signed** moments

    Σ_{k=0}^{n} (-1)ᵏ · k^(r) · C(n,k)            (k^(r) = Nat.descFactorial k r)?

Unlike the unsigned case, where `(1+x)ⁿ⁻ʳ` is still large at `x = 1`, here the
factor `(1+x)ⁿ⁻ʳ` *vanishes* at `x = -1` for every `r < n`.  This is the
generating-function shadow of the classical **finite-difference** fact: the
`n`-th forward difference annihilates every polynomial of degree `< n`.

Answer.  For all `n r : ℕ`,

    Σ_{k=0}^{n} (-1)ᵏ · k^(r) · C(n,k) = (-1)ʳ · n^(r) · [n = r],

a single closed form (`[P]` is the Iverson bracket, `1` if `P` else `0`).  In
particular the sum **vanishes whenever `n ≠ r`** — for `r < n` because the
polynomial `k^(r)` has degree `r < n`, and for `r > n` because every term is
zero — and at the diagonal `r = n` it peaks at

    Σ_{k=0}^{n} (-1)ᵏ · k^(n) · C(n,k) = (-1)ⁿ · n!.

None of these signed moments is in Mathlib (Mathlib has only the zeroth one,
`Int.alternating_sum_range_choose : Σ (-1)ᵏ C(n,k) = [n = 0]`).

The proof reuses the parent's single *absorption* identity
`(k+1)·C(m+1,k+1) = (m+1)·C(m,k)`.  Over ℤ it lifts the signed sum to the
recurrence

    T(m+1, r+1) = -(m+1) · T(m, r),     T(n, 0) = [n = 0],

— identical to the unsigned recurrence `S(m+1,r+1) = (m+1)·S(m,r)` of OQ-01 but
carrying the extra minus sign produced by reindexing `k ↦ k+1` against `(-1)ᵏ`.
Iterating it `r` times unfolds `n^(r)` through `descFactorial` and lands the base
case `T(n-r, 0)`, which is Mathlib's alternating binomial sum.  The whole proof
is one induction on `r`; everything stays exact over ℤ.

Tags: combinatorics, binomial-coefficients, moments, falling-factorial,
finite-differences, alternating-sum, absorption, generating-functions
-/

import Mathlib
import Proofs.BinomialTheoremOQ03

open Finset BigOperators

namespace BinomialTheoremOQ03OQ01OQ02

/-! ## Part I: The signed absorption step

The engine of the induction.  Reindexing `k ↦ k+1` against the alternating sign
`(-1)ᵏ` is what turns the parent's positive recurrence into a *signed* one. -/

/-- **Signed falling-factorial absorption step.**  Peeling the vanishing `k = 0`
term, reindexing `k ↦ k+1`, and applying the single absorption identity
`(k+1)·C(m+1,k+1) = (m+1)·C(m,k)` term-by-term turns the `(r+1)`-th *signed*
falling-factorial sum over `range (m+2)` into `-(m+1)` times the `r`-th signed
falling-factorial sum over `range (m+1)`.  The minus sign comes from the
`(-1)ᵏ⁺¹ = -(-1)ᵏ` produced by the reindex; everything else is exactly the
parent's positive step. -/
theorem signed_step (m r : ℕ) :
    ∑ k ∈ range (m + 2),
        (-1 : ℤ) ^ k * (k.descFactorial (r + 1) : ℤ) * ((m + 1).choose k : ℤ)
      = -(m + 1 : ℤ) *
          ∑ k ∈ range (m + 1),
            (-1 : ℤ) ^ k * (k.descFactorial r : ℤ) * (m.choose k : ℤ) := by
  rw [Finset.sum_range_succ']
  -- the peeled `k = 0` term is `(-1)⁰ · 0^(r+1) · C(m+1,0) = 0`
  simp only [Nat.zero_descFactorial_succ, Nat.cast_zero, mul_zero, zero_mul, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  -- (k+1)^(r+1) = (k+1) · k^(r), and absorption rewrites the choose product
  rw [Nat.succ_descFactorial_succ]
  have habZ : ((k : ℤ) + 1) * ((m + 1).choose (k + 1) : ℤ)
      = ((m : ℤ) + 1) * (m.choose k : ℤ) := by
    exact_mod_cast BinomialTheoremOQ03.absorption m k
  push_cast
  linear_combination (-((-1 : ℤ) ^ k) * (k.descFactorial r : ℤ)) * habZ

/-! ## Part II: The general signed moment (Iverson-bracket closed form) -/

/-- **General signed falling-factorial moment.**  For all `n r : ℕ`,

    Σ_{k=0}^{n} (-1)ᵏ · k^(r) · C(n,k) = (-1)ʳ · n^(r) · [n = r],

where `k^(r) = Nat.descFactorial k r` and `[n = r] = if n = r then 1 else 0`.
Proved by induction on `r`: the base case `r = 0` is Mathlib's alternating
binomial sum `Σ (-1)ᵏ C(n,k) = [n = 0]`, and the step is the recurrence
`signed_step` (`T(m+1,r+1) = -(m+1)·T(m,r)`) together with
`Nat.succ_descFactorial_succ`.  Holds unconditionally; for `n ≠ r` the right-hand
side is `0`. -/
theorem signed_descFactorial_moment (n r : ℕ) :
    ∑ k ∈ range (n + 1),
        (-1 : ℤ) ^ k * (k.descFactorial r : ℤ) * (n.choose k : ℤ)
      = (-1 : ℤ) ^ r * (n.descFactorial r : ℤ) * (if n = r then 1 else 0) := by
  induction r generalizing n with
  | zero =>
    -- `k^(0) = 1`, so this is exactly the alternating binomial sum
    simpa [Nat.descFactorial_zero] using
      (Int.alternating_sum_range_choose (n := n))
  | succ r ih =>
    cases n with
    | zero =>
      -- the only term is `k = 0`, whose `0^(r+1) = 0`; RHS is `[0 = r+1] = 0` too
      simp
    | succ m =>
      rw [signed_step m r, ih m, Nat.succ_descFactorial_succ]
      rcases eq_or_ne m r with h | h
      · subst h
        rw [if_pos rfl, if_pos rfl]
        push_cast
        ring
      · rw [if_neg h, if_neg (show m + 1 ≠ r + 1 by omega)]
        ring

/-! ## Part III: Vanishing (finite differences) and the diagonal peak -/

/-- **Vanishing off the diagonal.**  Whenever `n ≠ r`,

    Σ_{k=0}^{n} (-1)ᵏ · k^(r) · C(n,k) = 0.

For `r < n` this is the finite-difference annihilation of a degree-`r` polynomial
by the `n`-th alternating sum; for `r > n` every term already vanishes. -/
theorem signed_descFactorial_moment_of_ne (n r : ℕ) (h : n ≠ r) :
    ∑ k ∈ range (n + 1),
        (-1 : ℤ) ^ k * (k.descFactorial r : ℤ) * (n.choose k : ℤ) = 0 := by
  rw [signed_descFactorial_moment, if_neg h, mul_zero]

/-- **Diagonal peak.**  At `r = n` the signed falling-factorial moment is the
nonzero extreme

    Σ_{k=0}^{n} (-1)ᵏ · k^(n) · C(n,k) = (-1)ⁿ · n!.

This is the `n`-th finite difference of the leading monomial `x^(n)`, equal to
`n!` (up to the alternating sign), and the discrete analogue of `dⁿ/dxⁿ xⁿ = n!`. -/
theorem signed_descFactorial_moment_diagonal (n : ℕ) :
    ∑ k ∈ range (n + 1),
        (-1 : ℤ) ^ k * (k.descFactorial n : ℤ) * (n.choose k : ℤ)
      = (-1 : ℤ) ^ n * (n.factorial : ℤ) := by
  rw [signed_descFactorial_moment, if_pos rfl, Nat.descFactorial_self]
  ring

/-! ## Part IV: Concrete signed power moments (companions to the parent) -/

/-- **Signed first moment.**  `Σ_{k=0}^{n} (-1)ᵏ · k · C(n,k) = 0` for `n ≥ 2`.
The alternating companion of the parent's `Σ k·C(n,k) = n·2ⁿ⁻¹`: weighting the
binomial coefficients by `k` and alternating signs sums to zero once `n` exceeds
the degree `1`.  (At `n = 1` the sum is `-1`, the diagonal peak.) -/
theorem alternating_sum_id_mul_choose (n : ℕ) (h : 2 ≤ n) :
    ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * (k : ℤ) * (n.choose k : ℤ) = 0 := by
  have hkey := signed_descFactorial_moment_of_ne n 1 (by omega)
  simpa [Nat.descFactorial_one] using hkey

/-- **Signed second factorial moment.**  `Σ_{k=0}^{n} (-1)ᵏ · k(k-1) · C(n,k) = 0`
for `n ≥ 3`.  The alternating companion of the parent's
`Σ k(k-1)·C(n,k) = n(n-1)·2ⁿ⁻²`; it vanishes once `n` exceeds the degree `2`. -/
theorem alternating_sum_descFactorial2_mul_choose (n : ℕ) (h : 3 ≤ n) :
    ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * ((k * (k - 1) : ℕ) : ℤ) * (n.choose k : ℤ) = 0 := by
  have hkey := signed_descFactorial_moment_of_ne n 2 (by omega)
  have hdf : ∀ k : ℕ, k.descFactorial 2 = k * (k - 1) := fun k => by
    rw [show (2 : ℕ) = 1 + 1 from rfl, Nat.descFactorial_succ, Nat.descFactorial_one,
      Nat.mul_comm]
  simp only [hdf] at hkey
  exact hkey

end BinomialTheoremOQ03OQ01OQ02
