import Mathlib
/-
# De Moivre OQ-01-OQ-01-OQ-01-OQ-01: The Explicit Closed Form of the Chebyshev U_n

## Open Question

This entry answers the **leading open question** posed by the parent entry
`de-moivre-oq-01-oq-01-oq-01` ("The Binomial Expansion of sin(nθ) and its
Chebyshev-U Connection"):

> Can the polynomial coefficients of `U_n` over `ℤ` be read off from the
> odd-index expansion, giving an explicit closed form for `U_n` analogous to
> the `T_n` coefficient question?

The answer is **yes**.  We prove the classical explicit formula for the
Chebyshev polynomial of the second kind

  `U_n(X) = ∑_{k=0}^{⌊n/2⌋} (-1)^k · C(n-k, k) · (2X)^{n-2k}`,

as an identity of integer polynomials `U ℤ n = Uexpl n`.  Mathlib defines
`Polynomial.Chebyshev.U` by its recurrence but (as of the current version)
provides **no** explicit coefficient formula — its source even lists
"Add explicit formula ... for Chebyshev polynomials" as a TODO — so this is a
genuinely new, machine-checked closed form rather than a restatement.

## Mathematical Content

The Chebyshev polynomials of the second kind satisfy `U_0 = 1`, `U_1 = 2X`, and
the recurrence `U_{n+2} = 2X·U_{n+1} - U_n`.  The candidate explicit sum
`Uexpl n` satisfies the *same* two base cases and the *same* recurrence, so the
two agree for all `n` by two-step induction.

The heart of the proof is the **termwise Pascal recurrence** (`term_succ_rec`):

  `term (n+2) (k+1) = 2X · term (n+1) (k+1) - term n k`,

where `term m k = (-1)^k · C(m-k, k) · (2X)^{m-2k}`.  Shifting the summation
index by one (`k ↦ k+1`) keeps every binomial coefficient of the classical form
`C((n-k)+1, k+1)`, so Pascal's rule `C((n-k)+1, k+1) = C(n-k, k) + C(n-k, k+1)`
applies directly, with the two Pascal pieces producing the `-term n k` and
`2X·term (n+1) (k+1)` contributions respectively.  Boundary terms where
`2k > m` vanish because `C(m-k, k) = 0` (`Nat.choose_eq_zero_of_lt`), which lets
us sum over a uniform range and dispenses with all floor bookkeeping.

## What is proved here (0 axioms, Mathlib-backed)

* `term_eq_zero`     — a summand vanishes once `2k > m`.
* `Uexpl_eq_sum_range`— `Uexpl n` may be summed over any range covering its support.
* `term_succ_rec`    — the termwise Pascal recurrence (the combinatorial core).
* `Uexpl_rec`        — `Uexpl` obeys the Chebyshev-U recurrence.
* `Uexpl_zero`, `Uexpl_one` — the two base cases.
* `U_eq_Uexpl`       — **the explicit closed form** `U ℤ n = Uexpl n`.

This supplies the `U_n` coefficient formula that mirrors, on the second-kind
side, the `T_n` development of the ancestor entries; together they give explicit
integer-coefficient closed forms for both kinds of Chebyshev polynomials.
-/

open Polynomial Finset

namespace DeMoivreExplicitU

/-- The `k`-th summand of the explicit expansion of `U_m`:
`(-1)^k · C(m-k, k) · (2X)^{m-2k}`. -/
noncomputable def term (m k : ℕ) : Polynomial ℤ :=
  (-1 : Polynomial ℤ) ^ k * ((m - k).choose k : Polynomial ℤ) * (2 * X) ^ (m - 2 * k)

/-- The explicit closed-form candidate for `U_n`:
`∑_{k=0}^{⌊n/2⌋} (-1)^k · C(n-k, k) · (2X)^{n-2k}`. -/
noncomputable def Uexpl (n : ℕ) : Polynomial ℤ :=
  ∑ k ∈ Finset.range (n / 2 + 1), term n k

/-- A summand vanishes once `2k > m`, because the binomial coefficient is zero. -/
lemma term_eq_zero {m k : ℕ} (h : m < 2 * k) : term m k = 0 := by
  have hlt : m - k < k := by omega
  simp [term, Nat.choose_eq_zero_of_lt hlt]

/-- `Uexpl n` may be summed over any range large enough to contain its support. -/
lemma Uexpl_eq_sum_range {n N : ℕ} (hN : n / 2 + 1 ≤ N) :
    Uexpl n = ∑ k ∈ Finset.range N, term n k := by
  unfold Uexpl
  apply Finset.sum_subset
  · intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  · intro k _ hk
    rw [Finset.mem_range, not_lt] at hk
    exact term_eq_zero (by omega)

/-- The termwise Pascal recurrence, with the summation index shifted by one.
This is the combinatorial core: `term (n+2) (k+1) = 2X·term (n+1) (k+1) - term n k`. -/
lemma term_succ_rec (n k : ℕ) :
    term (n + 2) (k + 1) = 2 * X * term (n + 1) (k + 1) - term n k := by
  rcases le_or_gt (2 * k + 1) n with h | h
  · -- Regular case `n ≥ 2k+1`: all exponents are genuine and Pascal applies.
    have e1 : n + 2 - (k + 1) = (n - k) + 1 := by omega
    have e2 : n + 2 - 2 * (k + 1) = (n - 1 - 2 * k) + 1 := by omega
    have e3 : n + 1 - (k + 1) = n - k := by omega
    have e4 : n + 1 - 2 * (k + 1) = n - 1 - 2 * k := by omega
    have e5 : n - 2 * k = (n - 1 - 2 * k) + 1 := by omega
    simp only [term, e1, e2, e3, e4, e5, Nat.choose_succ_succ, pow_succ]
    push_cast
    ring
  · -- Degenerate case `n ≤ 2k`: the `term (n+1) (k+1)` piece vanishes.
    have hz : term (n + 1) (k + 1) = 0 := term_eq_zero (by omega)
    rw [hz, mul_zero, zero_sub]
    rcases eq_or_lt_of_le (show n ≤ 2 * k from by omega) with he | hl
    · -- `n = 2k`: both surviving terms are `±1`.
      subst he
      have a1 : 2 * k + 2 - (k + 1) = k + 1 := by omega
      have a2 : 2 * k + 2 - 2 * (k + 1) = 0 := by omega
      have a3 : 2 * k - k = k := by omega
      have a4 : 2 * k - 2 * k = 0 := by omega
      simp only [term, a1, a2, a3, a4, Nat.choose_self, Nat.cast_one, pow_zero, pow_succ]
      ring
    · -- `n < 2k`: both surviving terms vanish.
      rw [term_eq_zero (show n + 2 < 2 * (k + 1) by omega),
          term_eq_zero (show n < 2 * k from hl), neg_zero]

/-- `Uexpl` obeys the Chebyshev-U recurrence `Uexpl (n+2) = 2X·Uexpl (n+1) - Uexpl n`. -/
lemma Uexpl_rec (n : ℕ) :
    Uexpl (n + 2) = 2 * X * Uexpl (n + 1) - Uexpl n := by
  have hU2 : Uexpl (n + 2)
      = (∑ k ∈ Finset.range (n + 1), term (n + 2) (k + 1)) + term (n + 2) 0 := by
    rw [Uexpl_eq_sum_range (show (n + 2) / 2 + 1 ≤ n + 2 by omega)]
    exact Finset.sum_range_succ' (term (n + 2)) (n + 1)
  have hU1 : Uexpl (n + 1)
      = (∑ k ∈ Finset.range (n + 1), term (n + 1) (k + 1)) + term (n + 1) 0 := by
    rw [Uexpl_eq_sum_range (show (n + 1) / 2 + 1 ≤ n + 2 by omega)]
    exact Finset.sum_range_succ' (term (n + 1)) (n + 1)
  have hU0 : Uexpl n = ∑ k ∈ Finset.range (n + 1), term n k := by
    rw [Uexpl_eq_sum_range (show n / 2 + 1 ≤ n + 2 by omega), Finset.sum_range_succ,
        term_eq_zero (show n < 2 * (n + 1) by omega), add_zero]
  have hA : (∑ k ∈ Finset.range (n + 1), term (n + 2) (k + 1))
      = 2 * X * (∑ k ∈ Finset.range (n + 1), term (n + 1) (k + 1))
        - ∑ k ∈ Finset.range (n + 1), term n k := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k _ => term_succ_rec n k)
  have h0 : term (n + 2) 0 = 2 * X * term (n + 1) 0 := by
    simp only [term, pow_zero, Nat.sub_zero, mul_zero, Nat.choose_zero_right,
      Nat.cast_one, mul_one, one_mul]
    rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
    ring
  rw [hU2, hU1, hU0, hA, h0]
  ring

/-- Base case `U_0 = 1`. -/
lemma Uexpl_zero : Uexpl 0 = 1 := by
  simp [Uexpl, term]

/-- Base case `U_1 = 2X`. -/
lemma Uexpl_one : Uexpl 1 = 2 * X := by
  simp [Uexpl, term]

/-- **The explicit closed form of the Chebyshev polynomial of the second kind.**
`U_n(X) = ∑_{k=0}^{⌊n/2⌋} (-1)^k · C(n-k, k) · (2X)^{n-2k}`. -/
theorem U_eq_Uexpl (n : ℕ) : Polynomial.Chebyshev.U ℤ n = Uexpl n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [Uexpl_zero]
  | one => simp [Uexpl_one]
  | more n ih1 ih2 =>
      have h := Polynomial.Chebyshev.U_add_two ℤ (n : ℤ)
      rw [Uexpl_rec, ← ih1, ← ih2]
      push_cast
      push_cast at h
      exact h

/-- Sanity check: the explicit formula reproduces `U_2 = 4X² - 1`. -/
example : Uexpl 2 = 4 * X ^ 2 - 1 := by
  simp only [Uexpl, Finset.sum_range_succ, Finset.sum_range_zero, term]
  norm_num
  ring

/-- Sanity check: the explicit formula reproduces `U_4 = 16X⁴ - 12X² + 1`. -/
example : Uexpl 4 = 16 * X ^ 4 - 12 * X ^ 2 + 1 := by
  simp only [Uexpl, Finset.sum_range_succ, Finset.sum_range_zero, term]
  norm_num
  ring

/-- Consistency: composing with the Mathlib definition, `U_3 = 8X³ - 4X`. -/
example : Polynomial.Chebyshev.U ℤ ((3 : ℕ) : ℤ) = 8 * X ^ 3 - 4 * X := by
  rw [U_eq_Uexpl]
  simp only [Uexpl, Finset.sum_range_succ, Finset.sum_range_zero, term]
  norm_num
  ring

end DeMoivreExplicitU
