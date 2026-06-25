import Mathlib

/-
# Combinations Formula OQ-01-OQ-02: the terminating Gauss ₂F₁ summation

The parent entry `combinations-formula-oq-01` proves the classical
**Vandermonde convolution** for binomial coefficients,
`C(m + n, r) = ∑_{k} C(m, k) · C(n, r − k)`, a purely natural-number identity.
This file lifts that identity to the level of the **Gauss (ordinary)
hypergeometric series** `₂F₁`, of which Vandermonde is the terminating special
case.

Mathlib already provides `descPochhammer_smeval_add` (a Vandermonde convolution
for descending Pochhammer symbols, phrased through `smeval`) and
`ordinaryHypergeometric` (notation `₂F₁`, the analytic series
`∑ (a)_n (b)_n / (c)_n · xⁿ/n!`). It does **not** provide any *summation
theorem* giving a closed form for the value of `₂F₁`. The cornerstone such
result is **Gauss's second / terminating theorem** (Chu–Vandermonde):

  `₂F₁(−n, b; c; 1) = (c − b)_n / (c)_n`,

valid because the upper parameter `−n` makes the series terminate. Clearing
denominators turns it into a polynomial identity valid over *any* commutative
ring, with no positivity, division, or convergence hypotheses:

  `∑_{i+j=n} (−1)ⁱ C(n,i) · (b)ᵢ · (c+i)ⱼ  =  (c − b)_n`,        (★)

where `(z)_m = (ascPochhammer _ m).eval z` is the rising factorial.

## What is proved here

* `descPochhammer_eval_vandermonde` / `ascPochhammer_eval_vandermonde` — the
  Vandermonde convolution in `.eval` form over a commutative ring, for falling
  and rising factorials respectively (the polynomial backbone). The rising form
  is the Chu–Vandermonde identity that generalizes the parent's binomial one.
* `ascPochhammer_eval_eq_descPochhammer'` — the bridge `(z)_m = (z+m−1)^{≤m}`.
* `neg_one_pow_mul_ascPochhammer_eval` — the sign bridge `(−1)ⁱ (b)ᵢ = (−b)^{≤i}`.
* `gauss_terminating_ring` — the ring-level terminating identity (★).
* `gauss_terminating_field` — the genuine quotient form
  `∑_{i+j=n} (−1)ⁱ C(n,i) (b)ᵢ / (c)ᵢ = (c − b)_n / (c)_n` over a field, under
  the single nonvanishing hypothesis `(c)_n ≠ 0`.

## Method

Because `(z)_m = (z+m−1)^{≤m}` (rising = falling shifted) and
`(−1)ⁱ (b)ᵢ = (−b)^{≤i}`, every summand of (★) becomes a *falling* Pochhammer
with a base independent of the summation index `i`:
`(−1)ⁱ (b)ᵢ · (c+i)_{n−i} = (−b)^{≤i} · (c+n−1)^{≤(n−i)}`. So (★) is exactly the
falling Vandermonde convolution evaluated at `α = −b`, `β = c + n − 1`, since
`α + β = c − b + n − 1` and `(c−b)_n = (c−b+n−1)^{≤n}`. The quotient form then
follows by clearing `(c)_n` via the split `(c)_n = (c)ᵢ · (c+i)_{n−i}`.
-/

open Finset Polynomial

namespace CombinationsFormulaOQ01OQ02

variable {R : Type*} [CommRing R]

/-! ## The descending-Pochhammer Vandermonde convolution (polynomial backbone) -/

/-- **Descending-Pochhammer Vandermonde convolution**, evaluated form over a
commutative ring:
`(α+β)^{\underline n} = ∑_{i+j=n} C(n,i) · α^{\underline i} · β^{\underline j}`. -/
theorem descPochhammer_eval_vandermonde (α β : R) (n : ℕ) :
    (descPochhammer R n).eval (α + β)
      = ∑ ij ∈ antidiagonal n,
          (n.choose ij.1 : R)
            * ((descPochhammer R ij.1).eval α * (descPochhammer R ij.2).eval β) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_mul
          (fun i j => (descPochhammer R i).eval α * (descPochhammer R j).eval β) n,
        descPochhammer_succ_eval, ih, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro ij hmem
    obtain ⟨i, j⟩ := ij
    have hij : i + j = n := Finset.mem_antidiagonal.mp hmem
    have hsum : (i : R) + (j : R) = (n : R) := by rw [← Nat.cast_add, hij]
    have hsymm : (n.choose j : R) = (n.choose i : R) := by
      have hji : n = j + i := by omega
      rw [Nat.choose_symm_of_eq_add hji]
    rw [descPochhammer_succ_eval, descPochhammer_succ_eval, hsymm, ← hsum]
    ring

/-! ## Rising / falling factorial bridge -/

/-- The rising factorial as a shifted falling factorial:
`(z)_m = (z + m − 1)^{\underline m}`. -/
theorem ascPochhammer_eval_eq_descPochhammer' (z : R) (m : ℕ) :
    (ascPochhammer R m).eval z = (descPochhammer R m).eval (z + m - 1) := by
  rw [descPochhammer_eval_eq_ascPochhammer]
  congr 1
  ring

/-- The signed rising factorial as a falling factorial at the negated base:
`(−1)ⁱ · (b)ᵢ = (−b)^{\underline i}`. -/
theorem neg_one_pow_mul_ascPochhammer_eval (b : R) (i : ℕ) :
    (-1) ^ i * (ascPochhammer R i).eval b = (descPochhammer R i).eval (-b) := by
  have h := ascPochhammer_eval_neg_eq_descPochhammer R (-b) i
  rw [neg_neg] at h
  rw [h, ← mul_assoc]
  have h2 : ((-1 : R)) ^ i * (-1) ^ i = 1 := by
    rw [← pow_add]; exact Even.neg_one_pow ⟨i, by ring⟩
  rw [h2, one_mul]

/-! ## The rising-factorial Vandermonde convolution -/

/-- **Rising-Pochhammer Vandermonde convolution**, evaluated form over a
commutative ring:
`(x+y)_n = ∑_{i+j=n} C(n,i) · (x)ᵢ · (y)ⱼ`.

This is the Chu–Vandermonde identity for rising factorials; the parent's
natural-number Vandermonde is its specialization at integer arguments. -/
theorem ascPochhammer_eval_vandermonde (x y : R) (n : ℕ) :
    (ascPochhammer R n).eval (x + y)
      = ∑ ij ∈ antidiagonal n,
          (n.choose ij.1 : R)
            * ((ascPochhammer R ij.1).eval x * (ascPochhammer R ij.2).eval y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_mul
          (fun i j => (ascPochhammer R i).eval x * (ascPochhammer R j).eval y) n,
        ascPochhammer_succ_eval, ih, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro ij hmem
    obtain ⟨i, j⟩ := ij
    have hij : i + j = n := Finset.mem_antidiagonal.mp hmem
    have hsum : (i : R) + (j : R) = (n : R) := by rw [← Nat.cast_add, hij]
    have hsymm : (n.choose j : R) = (n.choose i : R) := by
      have hji : n = j + i := by omega
      rw [Nat.choose_symm_of_eq_add hji]
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, hsymm, ← hsum]
    ring

/-! ## The terminating Gauss ₂F₁ summation (Chu–Vandermonde) -/

/-- **Terminating Gauss ₂F₁ summation, ring form** (Chu–Vandermonde).

For all `b c : R` and `n : ℕ`,
`∑_{i+j=n} (−1)ⁱ C(n,i) · (b)ᵢ · (c+i)ⱼ = (c − b)_n`.

This is `₂F₁(−n, b; c; 1) = (c−b)_n / (c)_n` with denominators cleared, hence
valid over an *arbitrary* commutative ring with no nonvanishing hypotheses.
Each summand collapses to a falling factorial with index-independent base
(`(−b)^{\underline i}` and `(c+n−1)^{\underline{\,j}}`), so the whole sum is the
descending Vandermonde convolution at `α = −b`, `β = c + n − 1`. -/
theorem gauss_terminating_ring (b c : R) (n : ℕ) :
    ∑ ij ∈ antidiagonal n,
        ((-1) ^ ij.1 * (n.choose ij.1 : R))
          * ((ascPochhammer R ij.1).eval b * (ascPochhammer R ij.2).eval (c + ij.1))
      = (ascPochhammer R n).eval (c - b) := by
  rw [ascPochhammer_eval_eq_descPochhammer' (c - b) n,
      show (c - b) + (n : R) - 1 = (-b) + (c + (n : R) - 1) by ring,
      descPochhammer_eval_vandermonde (-b) (c + (n : R) - 1) n]
  refine Finset.sum_congr rfl ?_
  intro ij hmem
  obtain ⟨i, j⟩ := ij
  have hij : i + j = n := Finset.mem_antidiagonal.mp hmem
  have hsum : (i : R) + (j : R) = (n : R) := by rw [← Nat.cast_add, hij]
  rw [ascPochhammer_eval_eq_descPochhammer' (c + (i : R)) j,
      show (c + (i : R)) + (j : R) - 1 = c + (n : R) - 1 by rw [← hsum]; ring,
      ← neg_one_pow_mul_ascPochhammer_eval b i]
  ring

/-- Multiplicative splitting of the rising factorial:
`(c)_{k+m} = (c)_k · (c+k)_m`. -/
theorem ascPochhammer_eval_split (c : R) (k m : ℕ) :
    (ascPochhammer R (k + m)).eval c
      = (ascPochhammer R k).eval c * (ascPochhammer R m).eval (c + k) := by
  rw [← ascPochhammer_mul, eval_mul, eval_comp, eval_add, eval_X, eval_natCast]

/-- **Terminating Gauss ₂F₁ summation, quotient form** over a field:

`∑_{i+j=n} (−1)ⁱ C(n,i) · (b)ᵢ / (c)ᵢ = (c − b)_n / (c)_n`,

i.e. `₂F₁(−n, b; c; 1) = (c − b)_n / (c)_n`, under the single nonvanishing
hypothesis `(c)_n ≠ 0` (which forces every `(c)ᵢ ≠ 0` for `i ≤ n`, since
`(c)ᵢ` divides `(c)_n`). This is the classical statement of Gauss's second
theorem; it follows from the ring form by clearing `(c)_n` and using the
split `(c)_n = (c)ᵢ · (c+i)_{n−i}`. -/
theorem gauss_terminating_field {K : Type*} [Field K] (b c : K) (n : ℕ)
    (hc : (ascPochhammer K n).eval c ≠ 0) :
    ∑ ij ∈ antidiagonal n,
        ((-1) ^ ij.1 * (n.choose ij.1 : K))
          * ((ascPochhammer K ij.1).eval b / (ascPochhammer K ij.1).eval c)
      = (ascPochhammer K n).eval (c - b) / (ascPochhammer K n).eval c := by
  rw [eq_div_iff hc, Finset.sum_mul, ← gauss_terminating_ring b c n]
  refine Finset.sum_congr rfl ?_
  intro ij hmem
  obtain ⟨i, j⟩ := ij
  have hij : i + j = n := Finset.mem_antidiagonal.mp hmem
  have hsplit : (ascPochhammer K n).eval c
      = (ascPochhammer K i).eval c * (ascPochhammer K j).eval (c + i) := by
    rw [← hij]; exact ascPochhammer_eval_split c i j
  have hci : (ascPochhammer K i).eval c ≠ 0 := by
    intro h; apply hc; rw [hsplit, h, zero_mul]
  rw [hsplit]
  field_simp

end CombinationsFormulaOQ01OQ02
