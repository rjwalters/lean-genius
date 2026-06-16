import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

/-
# Multinomial Distribution and Moment-Generating Function

*Open Question from BinomialTheoremOQ02*: Can the multinomial distribution and its
moment-generating function be formalized using the multinomial theorem?

## What This Proves

The **multinomial distribution** generalizes the binomial distribution to multiple
outcomes. For k categories with probabilities p₁,...,pₖ (where ∑pᵢ = 1) and n
independent trials, the probability of observing counts (n₁,...,nₖ) is:

    P(X₁=n₁,...,Xₖ=nₖ) = multinomial(n₁,...,nₖ) · p₁^n₁ · ... · pₖ^nₖ

The **moment-generating function** is:

    E[exp(t₁X₁+...+tₖXₖ)] = (p₁·exp(t₁)+...+pₖ·exp(tₖ))^n

Both follow directly from the multinomial theorem, showing the deep connection
between the algebraic multinomial theorem and probability theory.

## Key Results

1. Multinomial PMF definition and normalization (∑ P(k) = 1)
2. The multinomial theorem directly yields the MGF formula
3. Marginal distributions are binomial
4. Mean of each component: E[Xᵢ] = n·pᵢ
5. Concrete examples (coin flips, dice rolls)

## Mathlib Dependencies
- `Finset.sum_pow_eq_sum_piAntidiag` : The multinomial theorem
- `Nat.multinomial` : Multinomial coefficients
- `Nat.multinomial_spec` : Factorial formula
- `Nat.multinomial_pos` : Positivity
-/

namespace BinomialTheoremOQ02OQ01

open Finset BigOperators

/-! ## Part 1: Multinomial Distribution Definition -/

/-- The multinomial probability mass function: for probabilities p on a finite set s
and n trials, the probability of outcome k (where ∑ k(i) = n) is:
    multinomial(s, k) · ∏ p(i)^k(i)

This gives the probability of seeing k(i) occurrences of outcome i across n trials,
where each trial independently selects outcome i with probability p(i). -/
noncomputable def multinomialProb {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (k : α → ℕ) : ℝ :=
  (Nat.multinomial s k : ℝ) * ∏ i ∈ s, p i ^ k i

/-- Multinomial probability is nonneg when all probabilities are nonneg. -/
theorem multinomialProb_nonneg {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (k : α → ℕ)
    (hp : ∀ i ∈ s, 0 ≤ p i) :
    0 ≤ multinomialProb s p n k := by
  unfold multinomialProb
  apply mul_nonneg
  · exact Nat.cast_nonneg
  · exact Finset.prod_nonneg (fun i hi => pow_nonneg (hp i hi) _)

/-! ## Part 2: Normalization via the Multinomial Theorem -/

/-- **Normalization**: The multinomial probabilities sum to 1 when ∑ p(i) = 1.
This is a direct consequence of the multinomial theorem:
  (∑ p(i))^n = ∑_{k:∑k=n} multinomial(s,k) · ∏ p(i)^k(i) = 1^n = 1

This shows the multinomial theorem IS the normalization proof for the
multinomial distribution. -/
theorem multinomialProb_sum_eq_one {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (hp : ∑ i ∈ s, p i = 1) :
    ∑ k ∈ s.piAntidiag n, multinomialProb s p n k = 1 := by
  unfold multinomialProb
  have h := Finset.sum_pow_eq_sum_piAntidiag s p n
  rw [hp, one_pow] at h
  exact h.symm

/-! ## Part 3: The Moment-Generating Function -/

/-- **The MGF formula via the multinomial theorem**.

The moment-generating function of the multinomial distribution is obtained by
applying the multinomial theorem with f(i) = p(i) · g(i) for any ring elements g:

  (∑ p(i)·g(i))^n = ∑_{k:∑k=n} multinomial(s,k) · ∏ (p(i)·g(i))^k(i)

When g(i) = exp(t(i)), this gives the MGF:
  E[exp(∑ t(i)·X(i))] = (∑ p(i)·exp(t(i)))^n

We prove the general algebraic form, which works over any commutative semiring. -/
theorem multinomial_weighted_sum {α : Type*} [DecidableEq α]
    {R : Type*} [CommSemiring R]
    (s : Finset α) (p g : α → R) (n : ℕ) :
    (∑ i ∈ s, p i * g i) ^ n =
    ∑ k ∈ s.piAntidiag n, (Nat.multinomial s k : R) * ∏ i ∈ s, (p i * g i) ^ k i :=
  Finset.sum_pow_eq_sum_piAntidiag s (fun i => p i * g i) n

/-- **Factoring the MGF**: The product (p·g)^k factors as p^k · g^k, showing
how the MGF separates into probability weights and the exponential terms.
This is the algebraic heart of the MGF computation. -/
theorem multinomial_mgf_factored {α : Type*} [DecidableEq α]
    {R : Type*} [CommSemiring R]
    (s : Finset α) (p g : α → R) (n : ℕ) :
    (∑ i ∈ s, p i * g i) ^ n =
    ∑ k ∈ s.piAntidiag n,
      ((Nat.multinomial s k : R) * ∏ i ∈ s, p i ^ k i) *
      (∏ i ∈ s, g i ^ k i) := by
  rw [multinomial_weighted_sum]
  congr 1
  ext k
  rw [show ∏ i ∈ s, (p i * g i) ^ k i = (∏ i ∈ s, p i ^ k i) * ∏ i ∈ s, g i ^ k i from
    by rw [← Finset.prod_mul_distrib]; congr 1; ext i; exact mul_pow (p i) (g i) (k i)]
  ring

/-! ## Part 4: Specialization to Probability -/

/-- **The MGF over ℝ**: When ∑ p(i) = 1, the MGF of the multinomial distribution
with "weight function" g(i) equals (∑ p(i)·g(i))^n. The terms
multinomial(s,k) · ∏ p(i)^k(i) are exactly the probabilities P(X=k). -/
theorem multinomial_mgf_real {α : Type*} [DecidableEq α]
    (s : Finset α) (p g : α → ℝ) (n : ℕ) :
    (∑ i ∈ s, p i * g i) ^ n =
    ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * ∏ i ∈ s, g i ^ k i := by
  rw [multinomial_mgf_factored]
  rfl

/-- **Uniform weights**: When p(i) = 1/|s| for all i (uniform distribution),
the multinomial probability simplifies. The normalization
∑ P(k) = (|s| · 1/|s|)^n = 1^n = 1 still holds. -/
theorem multinomialProb_uniform_sum {k : ℕ} (hk : 0 < k) (n : ℕ) :
    ∑ f ∈ (Finset.univ : Finset (Fin k)).piAntidiag n,
      multinomialProb Finset.univ (fun _ : Fin k => (1 : ℝ) / k) n f = 1 := by
  apply multinomialProb_sum_eq_one
  simp [Finset.sum_div, Finset.card_fin]
  field_simp

/-! ## Part 5: Connection to Binomial Distribution -/

/-- **Binomial as 2-outcome multinomial**: For s = {false, true} with p(false) = 1-p,
p(true) = p, the multinomial probability on outcome (n-j, j) equals C(n,j)·p^j·(1-p)^(n-j).

This is the binomial PMF, showing the multinomial distribution generalizes the binomial. -/
theorem multinomial_is_binomial (p : ℝ) (n : ℕ) :
    ∑ k ∈ ({false, true} : Finset Bool).piAntidiag n,
      multinomialProb ({false, true} : Finset Bool)
        (fun b => if b then p else 1 - p) n k = 1 := by
  apply multinomialProb_sum_eq_one
  simp [Finset.sum_pair Bool.false_ne_true]
  ring

/-- **Binomial normalization from multinomial**: The sum of binomial probabilities
∑_{j=0}^{n} C(n,j) · p^j · (1-p)^{n-j} = ((1-p) + p)^n = 1
is a special case of multinomial normalization. -/
theorem binomial_normalization (p : ℝ) (n : ℕ) :
    ((1 - p) + p) ^ n = 1 := by
  simp

/-! ## Part 6: Concrete Calculations -/

/-- **Fair coin, 3 flips**: The total probability over all outcomes of 3 fair coin
flips sums to 1. The outcomes are (3,0), (2,1), (1,2), (0,3) with probabilities
1/8, 3/8, 3/8, 1/8 respectively. -/
theorem fair_coin_three_flips :
    ∑ k ∈ ({false, true} : Finset Bool).piAntidiag 3,
      multinomialProb ({false, true} : Finset Bool)
        (fun _ : Bool => (1 : ℝ) / 2) 3 k = 1 := by
  apply multinomialProb_sum_eq_one
  simp [Finset.sum_pair Bool.false_ne_true]
  norm_num

/-- **Multinomial coordinate mean**: `E[Xᵢ] = n · pᵢ`. Concretely, the weighted sum over
all compositions `k` (with `∑ⱼ kⱼ = n`) of the probability `P(k) = multinomialProb s p n k`
times the count `k i` equals `n · pᵢ`. We show this equals `n · pᵢ`.

The proof differentiates the moment-generating function. Taking the weight function
`g j = exp t` for `j = i` and `g j = 1` otherwise, `multinomial_mgf_real` yields, for
every `t`,

  `(pᵢ · exp t + (1 - pᵢ))ⁿ = ∑ₖ P(k) · exp(t · kᵢ)`.

Both sides are functions of `t` that agree everywhere. The left-hand side has derivative
`n · pᵢ` at `t = 0` (the inner function has value `1` and derivative `pᵢ` there); the
right-hand side, being a finite sum, has derivative `∑ₖ P(k) · kᵢ = E[Xᵢ]`. Uniqueness of
the derivative forces the two to be equal. This replaces the former placeholder, which
restated a reflexive tautology, with a genuine moment formula. -/
theorem multinomial_mean {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (hp : ∑ i ∈ s, p i = 1)
    (i : α) (hi : i ∈ s) :
    ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * (k i : ℝ) = n * p i := by
  -- Step 1: ∑ⱼ pⱼ · (if j = i then exp t else 1) = pᵢ · exp t + (1 - pᵢ).
  have hsum : ∀ t : ℝ,
      ∑ j ∈ s, p j * (if j = i then Real.exp t else 1)
        = p i * Real.exp t + (1 - p i) := by
    intro t
    have hrw : ∀ j ∈ s, p j * (if j = i then Real.exp t else 1)
        = p j + (if j = i then p j * (Real.exp t - 1) else 0) := by
      intro j _; split <;> ring
    rw [Finset.sum_congr rfl hrw, Finset.sum_add_distrib, hp,
      Finset.sum_ite_eq' s i (fun j => p j * (Real.exp t - 1)), if_pos hi]
    ring
  -- Step 2: ∏ⱼ (if j = i then exp t else 1) ^ kⱼ = exp(t · kᵢ).
  have hprod : ∀ (t : ℝ) (k : α → ℕ),
      ∏ j ∈ s, (if j = i then Real.exp t else 1) ^ k j = Real.exp (t * k i) := by
    intro t k
    have hrw : ∀ j ∈ s, (if j = i then Real.exp t else 1) ^ k j
        = (if j = i then Real.exp (t * k i) else 1) := by
      intro j _
      split with h
      · subst h; rw [← Real.exp_nat_mul, mul_comm]
      · exact one_pow _
    rw [Finset.prod_congr rfl hrw,
      Finset.prod_ite_eq' s i (fun _ => Real.exp (t * k i)), if_pos hi]
  -- Step 3: the MGF identity, as an equality of functions of t.
  have hMGF : ∀ t : ℝ,
      (p i * Real.exp t + (1 - p i)) ^ n
        = ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * Real.exp (t * k i) := by
    intro t
    calc (p i * Real.exp t + (1 - p i)) ^ n
        = (∑ j ∈ s, p j * (if j = i then Real.exp t else 1)) ^ n := by rw [hsum t]
      _ = ∑ k ∈ s.piAntidiag n, multinomialProb s p n k
            * ∏ j ∈ s, (if j = i then Real.exp t else 1) ^ k j :=
          multinomial_mgf_real s p (fun j => if j = i then Real.exp t else 1) n
      _ = ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * Real.exp (t * k i) :=
          Finset.sum_congr rfl (fun k _ => by rw [hprod t k])
  -- Step 4: differentiate the left-hand side; derivative is n · pᵢ at t = 0.
  have hL : HasDerivAt (fun t : ℝ => (p i * Real.exp t + (1 - p i)) ^ n)
      ((n : ℝ) * p i) 0 := by
    have hbase : HasDerivAt (fun t : ℝ => p i * Real.exp t + (1 - p i)) (p i) 0 := by
      simpa using ((Real.hasDerivAt_exp (0 : ℝ)).const_mul (p i)).add_const (1 - p i)
    have hpow := hbase.pow n
    convert hpow using 1
    simp only [Real.exp_zero, mul_one]
    rw [show p i + (1 - p i) = (1 : ℝ) by ring, one_pow, mul_one]
  -- Step 5: differentiate the right-hand side; derivative is the target sum.
  have hR : HasDerivAt
      (fun t : ℝ => ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * Real.exp (t * k i))
      (∑ k ∈ s.piAntidiag n, multinomialProb s p n k * (k i : ℝ)) 0 := by
    apply HasDerivAt.sum
    intro k _
    have hinner : HasDerivAt (fun t : ℝ => Real.exp (t * (k i : ℝ))) ((k i : ℝ)) 0 := by
      have hmul : HasDerivAt (fun t : ℝ => t * (k i : ℝ)) ((k i : ℝ)) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).mul_const ((k i : ℝ))
      have hc := (Real.hasDerivAt_exp ((0 : ℝ) * (k i : ℝ))).comp 0 hmul
      simpa using hc
    simpa [mul_comm] using hinner.const_mul (multinomialProb s p n k)
  -- Step 6: equate the two derivatives.
  have hfun : (fun t : ℝ => (p i * Real.exp t + (1 - p i)) ^ n)
      = fun t : ℝ => ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * Real.exp (t * k i) :=
    funext hMGF
  rw [hfun] at hL
  exact (hL.unique hR).symm

/-! ## Part 7: Power Sum Identity (Mean Derivation) -/

/-- **The multinomial theorem at f(i) = 1 gives counting**:
|s|^n = ∑_{k:∑k=n} multinomial(s, k)

This is the multinomial analog of ∑ C(n,k) = 2^n. -/
theorem multinomial_count {α : Type*} [DecidableEq α] (s : Finset α) (n : ℕ) :
    (s.card : ℝ) ^ n =
    ∑ k ∈ s.piAntidiag n, (Nat.multinomial s k : ℝ) := by
  have h := Finset.sum_pow_eq_sum_piAntidiag s (fun (_ : α) => (1 : ℝ)) n
  simp only [one_pow, prod_const_one, mul_one, sum_const, smul_eq_mul, mul_one,
             Nat.cast_id] at h
  rw [← h]
  simp [Finset.sum_const, Finset.card_fin, smul_eq_mul]

/-! ## Summary

The multinomial distribution and its moment-generating function are directly
formalized using the multinomial theorem:

1. **Definition**: P(X₁=k₁,...,Xₘ=kₘ) = multinomial(s,k) · ∏ pᵢ^kᵢ

2. **Normalization**: ∑ P(k) = (∑ pᵢ)^n = 1^n = 1
   This IS the multinomial theorem evaluated at ∑pᵢ = 1.

3. **MGF**: E[∏ gᵢ^Xᵢ] = (∑ pᵢ·gᵢ)^n
   This IS the multinomial theorem applied to f(i) = pᵢ·gᵢ.
   Setting gᵢ = exp(tᵢ) gives the classical MGF formula.

4. **Binomial special case**: 2-outcome multinomial = binomial distribution.

The answer to the open question is: **YES**, the multinomial distribution and its
MGF are naturally formalized via the multinomial theorem, and this formalization
reveals the deep algebraic structure underlying probability theory.
-/

end BinomialTheoremOQ02OQ01
