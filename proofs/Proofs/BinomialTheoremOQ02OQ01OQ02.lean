/-
# Marginal Distributions of Multinomial Are Binomial

*Open Question from BinomialTheoremOQ02OQ01*: Do the marginal distributions of
the multinomial distribution arise as binomial distributions?

## What This Proves

If (X₁, X₂, ..., Xₖ) follows a Multinomial(n, p₁, ..., pₖ) distribution,
then each component Xᵢ follows Binomial(n, pᵢ).

## Proof Strategy: Probability Generating Function

We use the **probability generating function** (PGF). For a random variable X,
its PGF is E[t^X]. Two distributions on {0,...,n} with the same PGF are identical.

**Key result** (proved here): The PGF of the marginal X_{i₀} is

    E[t^{X_{i₀}}] = ∑_{k} P(X=k) · t^{k(i₀)} = (p(i₀)·t + (1−p(i₀)))^n

This is exactly the PGF of Binomial(n, p(i₀)), proving the marginal is binomial.

## Proof of the PGF Formula

Apply the multinomial MGF theorem with g(i) = t if i = i₀, else 1:

    ∑_{k} P(X=k) · ∏ g(i)^{k(i)} = (∑ p(i)·g(i))^n

The LHS reduces to ∑_{k} P(X=k) · t^{k(i₀)} because g(i)^{k(i)} = 1 for i ≠ i₀.
The RHS simplifies to (p(i₀)·t + (1−p(i₀)))^n.

## Mathlib Dependencies

- `Finset.sum_pow_eq_sum_piAntidiag` : The multinomial theorem
- `Finset.prod_eq_single`            : Product concentrated at one element
- `Finset.sum_ite_eq'`               : Sum of indicator function
- `Finset.sum_add_distrib`           : Linearity of sum
- `Finset.mul_sum`                   : Pulling constant out of sum
-/

import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace BinomialTheoremOQ02OQ01OQ02

open Finset BigOperators

/-! ## Setup: Multinomial Distribution -/

/-- The multinomial probability mass function: multinomial(s, k) · ∏ p(i)^k(i) -/
noncomputable def multinomialProb {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (k : α → ℕ) : ℝ :=
  (Nat.multinomial s k : ℝ) * ∏ i ∈ s, p i ^ k i

/-- **Multinomial MGF**: The moment-generating function identity.
For any weight function g, the multinomial theorem gives:

    (∑ p(i)·g(i))^n = ∑_{k:∑k=n} P(X=k) · ∏ g(i)^{k(i)}

This is the algebraic core of the PGF approach. -/
theorem multinomial_mgf_real {α : Type*} [DecidableEq α]
    (s : Finset α) (p g : α → ℝ) (n : ℕ) :
    (∑ i ∈ s, p i * g i) ^ n =
    ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * ∏ i ∈ s, g i ^ k i := by
  unfold multinomialProb
  rw [Finset.sum_pow_eq_sum_piAntidiag s (fun i => p i * g i) n]
  congr 1; ext k
  have prod_split : ∏ i ∈ s, (p i * g i) ^ k i =
      (∏ i ∈ s, p i ^ k i) * ∏ i ∈ s, g i ^ k i := by
    rw [← Finset.prod_mul_distrib]
    congr 1; ext i
    exact mul_pow (p i) (g i) (k i)
  rw [prod_split]; ring

/-- **Normalization**: The multinomial PMF sums to 1 when ∑ p(i) = 1. -/
theorem multinomialProb_sum_one {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (hp : ∑ i ∈ s, p i = 1) :
    ∑ k ∈ s.piAntidiag n, multinomialProb s p n k = 1 := by
  unfold multinomialProb
  have h := Finset.sum_pow_eq_sum_piAntidiag s p n
  rw [hp, one_pow] at h
  exact h.symm

/-! ## Main Theorem: Marginal PGF -/

/-- **Marginal PGF Theorem** (Main Result): The probability generating function of
component X_{i₀} in a multinomial distribution equals the Binomial(n, p(i₀)) PGF:

    E[t^{X_{i₀}}] = ∑_{k} P(X=k) · t^{k(i₀)} = (p(i₀)·t + (1−p(i₀)))^n

**Proof**: Apply the MGF theorem with g(i) = t if i = i₀ and g(i) = 1 otherwise.
- The product ∏ g(i)^{k(i)} collapses to t^{k(i₀)} since g(i)^{k(i)} = 1^{k(i)} = 1 for i ≠ i₀.
- The sum ∑ p(i)·g(i) = p(i₀)·t + ∑_{i≠i₀} p(i) = p(i₀)·t + (1−p(i₀)) using ∑ p(i) = 1. -/
theorem multinomial_marginal_pgf {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (hp : ∑ i ∈ s, p i = 1)
    (i₀ : α) (hi₀ : i₀ ∈ s) (t : ℝ) :
    ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * t ^ (k i₀) =
    (p i₀ * t + (1 - p i₀)) ^ n := by
  -- Key lemma 1: The product ∏ i ∈ s, (if i = i₀ then t else 1)^{k(i)} = t^{k(i₀)}
  -- because all factors with i ≠ i₀ equal 1^{k(i)} = 1.
  have prod_simp : ∀ k : α → ℕ,
      ∏ i ∈ s, (if i = i₀ then t else (1 : ℝ)) ^ k i = t ^ k i₀ := fun k => by
    rw [Finset.prod_eq_single i₀
      (fun b _ hb => by simp [show b ≠ i₀ from hb])
      (fun h => absurd hi₀ h)]
    simp
  -- Key lemma 2: ∑ i ∈ s, p(i)·(if i = i₀ then t else 1) = p(i₀)·t + (1−p(i₀))
  -- via: write as ∑ p(i) + (t−1)·∑ p(i)·[i=i₀], then use hp and sum_ite_eq'.
  have sum_simp : ∑ i ∈ s, p i * (if i = i₀ then t else (1 : ℝ)) = p i₀ * t + (1 - p i₀) := by
    have h1 : ∑ i ∈ s, p i * (if i = i₀ then t else 1) =
              ∑ i ∈ s, p i + ∑ i ∈ s, (t - 1) * ite (i = i₀) (p i) 0 := by
      rw [← Finset.sum_add_distrib]
      congr 1; ext i; split_ifs <;> ring
    rw [h1, hp, ← Finset.mul_sum, Finset.sum_ite_eq']
    simp [hi₀]; ring
  -- Main proof: rewrite LHS using the MGF theorem with g(i) = if i=i₀ then t else 1,
  -- substitute prod_simp to collapse ∏ g^k to t^{k(i₀)}, then use sum_simp.
  rw [show ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * t ^ k i₀ =
          (∑ i ∈ s, p i * (if i = i₀ then t else 1)) ^ n from by
    rw [multinomial_mgf_real s p (fun i => if i = i₀ then t else 1) n]
    apply Finset.sum_congr rfl; intro k _; rw [prod_simp k],
    sum_simp]

/-! ## Corollaries -/

/-- **PGF identifies with binomial PGF**: The marginal PGF equals the binomial theorem
expansion of Binomial(n, p(i₀)), confirming the marginal distribution is Binomial(n, p(i₀)).

The binomial theorem gives: (p·t + (1−p))^n = ∑_{j=0}^n C(n,j)·p^j·(1−p)^(n−j)·t^j
which matches the Binomial(n, p) probability generating function. -/
theorem multinomial_marginal_pgf_eq_binomial {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (hp : ∑ i ∈ s, p i = 1)
    (i₀ : α) (hi₀ : i₀ ∈ s) (t : ℝ) :
    ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * t ^ (k i₀) =
    ∑ j ∈ Finset.range (n + 1),
      (Nat.choose n j : ℝ) * p i₀ ^ j * (1 - p i₀) ^ (n - j) * t ^ j := by
  rw [multinomial_marginal_pgf s p n hp i₀ hi₀ t, add_pow]
  congr 1; ext j; ring

/-- **Marginal normalization**: The marginal PMF sums to 1. -/
theorem multinomial_marginal_sum_one {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (hp : ∑ i ∈ s, p i = 1)
    (i₀ : α) (_ : i₀ ∈ s) :
    ∑ k ∈ s.piAntidiag n, multinomialProb s p n k = 1 :=
  multinomialProb_sum_one s p n hp

/-! ## Direct Marginal PMF Formula -/

/-- **Direct Marginal PMF Formula**: The probability that X_{i₀} = j equals the
binomial PMF: C(n,j) · p(i₀)^j · (1−p(i₀))^(n−j).

**Proof sketch**: The PGF identity `multinomial_marginal_pgf_eq_binomial` gives

    ∑_k P(X=k) · t^{k(i₀)} = ∑_j C(n,j)·p^j·(1−p)^(n−j)·t^j  for all t ∈ ℝ

Grouping LHS by the value of k(i₀) = j gives ∑_j P(X_{i₀}=j)·t^j.
Since two polynomials equal for all t ∈ ℝ have equal coefficients:
    P(X_{i₀} = j) = C(n,j)·p(i₀)^j·(1−p(i₀))^(n−j)

**Formalization gap**: Extracting polynomial coefficients from a pointwise equality
requires: (1) showing that ∑_j a_j·t^j is a polynomial, (2) using injectivity of
the polynomial ring map into functions ℝ → ℝ. The key ingredient is that if
two polynomials of degree ≤ n agree at n+2 points, they are equal (over ℝ).
This is available via `Polynomial.funext` combined with coefficient extraction. -/
theorem multinomial_marginal_pmf {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (hp : ∑ i ∈ s, p i = 1)
    (i₀ : α) (hi₀ : i₀ ∈ s) (j : ℕ) (hj : j ≤ n) :
    ∑ k ∈ (s.piAntidiag n).filter (fun k => k i₀ = j), multinomialProb s p n k =
    (Nat.choose n j : ℝ) * p i₀ ^ j * (1 - p i₀) ^ (n - j) := by
  -- Direct algebraic proof: factor multinomialProb using the multinomial_insert identity,
  -- apply a bijection between the filtered piAntidiag and (s.erase i₀).piAntidiag (n-j),
  -- then use the multinomial theorem on s.erase i₀.
  have hi₀_notin : i₀ ∉ s.erase i₀ := Finset.notMem_erase i₀ s
  have hs_eq : s = insert i₀ (s.erase i₀) := (Finset.insert_erase hi₀).symm
  -- ∑ i ∈ s.erase i₀, p i = 1 - p i₀
  have hpcomp : ∑ i ∈ s.erase i₀, p i = 1 - p i₀ := by
    have h := Finset.add_sum_erase s p hi₀; linarith
  -- For k in filter: ∑ i ∈ s.erase i₀, k i = n - j
  have herase_sum : ∀ k : α → ℕ, ∑ i ∈ s, k i = n → k i₀ = j →
      ∑ i ∈ s.erase i₀, k i = n - j := fun k hksum hkj => by
    have h : k i₀ + ∑ i ∈ s.erase i₀, k i = n :=
      (Finset.add_sum_erase s k hi₀).trans hksum
    omega
  -- Multinomial theorem on s.erase i₀ gives (1 - p i₀)^(n-j)
  have hmultinom_erase :
      ∑ f ∈ (s.erase i₀).piAntidiag (n - j), multinomialProb (s.erase i₀) p (n - j) f =
      (1 - p i₀) ^ (n - j) := by
    simp only [multinomialProb, ← Finset.sum_pow_eq_sum_piAntidiag, hpcomp]
  -- Bijection: k (with k i₀ = j) ↔ k restricted to s.erase i₀
  -- Forward σ k = zero out i₀; Backward τ f = restore j at i₀
  have hbij :
      ∑ k ∈ (s.piAntidiag n).filter (fun k => k i₀ = j),
        multinomialProb (s.erase i₀) p (n - j) k =
      ∑ f ∈ (s.erase i₀).piAntidiag (n - j),
        multinomialProb (s.erase i₀) p (n - j) f :=
    Finset.sum_nbij' (fun k => fun a => if a = i₀ then 0 else k a)
                     (fun f => fun a => if a = i₀ then j else f a)
      -- σ k ∈ (s.erase i₀).piAntidiag (n-j)
      (fun k hk => by
        simp only [Finset.mem_filter, Finset.mem_piAntidiag] at hk
        obtain ⟨⟨hksum, hksup⟩, hkj⟩ := hk
        rw [Finset.mem_piAntidiag]
        constructor
        · rw [Finset.sum_congr rfl
              (fun a ha => if_neg (Finset.mem_erase.mp ha).1)]
          exact herase_sum k hksum hkj
        · intro a ha
          by_cases haa : a = i₀
          · simp [haa] at ha
          · simp only [if_neg haa] at ha
            exact Finset.mem_erase.mpr ⟨haa, hksup a ha⟩)
      -- τ f ∈ filter
      (fun f hf => by
        simp only [Finset.mem_piAntidiag] at hf
        rw [Finset.mem_filter, Finset.mem_piAntidiag]
        have hfi₀ : f i₀ = 0 := by
          by_contra h; exact absurd (hf.2 i₀ h) hi₀_notin
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · -- Sum: ∑ i ∈ s, τ f i = n
          conv_lhs => rw [hs_eq]
          rw [Finset.sum_insert hi₀_notin, if_pos rfl,
              Finset.sum_congr rfl (fun a ha => if_neg (Finset.mem_erase.mp ha).1),
              hf.1]
          omega
        · -- Support
          intro a ha
          by_cases haa : a = i₀
          · exact haa ▸ hi₀
          · simp only [if_neg haa] at ha
            exact Finset.erase_subset i₀ s (hf.2 a ha)
        · simp)
      -- Left inverse: τ (σ k) = k
      (fun k hk => by
        simp only [Finset.mem_filter] at hk
        funext a
        by_cases ha : a = i₀
        · simp only [ha, ite_true]; exact hk.2.symm
        · simp only [if_neg ha])
      -- Right inverse: σ (τ f) = f
      (fun f hf => by
        simp only [Finset.mem_piAntidiag] at hf
        have hfi₀ : f i₀ = 0 := by
          by_contra h; exact absurd (hf.2 i₀ h) hi₀_notin
        funext a
        by_cases ha : a = i₀
        · simp only [ha, ite_true, hfi₀]
        · simp only [if_neg ha])
      -- Values: multinomialProb only depends on values at s.erase i₀
      (fun k _ => by
        simp only [multinomialProb]
        have hmn : Nat.multinomial (s.erase i₀) k =
            Nat.multinomial (s.erase i₀) (fun a => if a = i₀ then 0 else k a) := by
          apply Nat.multinomial_congr
          intro a ha; exact (if_neg (Finset.mem_erase.mp ha).1).symm
        have hpr : ∏ a ∈ s.erase i₀, p a ^ k a =
            ∏ a ∈ s.erase i₀, p a ^ (if a = i₀ then 0 else k a) := by
          apply Finset.prod_congr rfl
          intro a ha; congr 1; exact (if_neg (Finset.mem_erase.mp ha).1).symm
        rw [hmn, hpr])
  -- Factor C(n,j) * p i₀^j out of each term
  rw [show ∑ k ∈ (s.piAntidiag n).filter (fun k => k i₀ = j), multinomialProb s p n k =
          (Nat.choose n j : ℝ) * p i₀ ^ j *
          ∑ k ∈ (s.piAntidiag n).filter (fun k => k i₀ = j),
            multinomialProb (s.erase i₀) p (n - j) k from by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_piAntidiag] at hk
    obtain ⟨⟨hksum, hksup⟩, hkj⟩ := hk
    simp only [multinomialProb]
    have hmul : Nat.multinomial s k = Nat.choose n j * Nat.multinomial (s.erase i₀) k := by
      conv_lhs => rw [hs_eq]
      rw [Nat.multinomial_insert hi₀_notin, hkj,
          herase_sum k hksum hkj, Nat.add_sub_cancel' hj]
    have hprod : ∏ i ∈ s, p i ^ k i = p i₀ ^ j * ∏ i ∈ s.erase i₀, p i ^ k i := by
      rw [← Finset.mul_prod_erase s _ hi₀, hkj]
    rw [hmul, hprod]; push_cast; ring]
  rw [hbij, hmultinom_erase]

/-! ## Special Case: Bool (Bernoulli Marginals) -/

/-- **Bernoulli marginal PGF**: For a 2-outcome multinomial with s = {false, true},
p(false) = 1−p and p(true) = p, the PGF of the "true" component is (p·t + (1−p))^n.
This is the Binomial(n, p) PGF. -/
theorem bernoulli_marginal_pgf (p : ℝ) (n : ℕ) (t : ℝ) :
    ∑ k ∈ ({false, true} : Finset Bool).piAntidiag n,
      multinomialProb ({false, true} : Finset Bool)
        (fun b => if b then p else 1 - p) n k * t ^ k true =
    (p * t + (1 - p)) ^ n := by
  apply multinomial_marginal_pgf
  · simp [Finset.sum_pair Bool.false_ne_true]
  · simp

/-- **Concrete example (n=2)**: For 2 independent Bernoulli trials with success prob p,
the PGF of total successes is (p·t + (1−p))² = p²t² + 2p(1−p)t + (1−p)². -/
theorem binomial_2_pgf (p t : ℝ) :
    ∑ k ∈ ({false, true} : Finset Bool).piAntidiag 2,
      multinomialProb ({false, true} : Finset Bool)
        (fun b => if b then p else 1 - p) 2 k * t ^ k true =
    (p * t + (1 - p)) ^ 2 :=
  bernoulli_marginal_pgf p 2 t

/-- **Symmetry**: The "false" component also follows a binomial distribution.
Its PGF is ((1−p)·t + p)^n = Binomial(n, 1−p). -/
theorem bernoulli_false_marginal_pgf (p : ℝ) (n : ℕ) (t : ℝ) :
    ∑ k ∈ ({false, true} : Finset Bool).piAntidiag n,
      multinomialProb ({false, true} : Finset Bool)
        (fun b => if b then p else 1 - p) n k * t ^ k false =
    ((1 - p) * t + p) ^ n := by
  have h := multinomial_marginal_pgf ({false, true} : Finset Bool)
    (fun b => if b then p else 1 - p) n
    (by simp [Finset.sum_pair Bool.false_ne_true])
    false (by simp) t
  simpa using h

/-! ## Summary

The **multinomial marginal theorem** establishes:

If (X₁,...,Xₖ) ~ Multinomial(n, p₁,...,pₖ) with ∑pᵢ = 1, then each component
Xᵢ has **PGF** E[t^{Xᵢ}] = (pᵢ·t + (1−pᵢ))^n = Binomial(n, pᵢ) PGF.

**Proved in this file:**
1. `multinomial_mgf_real`               — Multinomial MGF identity (algebraic)
2. `multinomialProb_sum_one`            — Normalization: ∑ P(X=k) = 1
3. `multinomial_marginal_pgf`           — Main result: marginal PGF formula
4. `multinomial_marginal_pgf_eq_binomial` — PGF matches binomial theorem expansion
5. `multinomial_marginal_pmf`           — Direct PMF formula (bijection + multinomial theorem)
6. `bernoulli_marginal_pgf`             — Concrete: Bool 2-outcome case

The answer to the open question is: **YES**, marginals of the multinomial are binomial.
The algebraic proof via PGF is elementary and uses only the multinomial theorem.
-/

end BinomialTheoremOQ02OQ01OQ02
