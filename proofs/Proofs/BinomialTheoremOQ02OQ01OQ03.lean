import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Proofs.BinomialTheoremOQ02OQ01OQ02
import Proofs.BinomialTheoremOQ03

/-
# Multinomial Covariance: Cov(Xᵢ, Xⱼ) = -n·pᵢ·pⱼ

*Open Question from BinomialTheoremOQ02OQ01*: Can we formalize the covariance
structure of the multinomial distribution?

## Answer

YES. We prove Cov(Xᵢ, Xⱼ) = -n·pᵢ·pⱼ for distinct outcomes i ≠ j in a
multinomial distribution with n trials and probabilities (p₁,...,pₖ) with ∑pᵢ = 1.

## Mathematical Structure

For (X₁,...,Xₖ) ~ Multinomial(n, p₁,...,pₖ):

  Cov(Xᵢ, Xⱼ) = E[XᵢXⱼ] - E[Xᵢ]·E[Xⱼ]
               = n(n-1)pᵢpⱼ − n²pᵢpⱼ
               = -n·pᵢ·pⱼ

## Why the Covariance is Negative

The counts Xᵢ and Xⱼ are negatively correlated because the n outcomes are a fixed
total: more of outcome i necessarily means less of outcome j.

## Proof Strategy

1. **E[Xᵢ] = n·pᵢ**: Proved via fiber grouping over values of k(i), using the
   marginal PMF P(Xᵢ = j) = C(n,j)·pᵢʲ·(1-pᵢ)^(n-j) from BinomialTheoremOQ02OQ01OQ02
   and the binomial mean E[Bin(n,p)] = np from BinomialTheoremOQ03.

2. **E[XᵢXⱼ] = n(n-1)·pᵢ·pⱼ** (sorry): Apply multinomial MGF theorem with
   g(l) = 1+a if l=i, 1+b if l=j, 1 otherwise. This gives:
     ∑_k P(k)·(1+a)^{k(i)}·(1+b)^{k(j)} = (1 + pᵢa + pⱼb)^n
   Differentiating w.r.t. a at 0 gives ∑_k P(k)·k(i)·(1+b)^{k(j)} = n·pᵢ·(1+pⱼb)^{n-1}.
   Differentiating that w.r.t. b at 0 gives E[XᵢXⱼ] = n(n-1)pᵢpⱼ.

3. **Main theorem**: Cov = n(n-1)pᵢpⱼ - n²pᵢpⱼ = -npᵢpⱼ. ∎
-/

namespace BinomialTheoremOQ02OQ01OQ03

open Finset BigOperators

/-- The multinomial probability mass function.
    Identical to BinomialTheoremOQ02OQ01OQ02.multinomialProb. -/
noncomputable def multinomialProb {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (_ : ℕ) (k : α → ℕ) : ℝ :=
  (Nat.multinomial s k : ℝ) * ∏ i ∈ s, p i ^ k i

lemma multinomialProb_eq {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (k : α → ℕ) :
    multinomialProb s p n k =
    BinomialTheoremOQ02OQ01OQ02.multinomialProb s p n k := rfl

/-! ## Normalization -/

theorem multinomialProb_sum_one {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ) (hp : ∑ i ∈ s, p i = 1) :
    ∑ k ∈ s.piAntidiag n, multinomialProb s p n k = 1 := by
  simp_rw [multinomialProb_eq]
  exact BinomialTheoremOQ02OQ01OQ02.multinomialProb_sum_one s p n hp

/-! ## Mean E[Xᵢ] = n·pᵢ -/

-- Binomial mean for all n including n=0
private lemma binomial_mean_all (n : ℕ) (p : ℝ) :
    ∑ k ∈ range (n + 1), (k : ℝ) * BinomialTheoremOQ03.binomPMF n p k = n * p := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [BinomialTheoremOQ03.binomPMF]
  · exact BinomialTheoremOQ03.binomial_mean n hn p

-- Helper: binomPMF unfolded into choose form
private lemma binomPMF_eq (n : ℕ) (p : ℝ) (j : ℕ) :
    BinomialTheoremOQ03.binomPMF n p j =
    (Nat.choose n j : ℝ) * p ^ j * (1 - p) ^ (n - j) := by
  unfold BinomialTheoremOQ03.binomPMF; ring

/-- **Mean of multinomial component**: E[Xᵢ] = n·p(i).

    Complete proof via fiber grouping:
    1. Group ∑_k k(i₀)*P(k) by value j = k(i₀) using `sum_fiberwise_of_maps_to`
    2. On each fiber {k | k(i₀) = j}: factor out j and apply marginal PMF formula
    3. Recognize as ∑_j j * binomPMF n (p i₀) j = n * p i₀ by `binomial_mean`. -/
theorem multinomial_mean {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ)
    (hp_sum : ∑ i ∈ s, p i = 1) (i₀ : α) (hi₀ : i₀ ∈ s) :
    ∑ k ∈ s.piAntidiag n, (k i₀ : ℝ) * multinomialProb s p n k = n * p i₀ := by
  -- k(i₀) ≤ n for k ∈ piAntidiag n
  have hmaps_to : ∀ k ∈ s.piAntidiag n, k i₀ ∈ range (n + 1) := fun k hk => by
    rw [mem_range]
    have hle : k i₀ ≤ ∑ l ∈ s, k l :=
      Finset.single_le_sum (fun l _ => Nat.zero_le _) s hi₀
    omega
  -- Fiber grouping
  rw [← sum_fiberwise_of_maps_to hmaps_to]
  -- Prove each fiber sum = j * binomPMF n (p i₀) j
  have hfibers : ∀ j ∈ range (n + 1),
      ∑ k ∈ (s.piAntidiag n).filter (fun k => k i₀ = j),
        (k i₀ : ℝ) * multinomialProb s p n k =
      (j : ℝ) * BinomialTheoremOQ03.binomPMF n (p i₀) j := by
    intro j hj
    rw [mem_range] at hj
    -- (1) Replace k(i₀) by j on the filter
    have step1 :
        ∑ k ∈ (s.piAntidiag n).filter (fun k => k i₀ = j),
          (k i₀ : ℝ) * multinomialProb s p n k =
        ∑ k ∈ (s.piAntidiag n).filter (fun k => k i₀ = j),
          (j : ℝ) * multinomialProb s p n k :=
      sum_congr rfl fun k hk => by
        have heq : k i₀ = j := (mem_filter.mp hk).2
        congr 1; exact_mod_cast heq
    -- (2) Factor out j, apply marginal PMF, match binomPMF
    have step2 :
        ∑ k ∈ (s.piAntidiag n).filter (fun k => k i₀ = j),
          (j : ℝ) * multinomialProb s p n k =
        (j : ℝ) * BinomialTheoremOQ03.binomPMF n (p i₀) j := by
      rw [← mul_sum]
      simp_rw [multinomialProb_eq]
      rw [BinomialTheoremOQ02OQ01OQ02.multinomial_marginal_pmf s p n hp_sum i₀ hi₀ j (by omega)]
      rw [binomPMF_eq]
    rw [step1, step2]
  -- Apply the fiber results and use binomial_mean
  rw [sum_congr rfl hfibers]
  exact binomial_mean_all n (p i₀)

/-! ## Cross-Moment E[XᵢXⱼ] = n(n-1)pᵢpⱼ -/

/-- **Cross-moment of multinomial components**: E[XᵢXⱼ] = n·(n-1)·p(i)·p(j) for i ≠ j.

    ## Proof Sketch

    Apply `multinomial_mgf_real` with g(l) = (1+a) if l=i, (1+b) if l=j, 1 otherwise:

      ∑_k P(k)·(1+a)^{k(i)}·(1+b)^{k(j)} = (1 + pᵢa + pⱼb)^n         (*)

    (using ∑_l pₗ·gₗ = 1 + pᵢa + pⱼb since ∑ pₗ = 1 and ∏ gₗ^{kₗ} = (1+a)^{k(i)}·(1+b)^{k(j)})

    Differentiate (*) w.r.t. a at a=0 (using `HasDerivAt.sum` on the LHS):
      ∑_k P(k)·k(i)·(1+b)^{k(j)} = n·pᵢ·(1 + pⱼb)^{n-1}             (**)

    Differentiate (**) w.r.t. b at b=0:
      ∑_k P(k)·k(i)·k(j) = n·pᵢ·(n-1)·pⱼ·(1 + 0)^{n-2} = n(n-1)pᵢpⱼ  ✓

    The HasDerivAt proof requires:
    - `HasDerivAt.sum` for the finite sum
    - `HasDerivAt.pow` + chain rule for (1+a)^m and (1+pᵢa+pⱼb)^n
    - Careful treatment of 0^{m-1} via `Nat.cast_nonneg` and `one_pow` -/
theorem multinomial_cross_moment {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ)
    (hp_sum : ∑ i ∈ s, p i = 1) (hp_nonneg : ∀ i ∈ s, 0 ≤ p i)
    (i j : α) (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    ∑ k ∈ s.piAntidiag n, (k i : ℝ) * (k j : ℝ) * multinomialProb s p n k =
    n * (↑n - 1) * p i * p j := by
  sorry

/-! ## Main Theorem: Covariance = -n·pᵢ·pⱼ -/

/-- **Multinomial Covariance**: Cov(Xᵢ, Xⱼ) = -n·pᵢ·pⱼ for distinct i ≠ j.

    The negative correlation reflects the competition between outcomes in n trials.

    The sum formula for covariance is:
      Σ_k (k(i)·k(j) - E[Xᵢ]·E[Xⱼ]) · P(X=k) = E[XᵢXⱼ] - E[Xᵢ]·E[Xⱼ]

    **Proof**:
      = E[XᵢXⱼ] - n·pᵢ·(n·pⱼ)            [linearity]
      = n(n-1)·pᵢ·pⱼ - n²·pᵢ·pⱼ           [by cross_moment + normalization]
      = -n·pᵢ·pⱼ                            [ring] -/
theorem multinomial_covariance {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ)
    (hp_sum : ∑ i ∈ s, p i = 1) (hp_nonneg : ∀ i ∈ s, 0 ≤ p i)
    (i j : α) (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    ∑ k ∈ s.piAntidiag n,
      ((k i : ℝ) * (k j : ℝ) - n * p i * (n * p j)) *
      ((Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l) =
    -(n : ℝ) * p i * p j := by
  -- Rewrite raw form as multinomialProb
  conv_lhs => arg 2; ext k; rw [show (Nat.multinomial s k : ℝ) * ∏ l ∈ s, p l ^ k l =
      multinomialProb s p n k from rfl]
  -- Expand (a - b) * P = a*P - b*P
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  -- Second sum: n*pi*n*pj * ∑P = n*pi*n*pj  (by normalization)
  have h_norm : ∑ k ∈ s.piAntidiag n,
      n * p i * (n * p j) * multinomialProb s p n k = n * p i * (n * p j) := by
    rw [← Finset.mul_sum, multinomialProb_sum_one s p n hp_sum, mul_one]
  -- First sum: E[Xi*Xj] = n*(n-1)*pi*pj  (by cross moment)
  have h_cross : ∑ k ∈ s.piAntidiag n,
      (k i : ℝ) * (k j : ℝ) * multinomialProb s p n k = n * (↑n - 1) * p i * p j :=
    multinomial_cross_moment s p n hp_sum hp_nonneg i j hi hj hij
  rw [h_cross, h_norm]
  ring

/-! ## Summary -/

/-
## Results

### Proved (0 axioms):
1. `multinomialProb_sum_one`  — Normalization ∑ P(k) = 1
2. `multinomial_mean`         — E[Xᵢ] = n·pᵢ (complete proof via fiber grouping)
3. `multinomial_covariance`   — Cov(Xᵢ,Xⱼ) = -npᵢpⱼ (modulo cross_moment)

### Sorries (1):
4. `multinomial_cross_moment` — E[XᵢXⱼ] = n(n-1)pᵢpⱼ
   Proof: Differentiate the joint MGF (∑ P(k)·(1+a)^{k(i)}·(1+b)^{k(j)} = (1+pᵢa+pⱼb)^n)
   twice using HasDerivAt: ∂/∂a at 0, then ∂/∂b at 0.

### Key Mathematical Content:
The covariance formula -npᵢpⱼ is an exact algebraic consequence of:
  E[XᵢXⱼ] = n(n-1)pᵢpⱼ and E[Xᵢ]E[Xⱼ] = n²pᵢpⱼ
  ⟹ Cov = n(n-1)pᵢpⱼ - n²pᵢpⱼ = -npᵢpⱼ ✓
-/

end BinomialTheoremOQ02OQ01OQ03
