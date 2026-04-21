import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
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

2. **E[XᵢXⱼ] = n(n-1)·pᵢ·pⱼ**: Apply multinomial MGF theorem with
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
      Finset.single_le_sum (fun l _ => Nat.zero_le _) hi₀
    have hsum : ∑ l ∈ s, k l = n := (Finset.mem_piAntidiag.mp hk).1
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

    Proof via bivariate MGF differentiation:

    Step 1: Prove ∀ a b, ∑_k P(k)·(1+a)^{k(i)}·(1+b)^{k(j)} = (1+pᵢa+pⱼb)^n  [MGF]

    Step 2: Differentiate w.r.t. a at 0 (HasDerivAt.sum + chain rule):
      ∑_k P(k)·k(i)·(1+b)^{k(j)} = n·pᵢ·(1+pⱼb)^{n-1}

    Step 3: Differentiate w.r.t. b at 0:
      ∑_k P(k)·k(i)·k(j) = n·pᵢ·(n-1)·pⱼ = n(n-1)pᵢpⱼ  ✓  -/
theorem multinomial_cross_moment {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → ℝ) (n : ℕ)
    (hp_sum : ∑ i ∈ s, p i = 1) (hp_nonneg : ∀ i ∈ s, 0 ≤ p i)
    (i j : α) (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j) :
    ∑ k ∈ s.piAntidiag n, (k i : ℝ) * (k j : ℝ) * multinomialProb s p n k =
    n * (↑n - 1) * p i * p j := by
  -- Helper: (1+a)^m has derivative m at a=0
  have deriv_add_pow : ∀ (m : ℕ),
      HasDerivAt (fun a : ℝ => (1 + a) ^ m) (↑m) 0 := fun m => by
    have h := (hasDerivAt_pow m (1 + (0 : ℝ))).comp 0
                ((hasDerivAt_id (0 : ℝ)).const_add 1)
    simp only [Function.comp, add_zero, one_pow, mul_one] at h
    exact h
  -- Bivariate MGF: ∑_k P(k)*(1+a)^{ki}*(1+b)^{kj} = (1+pi*a+pj*b)^n
  have hmgf : ∀ (a b : ℝ),
      ∑ k ∈ s.piAntidiag n,
        multinomialProb s p n k * (1 + a) ^ k i * (1 + b) ^ k j =
      (1 + p i * a + p j * b) ^ n := by
    intro a b
    -- Product formula: ∏_l g_l^{k_l} = (1+a)^{ki} * (1+b)^{kj}
    have hprod : ∀ k : α → ℕ,
        ∏ l ∈ s, (if l = i then 1 + a else if l = j then 1 + b else (1 : ℝ)) ^ k l =
        (1 + a) ^ k i * (1 + b) ^ k j := fun k => by
      rw [← Finset.mul_prod_erase s _ hi,
          ← Finset.mul_prod_erase (s.erase i) _
              (Finset.mem_erase.mpr ⟨hij.symm, hj⟩)]
      have hgi : (if i = i then 1 + a else if i = j then 1 + b else (1 : ℝ)) ^ k i =
                 (1 + a) ^ k i := by simp
      have hgj : (if j = i then 1 + a else if j = j then 1 + b else (1 : ℝ)) ^ k j =
                 (1 + b) ^ k j := by simp [hij.symm]
      have hrest : ∏ x ∈ (s.erase i).erase j,
          (if x = i then 1 + a else if x = j then 1 + b else (1 : ℝ)) ^ k x = 1 := by
        apply Finset.prod_eq_one; intro l hl
        have hli : l ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
        have hlj : l ≠ j := (Finset.mem_erase.mp hl).1
        simp [hli, hlj]
      rw [hgi, hgj, hrest]; ring
    -- Sum formula: ∑_l p_l * g_l = 1 + pi*a + pj*b
    have hsum_g : ∑ l ∈ s,
        p l * (if l = i then 1 + a else if l = j then 1 + b else (1 : ℝ)) =
        1 + p i * a + p j * b := by
      rw [← Finset.add_sum_erase s _ hi,
          ← Finset.add_sum_erase (s.erase i) _
              (Finset.mem_erase.mpr ⟨hij.symm, hj⟩)]
      have hgi : p i * (if i = i then 1 + a else if i = j then 1 + b else (1 : ℝ)) =
                 p i * (1 + a) := by simp
      have hgj : p j * (if j = i then 1 + a else if j = j then 1 + b else (1 : ℝ)) =
                 p j * (1 + b) := by simp [hij.symm]
      have hrest : ∑ l ∈ (s.erase i).erase j,
          p l * (if l = i then 1 + a else if l = j then 1 + b else (1 : ℝ)) =
          ∑ l ∈ (s.erase i).erase j, p l := by
        apply Finset.sum_congr rfl; intro l hl
        have hli := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
        have hlj := (Finset.mem_erase.mp hl).1
        simp [hli, hlj]
      have hprest : ∑ l ∈ (s.erase i).erase j, p l = 1 - p i - p j := by
        have h1 := (Finset.add_sum_erase s p hi).symm
        have h2 := (Finset.add_sum_erase (s.erase i) p
              (Finset.mem_erase.mpr ⟨hij.symm, hj⟩)).symm
        linarith [hp_sum]
      rw [hgi, hgj, hrest, hprest]; ring
    -- Convert to BinomialTheoremOQ02OQ01OQ02 form and apply MGF theorem
    have h_eq_sum : ∑ k ∈ s.piAntidiag n,
        multinomialProb s p n k * (1 + a) ^ k i * (1 + b) ^ k j =
      ∑ k ∈ s.piAntidiag n,
        BinomialTheoremOQ02OQ01OQ02.multinomialProb s p n k *
        ∏ l ∈ s, (if l = i then 1 + a else if l = j then 1 + b else (1 : ℝ)) ^ k l := by
      apply Finset.sum_congr rfl; intro k _
      rw [multinomialProb_eq, hprod k]; ring
    rw [h_eq_sum, ← BinomialTheoremOQ02OQ01OQ02.multinomial_mgf_real, hsum_g]
  -- Step 1: Differentiate w.r.t. a at 0
  -- Result: ∑_k P(k)*ki*(1+b)^{kj} = n*pi*(1+pj*b)^(n-1)
  have hstep1 : ∀ b : ℝ,
      ∑ k ∈ s.piAntidiag n,
        multinomialProb s p n k * (k i : ℝ) * (1 + b) ^ k j =
      n * p i * (1 + p j * b) ^ (n - 1) := fun b => by
    -- LHS: derivative of a-parameterized sum at a=0
    have hd_lhs : HasDerivAt
        (fun a => ∑ k ∈ s.piAntidiag n,
          multinomialProb s p n k * (1 + a) ^ k i * (1 + b) ^ k j)
        (∑ k ∈ s.piAntidiag n,
          multinomialProb s p n k * (k i : ℝ) * (1 + b) ^ k j)
        0 := by
      have key : ∀ k ∈ s.piAntidiag n,
          HasDerivAt (fun a => multinomialProb s p n k * (1 + a) ^ k i * (1 + b) ^ k j)
            (multinomialProb s p n k * (k i : ℝ) * (1 + b) ^ k j) 0 := fun k _ => by
        have hd1 := deriv_add_pow (k i)
        have hd2 := (hd1.const_mul (multinomialProb s p n k)).mul_const ((1 + b) ^ k j)
        convert hd2 using 1
      have h := HasDerivAt.sum key
      have feq : (∑ k ∈ s.piAntidiag n, fun a =>
            multinomialProb s p n k * (1 + a) ^ k i * (1 + b) ^ k j) =
          (fun a => ∑ k ∈ s.piAntidiag n,
            multinomialProb s p n k * (1 + a) ^ k i * (1 + b) ^ k j) :=
        funext fun a => Finset.sum_apply _ _ _
      rw [feq] at h; exact h
    -- RHS: derivative of (1+pi*a+pj*b)^n at a=0
    have hd_rhs : HasDerivAt
        (fun a => (1 + p i * a + p j * b : ℝ) ^ n)
        (n * p i * (1 + p j * b) ^ (n - 1))
        0 := by
      have hinner : HasDerivAt (fun a : ℝ => 1 + p i * a + p j * b) (p i) 0 := by
        have h1 : HasDerivAt (fun a : ℝ => p i * a) (p i * 1) 0 :=
          (hasDerivAt_id (0 : ℝ)).const_mul (p i)
        have h2 : HasDerivAt (fun a : ℝ => p i * a + p j * b) (p i * 1) 0 :=
          h1.add_const _
        have h3 : HasDerivAt (fun a : ℝ => 1 + (p i * a + p j * b)) (p i * 1) 0 :=
          h2.const_add 1
        simp only [mul_one] at h3
        convert h3 using 1; funext a; ring
      have houter : HasDerivAt (fun x : ℝ => x ^ n) (↑n * (1 + p i * 0 + p j * b) ^ (n - 1))
          (1 + p i * 0 + p j * b) :=
        hasDerivAt_pow n _
      -- comp before simp so base points match syntactically
      have hcomp := houter.comp 0 hinner
      simp only [mul_zero, add_zero, Function.comp] at hcomp
      convert hcomp using 1; ring
    have hfg : (fun a => ∑ k ∈ s.piAntidiag n,
          multinomialProb s p n k * (1 + a) ^ k i * (1 + b) ^ k j) =
              fun a => (1 + p i * a + p j * b : ℝ) ^ n :=
      funext (fun a => hmgf a b)
    rw [hfg] at hd_lhs
    linarith [hd_lhs.unique hd_rhs]
  -- Step 2: Differentiate w.r.t. b at 0
  -- Result: ∑_k P(k)*ki*kj = n*(n-1:ℕ)*pi*pj
  have hstep2 : ∑ k ∈ s.piAntidiag n,
      multinomialProb s p n k * (k i : ℝ) * (k j : ℝ) =
      n * ↑(n - 1) * p i * p j := by
    have hd_lhs : HasDerivAt
        (fun b => ∑ k ∈ s.piAntidiag n,
          multinomialProb s p n k * (k i : ℝ) * (1 + b) ^ k j)
        (∑ k ∈ s.piAntidiag n,
          multinomialProb s p n k * (k i : ℝ) * (k j : ℝ))
        0 := by
      have key : ∀ k ∈ s.piAntidiag n,
          HasDerivAt (fun b => multinomialProb s p n k * (k i : ℝ) * (1 + b) ^ k j)
            (multinomialProb s p n k * (k i : ℝ) * (k j : ℝ)) 0 := fun k _ => by
        have hd1 := deriv_add_pow (k j)
        have hd2 := hd1.const_mul (multinomialProb s p n k * (k i : ℝ))
        convert hd2 using 1 <;> ring
      have h := HasDerivAt.sum key
      have feq : (∑ k ∈ s.piAntidiag n, fun b =>
            multinomialProb s p n k * (k i : ℝ) * (1 + b) ^ k j) =
          (fun b => ∑ k ∈ s.piAntidiag n,
            multinomialProb s p n k * (k i : ℝ) * (1 + b) ^ k j) :=
        funext fun b => Finset.sum_apply _ _ _
      rw [feq] at h; exact h
    have hd_rhs : HasDerivAt
        (fun b => (n : ℝ) * p i * (1 + p j * b) ^ (n - 1))
        (n * ↑(n - 1) * p i * p j)
        0 := by
      have hinner : HasDerivAt (fun b : ℝ => 1 + p j * b) (p j) 0 := by
        have h1 : HasDerivAt (fun b : ℝ => p j * b) (p j * 1) 0 :=
          (hasDerivAt_id (0 : ℝ)).const_mul (p j)
        have h2 := h1.const_add (1 : ℝ)
        simp only [mul_one] at h2
        exact h2
      have houter : HasDerivAt (fun x : ℝ => x ^ (n - 1))
          (↑(n - 1) * (1 + p j * 0) ^ ((n - 1) - 1)) (1 + p j * 0) :=
        hasDerivAt_pow (n - 1) _
      -- comp before simp so base points match syntactically
      have hcomp := houter.comp 0 hinner
      simp only [mul_zero, add_zero, one_pow, mul_one] at hcomp
      -- hcomp : HasDerivAt (fun b => (1+pj*b)^(n-1)) (↑(n-1) * pj) 0
      have hscaled := hcomp.const_mul ((n : ℝ) * p i)
      -- hscaled : HasDerivAt (fun b => n*pi*(1+pj*b)^(n-1)) (n*pi*(↑(n-1)*pj)) 0
      convert hscaled using 1; ring
    have hfg : (fun b => ∑ k ∈ s.piAntidiag n,
          multinomialProb s p n k * (k i : ℝ) * (1 + b) ^ k j) =
              fun b => (n : ℝ) * p i * (1 + p j * b) ^ (n - 1) :=
      funext hstep1
    rw [hfg] at hd_lhs
    linarith [hd_lhs.unique hd_rhs]
  -- Reorder multiplication and cast n-1 to match goal
  rw [show ∑ k ∈ s.piAntidiag n, (k i : ℝ) * (k j : ℝ) * multinomialProb s p n k =
          ∑ k ∈ s.piAntidiag n, multinomialProb s p n k * (k i : ℝ) * (k j : ℝ) from
    Finset.sum_congr rfl (fun k _ => by ring)]
  rw [hstep2]
  -- (n-1:ℕ):ℝ = (n:ℝ)-1 when n≥1; both sides 0 when n=0
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Nat.cast_pred hn]

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

### Proved (0 axioms, 0 sorries):
1. `multinomialProb_sum_one`   — Normalization ∑ P(k) = 1
2. `multinomial_mean`          — E[Xᵢ] = n·pᵢ (complete proof via fiber grouping)
3. `multinomial_cross_moment`  — E[XᵢXⱼ] = n(n-1)pᵢpⱼ (via bivariate MGF differentiation)
4. `multinomial_covariance`    — Cov(Xᵢ,Xⱼ) = -npᵢpⱼ

### Key Mathematical Content:
The covariance formula -npᵢpⱼ is an exact algebraic consequence of:
  E[XᵢXⱼ] = n(n-1)pᵢpⱼ and E[Xᵢ]E[Xⱼ] = n²pᵢpⱼ
  ⟹ Cov = n(n-1)pᵢpⱼ - n²pᵢpⱼ = -npᵢpⱼ ✓

The cross-moment proof uses differentiation of the bivariate MGF:
  (∑_l pₗ·gₗ)^n = ∑_k P(k)·∏_l gₗ^{kₗ}   [multinomial_mgf_real]
with gₗ = (1+a) for l=i, (1+b) for l=j, 1 otherwise.
-/

end BinomialTheoremOQ02OQ01OQ03
