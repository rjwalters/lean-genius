/-
# The Poisson Limit Theorem (Law of Rare Events)

*Open question `binomial-theorem-oq-02-oq-01-oq-02-oq-03`.*
Parent: `BinomialTheoremOQ02OQ01OQ02` proved that each marginal of a multinomial
distribution is binomial.  This file proves the **limiting** behaviour: as the
number of trials `n → ∞` while the success probability `pₙ → 0` with `n·pₙ → λ`,
the binomial pmf converges to the **Poisson pmf** with rate `λ`:

    C(n,k) · pₙ^k · (1 - pₙ)^(n-k)  ⟶  e^(-λ) · λ^k / k!   =   poissonPMFReal λ k.

This is the classical *Poisson limit theorem* (the "law of rare events"), the
analytic engine behind the statement that a multinomial distribution converges to
**independent Poisson components**: combining it with the parent's marginal
reduction shows each component `Xᵢ` converges to `Poisson(λᵢ)`, and the joint
version (`multinomial_tendsto_prod_poisson` below) shows the limit factorises.

## Proof strategy

Write the binomial pmf as a product of three independently convergent factors:

* `C(n,k)·pₙ^k = (1/k!) · ∏_{j<k} ((n - j)·pₙ)`.  Each factor `(n-j)·pₙ → λ`
  (since `n·pₙ → λ` and `j·pₙ → 0`), so the product `→ λ^k`, giving `→ λ^k/k!`.
* `(1 - pₙ)^n → e^(-λ)` via Mathlib's `Real.tendsto_one_add_pow_exp_of_tendsto`
  applied with `g n = -pₙ` (so `n·g n → -λ`).
* `(1 - pₙ)^(n-k) → e^(-λ)` because it equals `(1-pₙ)^n / (1-pₙ)^k` eventually and
  `(1-pₙ)^k → 1`.

Multiplying the limits gives `e^(-λ)·λ^k/k!`.

## Mathlib gap

Mathlib defines `ProbabilityTheory.poissonPMFReal` but contains **no** convergence
result connecting the binomial and Poisson distributions; this supplies it.

## Status
- [x] `binomial_tendsto_poisson` : binomial pmf → Poisson pmf (real form)
- [x] `binomial_tendsto_poissonPMFReal` : restated against Mathlib's `poissonPMFReal`
- [x] joint `multinomial_tendsto_prod_poisson` : independent Poisson limit
- [x] 0 sorries, 0 axioms
-/

import Mathlib.Probability.Distributions.Poisson
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Tactic

namespace PoissonLimitOQ

open Filter Topology Finset
open scoped BigOperators Nat NNReal

/-! ## Auxiliary limits -/

/-- If `n·pₙ → λ` then `pₙ → 0`: the probability of a fixed cell shrinks. -/
theorem tendsto_zero_of_tendsto_nat_mul {p : ℕ → ℝ} {lam : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (𝓝 lam)) :
    Tendsto p atTop (𝓝 0) := by
  have hdiv : Tendsto (fun n : ℕ => ((n : ℝ) * p n) / (n : ℝ)) atTop (𝓝 0) :=
    hp.div_atTop tendsto_natCast_atTop_atTop
  refine hdiv.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-- The exponential factor: `(1 - pₙ)^n → e^(-λ)` when `n·pₙ → λ`. -/
theorem tendsto_one_sub_pow_exp {p : ℕ → ℝ} {lam : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (𝓝 lam)) :
    Tendsto (fun n => (1 - p n) ^ n) atTop (𝓝 (Real.exp (-lam))) := by
  have hneg : Tendsto (fun n : ℕ => (n : ℝ) * (-p n)) atTop (𝓝 (-lam)) := by
    simpa [mul_neg] using hp.neg
  have h := Real.tendsto_one_add_pow_exp_of_tendsto hneg
  refine h.congr (fun n => ?_)
  rw [sub_eq_add_neg]

/-- The shifted exponential factor: `(1 - pₙ)^(n-m) → e^(-λ)` for any fixed `m`,
when `n·pₙ → λ`.  (The fixed shift `m` washes out since `(1-pₙ)^m → 1`.) -/
theorem tendsto_one_sub_pow_sub_exp {p : ℕ → ℝ} {lam : ℝ} (m : ℕ)
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (𝓝 lam)) :
    Tendsto (fun n => (1 - p n) ^ (n - m)) atTop (𝓝 (Real.exp (-lam))) := by
  have hp0 : Tendsto p atTop (𝓝 0) := tendsto_zero_of_tendsto_nat_mul hp
  have hone_sub : Tendsto (fun n => 1 - p n) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hp0
  have hexpn : Tendsto (fun n => (1 - p n) ^ n) atTop (𝓝 (Real.exp (-lam))) :=
    tendsto_one_sub_pow_exp hp
  have hk1 : Tendsto (fun n => (1 - p n) ^ m) atTop (𝓝 1) := by
    simpa using hone_sub.pow m
  have hpos : ∀ᶠ n in atTop, (0 : ℝ) < 1 - p n :=
    hone_sub.eventually (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))
  have hdiv : Tendsto (fun n => (1 - p n) ^ n / (1 - p n) ^ m) atTop
      (𝓝 (Real.exp (-lam) / 1)) := hexpn.div hk1 one_ne_zero
  rw [div_one] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [hpos, eventually_ge_atTop m] with n hn hnk
  have hne : (1 - p n) ^ m ≠ 0 := pow_ne_zero m hn.ne'
  rw [div_eq_iff hne, ← pow_add, Nat.sub_add_cancel hnk]

/-! ## The Poisson limit theorem (one cell) -/

/-- **Poisson limit theorem (real form).** As `n → ∞` with `n·pₙ → λ`, the binomial
pmf at a fixed value `k` converges to the Poisson pmf `e^(-λ)·λ^k/k!`. -/
theorem binomial_tendsto_poisson (k : ℕ) {p : ℕ → ℝ} {lam : ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (𝓝 lam)) :
    Tendsto (fun n => (n.choose k : ℝ) * p n ^ k * (1 - p n) ^ (n - k)) atTop
      (𝓝 (Real.exp (-lam) * lam ^ k / k.factorial)) := by
  have hp0 : Tendsto p atTop (𝓝 0) := tendsto_zero_of_tendsto_nat_mul hp
  -- (1 - pₙ)^(n-k) → e^(-λ)
  have hsubk : Tendsto (fun n => (1 - p n) ^ (n - k)) atTop (𝓝 (Real.exp (-lam))) :=
    tendsto_one_sub_pow_sub_exp k hp
  -- C(n,k)·pₙ^k → λ^k/k!
  have hCp : Tendsto (fun n => (n.choose k : ℝ) * p n ^ k) atTop
      (𝓝 (lam ^ k / k.factorial)) := by
    -- each falling factor (n - j)·pₙ → λ
    have hfac : ∀ j ∈ range k,
        Tendsto (fun n : ℕ => ((n : ℝ) - j) * p n) atTop (𝓝 lam) := by
      intro j _
      have hjp : Tendsto (fun n => (j : ℝ) * p n) atTop (𝓝 0) := by
        simpa using hp0.const_mul (j : ℝ)
      have : Tendsto (fun n : ℕ => (n : ℝ) * p n - (j : ℝ) * p n) atTop (𝓝 (lam - 0)) :=
        hp.sub hjp
      simpa [sub_mul] using this
    have hprod : Tendsto (fun n : ℕ => ∏ j ∈ range k, (((n : ℝ) - j) * p n)) atTop
        (𝓝 (∏ _j ∈ range k, lam)) := tendsto_finset_prod _ hfac
    rw [prod_const, card_range] at hprod
    -- (1/k!) · ∏ → λ^k/k!
    have hscaled : Tendsto (fun n : ℕ => (k.factorial : ℝ)⁻¹ * ∏ j ∈ range k, (((n : ℝ) - j) * p n))
        atTop (𝓝 ((k.factorial : ℝ)⁻¹ * lam ^ k)) := hprod.const_mul _
    rw [show (k.factorial : ℝ)⁻¹ * lam ^ k = lam ^ k / k.factorial from by ring] at hscaled
    refine hscaled.congr' ?_
    filter_upwards [eventually_ge_atTop k] with n hnk
    -- algebraic identity: C(n,k)·pₙ^k = (1/k!) · ∏_{j<k} ((n-j)·pₙ)
    have hcast : ((n.descFactorial k : ℕ) : ℝ) = ∏ j ∈ range k, ((n : ℝ) - j) := by
      rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
      refine prod_congr rfl ?_
      intro j hj
      rw [mem_range] at hj
      rw [Nat.cast_sub (le_of_lt (lt_of_lt_of_le hj hnk))]
    have hchoose : (n.choose k : ℝ) = (∏ j ∈ range k, ((n : ℝ) - j)) / (k.factorial : ℝ) := by
      have hfk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
      rw [eq_div_iff hfk, ← hcast]
      rw [← Nat.cast_mul]
      congr 1
      rw [mul_comm, ← Nat.descFactorial_eq_factorial_mul_choose]
    rw [hchoose, prod_mul_distrib, prod_const, card_range]
    ring
  -- combine: target = (C(n,k)·pₙ^k) · (1-pₙ)^(n-k)
  have hmul := hCp.mul hsubk
  rw [show lam ^ k / (k.factorial : ℝ) * Real.exp (-lam)
        = Real.exp (-lam) * lam ^ k / (k.factorial : ℝ) from by ring] at hmul
  exact hmul

/-- **Poisson limit theorem, stated against Mathlib's `poissonPMFReal`.**  With rate
`r : ℝ≥0`, the binomial pmf converges to the Poisson pmf of `ProbabilityTheory`. -/
theorem binomial_tendsto_poissonPMFReal (k : ℕ) (r : ℝ≥0) {p : ℕ → ℝ}
    (hp : Tendsto (fun n : ℕ => (n : ℝ) * p n) atTop (𝓝 (r : ℝ))) :
    Tendsto (fun n => (n.choose k : ℝ) * p n ^ k * (1 - p n) ^ (n - k)) atTop
      (𝓝 (ProbabilityTheory.poissonPMFReal r k)) := by
  have h := binomial_tendsto_poisson k hp
  rwa [ProbabilityTheory.poissonPMFReal]

/-! ## The joint limit: a multinomial converges to independent Poissons -/

variable {ι : Type*}

/-- The key product limit underlying the joint Poisson limit.  The descending
factorial `∏_{j<K}(n-j)` (where `K = ∑ᵢ kᵢ`) times `∏ᵢ (pᵢ n)^{kᵢ}` converges to
`∏ᵢ λᵢ^{kᵢ}`.  Proof: rewrite the product as `∏_{j<K}(1 - j/n) · ∏ᵢ (n·pᵢ n)^{kᵢ}`;
the first factor `→ 1` and each `n·pᵢ n → λᵢ`. -/
theorem tendsto_descFactorial_mul_prod (s : Finset ι) (k : ι → ℕ)
    {p : ι → ℕ → ℝ} {lam : ι → ℝ}
    (hp : ∀ i ∈ s, Tendsto (fun n : ℕ => (n : ℝ) * p i n) atTop (𝓝 (lam i))) :
    Tendsto (fun n : ℕ => (∏ j ∈ range (∑ i ∈ s, k i), ((n : ℝ) - j)) *
        ∏ i ∈ s, (p i n) ^ (k i)) atTop (𝓝 (∏ i ∈ s, (lam i) ^ (k i))) := by
  set K := ∑ i ∈ s, k i with hK
  -- factor 1: ∏_{j<K}(1 - j/n) → 1
  have hf1 : Tendsto (fun n : ℕ => ∏ j ∈ range K, (1 - (j : ℝ) / (n : ℝ))) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => ∏ j ∈ range K, (1 - (j : ℝ) / (n : ℝ))) atTop
        (𝓝 (∏ _j ∈ range K, (1 : ℝ))) := by
      apply tendsto_finset_prod
      intro j _
      have hj : Tendsto (fun n : ℕ => (j : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
        (tendsto_const_nhds (x := (j : ℝ))).div_atTop tendsto_natCast_atTop_atTop
      simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hj
    simpa using this
  -- factor 2: ∏ᵢ (n·pᵢ)^{kᵢ} → ∏ᵢ λᵢ^{kᵢ}
  have hf2 : Tendsto (fun n : ℕ => ∏ i ∈ s, ((n : ℝ) * p i n) ^ (k i)) atTop
      (𝓝 (∏ i ∈ s, (lam i) ^ (k i))) := by
    apply tendsto_finset_prod
    intro i hi
    exact (hp i hi).pow (k i)
  have hmul := hf1.mul hf2
  rw [one_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have e2 : ∏ i ∈ s, ((n : ℝ) * p i n) ^ (k i)
      = (n : ℝ) ^ K * ∏ i ∈ s, (p i n) ^ (k i) := by
    simp_rw [mul_pow]
    rw [prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← hK]
  have e1 : (∏ j ∈ range K, (1 - (j : ℝ) / (n : ℝ))) * (n : ℝ) ^ K
      = ∏ j ∈ range K, ((n : ℝ) - j) := by
    rw [show (n : ℝ) ^ K = ∏ _j ∈ range K, (n : ℝ) from by rw [prod_const, card_range]]
    rw [← prod_mul_distrib]
    refine prod_congr rfl (fun j _ => ?_)
    rw [sub_mul, one_mul, div_mul_cancel₀ (j : ℝ) hn0]
  rw [e2, ← mul_assoc, e1]

/-- The pmf of a multinomial distribution with `s`-many "rare" cells (rates
`pᵢ n`) and an implicit residual cell of probability `1 - ∑ᵢ pᵢ n`, evaluated at
fixed counts `kᵢ`.  Equals `n! / (∏ᵢ kᵢ! · (n-∑k)!) · ∏ᵢ pᵢ^{kᵢ} · (1-∑p)^{n-∑k}`. -/
noncomputable def multinomialPMF (s : Finset ι) (k : ι → ℕ) (p : ι → ℕ → ℝ) (n : ℕ) : ℝ :=
  (n.factorial : ℝ) / ((∏ i ∈ s, ((k i).factorial : ℝ)) * ((n - ∑ i ∈ s, k i).factorial : ℝ))
    * (∏ i ∈ s, (p i n) ^ (k i)) * (1 - ∑ i ∈ s, p i n) ^ (n - ∑ i ∈ s, k i)

/-- **Multinomial → independent Poisson limit.**  As `n → ∞` with `n·pᵢ n → λᵢ` for
each cell `i ∈ s`, the joint multinomial pmf at fixed counts `kᵢ` converges to the
product of Poisson pmfs `∏ᵢ e^(-λᵢ)·λᵢ^{kᵢ}/kᵢ!` — i.e. the cells become
asymptotically independent, each Poisson(λᵢ). -/
theorem multinomial_tendsto_prod_poisson (s : Finset ι) (k : ι → ℕ)
    {p : ι → ℕ → ℝ} {lam : ι → ℝ}
    (hp : ∀ i ∈ s, Tendsto (fun n : ℕ => (n : ℝ) * p i n) atTop (𝓝 (lam i))) :
    Tendsto (fun n : ℕ => multinomialPMF s k p n) atTop
      (𝓝 (∏ i ∈ s, (Real.exp (-lam i) * (lam i) ^ (k i) / (k i).factorial))) := by
  set K := ∑ i ∈ s, k i with hK
  -- total non-residual probability has rate ∑ᵢ λᵢ
  have hPsum : Tendsto (fun n : ℕ => (n : ℝ) * ∑ i ∈ s, p i n) atTop (𝓝 (∑ i ∈ s, lam i)) := by
    have : Tendsto (fun n : ℕ => ∑ i ∈ s, (n : ℝ) * p i n) atTop (𝓝 (∑ i ∈ s, lam i)) :=
      tendsto_finset_sum _ hp
    simpa [Finset.mul_sum] using this
  -- residual factor → e^(-∑λ) = ∏ᵢ e^(-λᵢ)
  have hres : Tendsto (fun n : ℕ => (1 - ∑ i ∈ s, p i n) ^ (n - K)) atTop
      (𝓝 (Real.exp (-∑ i ∈ s, lam i))) := tendsto_one_sub_pow_sub_exp K hPsum
  -- falling factorial × ∏ pᵢ^{kᵢ} → ∏ᵢ λᵢ^{kᵢ}
  have hfall := tendsto_descFactorial_mul_prod s k hp
  rw [← hK] at hfall
  -- assemble: (∏kᵢ!)⁻¹ · (falling × ∏p^k) · residual
  have hstep := ((hfall.const_mul ((∏ i ∈ s, ((k i).factorial : ℝ))⁻¹)).mul hres)
  -- the constant `(∏kᵢ!)⁻¹` is nonzero
  have hfk : ((∏ i ∈ s, ((k i).factorial : ℝ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => by exact_mod_cast (k i).factorial_ne_zero)
  -- rewrite the limit value to the target product
  rw [show (∏ i ∈ s, ((k i).factorial : ℝ))⁻¹ * (∏ i ∈ s, (lam i) ^ (k i))
        * Real.exp (-∑ i ∈ s, lam i)
        = ∏ i ∈ s, (Real.exp (-lam i) * (lam i) ^ (k i) / (k i).factorial) from by
    have hexp : Real.exp (-∑ i ∈ s, lam i) = ∏ i ∈ s, Real.exp (-lam i) := by
      rw [← Real.exp_sum]; congr 1; simp
    rw [hexp, ← Finset.prod_inv_distrib, ← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_congr rfl (fun i _ => ?_)
    rw [div_eq_mul_inv]; ring] at hstep
  -- match the function with multinomialPMF
  refine hstep.congr' ?_
  filter_upwards [eventually_ge_atTop K] with n hnk
  have hnK : ((n - K).factorial : ℝ) ≠ 0 := by exact_mod_cast (n - K).factorial_ne_zero
  -- n!/(n-K)! = descFactorial = ∏_{j<K}(n-j)
  have hcast : ((n.descFactorial K : ℕ) : ℝ) = ∏ j ∈ range K, ((n : ℝ) - j) := by
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    refine prod_congr rfl (fun j hj => ?_)
    rw [mem_range] at hj
    rw [Nat.cast_sub (le_of_lt (lt_of_lt_of_le hj hnk))]
  have hfact : (n.factorial : ℝ) / ((n - K).factorial : ℝ) = ∏ j ∈ range K, ((n : ℝ) - j) := by
    rw [div_eq_iff hnK, ← hcast, ← Nat.cast_mul]
    congr 1
    rw [Nat.descFactorial_eq_factorial_mul_choose, mul_comm (K.factorial) (n.choose K),
      Nat.choose_mul_factorial_mul_factorial hnk]
  -- finish: assemble the multinomial pmf algebraically
  simp only [multinomialPMF]
  rw [← hK, ← hfact]
  field_simp

end PoissonLimitOQ
