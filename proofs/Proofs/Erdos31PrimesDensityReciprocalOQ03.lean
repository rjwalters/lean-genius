/-
Erdős Problem #31 Follow-up (OQ-03): Mertens' Lower Bound for Σ 1/p

The parent entry `erdos-31-primes-density` proves that the primes have natural
density zero via the Chebyshev upper bound π(N) = O(N/log N).  Its third open
question asks for the *rate* at which the primes accumulate on the logarithmic
scale — Mertens' second theorem, Σ_{p ≤ N} 1/p ~ log log N.

Mathlib supplies only the *qualitative* divergence of Σ 1/p
(`not_summable_one_div_on_primes`, via Erdős's rough-number argument), which
gives no rate.  Here we prove the quantitative **lower** half of Mertens'
theorem with an explicit constant, by the classical Euler-product argument:

    Σ_{p ≤ N} 1/p  ≥  log log (N + 1) − 1     (for N ≥ 1).

Proof architecture (Euler product):

1. `harmonic_le_euler_product`  —  ∑_{k=1}^N 1/k ≤ ∏_{p ≤ N} (1 − 1/p)⁻¹.
   (Unique factorisation: every k ≤ N is a product of primes ≤ N, so 1/k
   appears in the expansion of the geometric factors.)
2. `sum_log_euler_factor_le`  —  ∑_{p ≤ N} log((1 − 1/p)⁻¹) ≤ ∑_{p ≤ N} 1/p + 1.
   (Per prime, −log(1 − 1/p) − 1/p ≤ 1/(p(p−1)); the tail sums to < 1.)
3. Assembly: chain `log_add_one_le_harmonic` (Mathlib) with (1), take logs, and
   bound with (2).

Status: work in progress — steps (1),(2) isolated; assembly complete.
Dependencies: Only Mathlib.
-/

import Mathlib

open Finset

namespace Erdos31PrimesDensityReciprocal

/-- The primes `≤ N`, as a `Finset`. -/
def primesLe (N : ℕ) : Finset ℕ := (Finset.range (N + 1)).filter Nat.Prime

lemma mem_primesLe {N p : ℕ} : p ∈ primesLe N ↔ p ≤ N ∧ p.Prime := by
  simp only [primesLe, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨h, hp⟩; exact ⟨by omega, hp⟩
  · rintro ⟨h, hp⟩; exact ⟨by omega, hp⟩

/-- Each Euler factor `(1 - 1/p)⁻¹` is strictly positive for a prime `p`. -/
lemma euler_factor_pos {p : ℕ} (hp : p.Prime) : 0 < (1 - 1 / (p : ℝ))⁻¹ := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have h1 : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) ≤ 1 / 2 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp2
    linarith
  positivity

lemma euler_factor_ne {p : ℕ} (hp : p.Prime) : (1 - 1 / (p : ℝ))⁻¹ ≠ 0 :=
  ne_of_gt (euler_factor_pos hp)

/-- The Euler product `∏_{p ≤ N} (1 - 1/p)⁻¹` is strictly positive. -/
lemma euler_product_pos (N : ℕ) :
    0 < ∏ p ∈ primesLe N, (1 - 1 / (p : ℝ))⁻¹ := by
  apply Finset.prod_pos
  intro p hp
  exact euler_factor_pos (mem_primesLe.mp hp).2

/-! ## Step 1: harmonic partial sum ≤ Euler product (crux, combinatorial) -/

/-- The reciprocal map `n ↦ (n : ℝ)⁻¹` as a multiplicative monoid homomorphism.
Multiplicativity holds because `(ab)⁻¹ = a⁻¹ b⁻¹` in the field `ℝ` (with `0⁻¹ = 0`). -/
noncomputable def invHom : ℕ →* ℝ where
  toFun n := (n : ℝ)⁻¹
  map_one' := by simp
  map_mul' a b := by push_cast; rw [mul_inv]

@[simp] lemma invHom_apply (n : ℕ) : invHom n = (n : ℝ)⁻¹ := rfl

/-- `primesLe N` is exactly `Nat.primesBelow (N + 1)`. -/
lemma primesLe_eq_primesBelow (N : ℕ) : primesLe N = Nat.primesBelow (N + 1) := rfl

/-- Every `k ∈ [1, N]` is `(N+1)`-smooth: nonzero with all prime factors `≤ N < N+1`. -/
lemma Icc_subset_smoothNumbers (N : ℕ) :
    ↑(Finset.Icc 1 N) ⊆ Nat.smoothNumbers (N + 1) := by
  intro k hk
  simp only [Finset.coe_Icc, Set.mem_Icc] at hk
  obtain ⟨hk1, hkN⟩ := hk
  rw [Nat.mem_smoothNumbers]
  refine ⟨by omega, ?_⟩
  intro p hp
  have hpd : p ∣ k := Nat.dvd_of_mem_primeFactorsList hp
  have hple : p ≤ k := Nat.le_of_dvd (by omega) hpd
  omega

/-- **Euler product lower bound.**  The `N`-th harmonic partial sum is dominated
by the finite Euler product over primes `≤ N`.  Every `k ∈ [1, N]` factors into
primes `≤ N`, so `1/k` occurs in the expansion of `∏_{p ≤ N} ∑_{e ≥ 0} p^{-e}`;
since all terms are nonnegative, the sum of the diagonal `1/k` is at most the
product. -/
lemma harmonic_le_euler_product (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, (1 / k : ℝ) ≤ ∏ p ∈ primesLe N, (1 - 1 / (p : ℝ))⁻¹ := by
  -- ‖f p‖ < 1 for each prime p, so the smooth-number Euler product converges.
  have hnorm : ∀ {p : ℕ}, p.Prime → ‖invHom p‖ < 1 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    rw [invHom_apply, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [inv_lt_one_iff₀]; right; linarith
  obtain ⟨hsummable, hhassum⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hnorm (N + 1)
  -- The Euler product on smooth numbers equals our product over primesLe N.
  set S : Set ℕ := Nat.smoothNumbers (N + 1) with hS
  have hprod_eq : (∏ p ∈ Nat.primesBelow (N + 1), (1 - invHom p)⁻¹)
      = ∏ p ∈ primesLe N, (1 - 1 / (p : ℝ))⁻¹ := by
    rw [primesLe_eq_primesBelow]
    apply Finset.prod_congr rfl
    intro p _; simp [one_div]
  rw [← hprod_eq]
  -- Move to the indicator formulation on all of ℕ.
  have hsummable_sub : Summable (fun m : S ↦ invHom (m : ℕ)) := hhassum.summable
  have hsum_ind : Summable (S.indicator (fun n => invHom n)) :=
    summable_subtype_iff_indicator.mp hsummable_sub
  have hRHS : (∏ p ∈ Nat.primesBelow (N + 1), (1 - invHom p)⁻¹)
      = ∑' n, S.indicator (fun n => invHom n) n := by
    rw [← hhassum.tsum_eq]; exact tsum_subtype S (fun n => invHom n)
  -- The harmonic sum equals the indicator sum over Icc 1 N.
  have hsub := Icc_subset_smoothNumbers N
  have heq : ∑ k ∈ Finset.Icc 1 N, (1 / k : ℝ)
      = ∑ k ∈ Finset.Icc 1 N, S.indicator (fun n => invHom n) k := by
    apply Finset.sum_congr rfl
    intro k hk
    have hkS : k ∈ S := hsub (by simpa using hk)
    rw [Set.indicator_of_mem hkS, invHom_apply, one_div]
  rw [hRHS, heq]
  -- Finite subsum ≤ full nonnegative tsum.
  exact Summable.sum_le_tsum (Finset.Icc 1 N)
    (fun i _ => Set.indicator_nonneg (fun n _ => by simp [invHom_apply, inv_nonneg]) i) hsum_ind

/-! ## Step 2: sum of log Euler factors ≤ Σ 1/p + 1 (crux, analytic) -/

/-- Telescoping identity `∑_{n=2}^{N+1} 1/(n(n-1)) = 1 - 1/(N+1)`. -/
lemma tail_sum_Icc (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 (N + 1), (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) = 1 - 1 / ((N : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih]
    have h1 : ((M : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((M : ℝ) + 2) ≠ 0 := by positivity
    have hT : ((M + 1 + 1 : ℕ) : ℝ) * (((M + 1 + 1 : ℕ) : ℝ) - 1)
        = ((M : ℝ) + 2) * ((M : ℝ) + 1) := by push_cast; ring
    have hR : ((M + 1 : ℕ) : ℝ) + 1 = (M : ℝ) + 2 := by push_cast; ring
    rw [hT, hR]
    field_simp
    ring

/-- The tail sum over primes `≤ N` is bounded by `1`: `∑_{p ≤ N} 1/(p(p-1)) ≤ 1`. -/
lemma tail_bound (N : ℕ) :
    ∑ p ∈ primesLe N, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 1 := by
  have hsub : primesLe N ⊆ Finset.Icc 2 N := by
    intro p hp
    rw [mem_primesLe] at hp
    rw [Finset.mem_Icc]
    exact ⟨hp.2.two_le, hp.1⟩
  have hle : ∑ p ∈ primesLe N, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) ≤
      ∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro n hn _
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by
      rw [Finset.mem_Icc] at hn; exact_mod_cast hn.1
    apply div_nonneg (by norm_num)
    nlinarith [hn2]
  refine hle.trans ?_
  cases N with
  | zero => simp
  | succ M =>
    rw [tail_sum_Icc M]
    have : (0 : ℝ) ≤ 1 / ((M : ℝ) + 1) := by positivity
    linarith

/-- **Log-tail bound.**  Summing `log((1 - 1/p)⁻¹) = −log(1 − 1/p)` over primes
`p ≤ N` exceeds `Σ 1/p` by at most `1`, because per prime
`log((1 − 1/p)⁻¹) ≤ (1 − 1/p)⁻¹ − 1 = 1/(p−1) = 1/p + 1/(p(p−1))`
(Mathlib `Real.log_le_sub_one_of_pos`) and `Σ_p 1/(p(p−1)) ≤ 1`. -/
lemma sum_log_euler_factor_le (N : ℕ) :
    ∑ p ∈ primesLe N, Real.log ((1 - 1 / (p : ℝ))⁻¹) ≤
      (∑ p ∈ primesLe N, (1 / (p : ℝ))) + 1 := by
  have hterm : ∀ p ∈ primesLe N,
      Real.log ((1 - 1 / (p : ℝ))⁻¹) ≤ 1 / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    intro p hp
    have hpp := (mem_primesLe.mp hp).2
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hpos : 0 < (1 - 1 / (p : ℝ))⁻¹ := euler_factor_pos hpp
    have hlog := Real.log_le_sub_one_of_pos hpos
    have hp0 : (p : ℝ) ≠ 0 := by positivity
    have hp1 : (p : ℝ) - 1 ≠ 0 := by
      have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      exact ne_of_gt this
    have hval : (1 - 1 / (p : ℝ))⁻¹ - 1 = 1 / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
      have hpne : (1 - 1 / (p : ℝ)) ≠ 0 := by
        have : (0 : ℝ) < 1 - 1 / (p : ℝ) := by
          have : 1 / (p : ℝ) ≤ 1 / 2 := by
            apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp2
          linarith
        exact ne_of_gt this
      field_simp
      ring
    rw [hval] at hlog
    exact hlog
  calc ∑ p ∈ primesLe N, Real.log ((1 - 1 / (p : ℝ))⁻¹)
      ≤ ∑ p ∈ primesLe N, (1 / (p : ℝ) + 1 / ((p : ℝ) * ((p : ℝ) - 1))) :=
        Finset.sum_le_sum hterm
    _ = (∑ p ∈ primesLe N, (1 / (p : ℝ))) +
          ∑ p ∈ primesLe N, (1 : ℝ) / ((p : ℝ) * ((p : ℝ) - 1)) := by
        rw [Finset.sum_add_distrib]
    _ ≤ (∑ p ∈ primesLe N, (1 / (p : ℝ))) + 1 := by
        gcongr
        exact tail_bound N

/-! ## Main result: Mertens lower bound -/

/-- **Mertens' lower bound.**  For all `N ≥ 1`,
`Σ_{p ≤ N} 1/p ≥ log log (N + 1) − 1`.  This exhibits the `log log N` growth
rate of the prime reciprocal sum (the lower half of Mertens' second theorem),
answering the lower-bound direction of erdos-31 OQ-03. -/
theorem mertens_reciprocal_lower_bound (N : ℕ) (hN : 1 ≤ N) :
    Real.log (Real.log ((N : ℝ) + 1)) - 1 ≤ ∑ p ∈ primesLe N, (1 / (p : ℝ)) := by
  -- log(N+1) > 0 since N + 1 ≥ 2
  have hNR : (2 : ℝ) ≤ (N : ℝ) + 1 := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have hlogpos : 0 < Real.log ((N : ℝ) + 1) :=
    Real.log_pos (by linarith)
  -- Step A: log(N+1) ≤ harmonic N = ∑_{k=1}^N 1/k
  have hHarm : Real.log ((N : ℝ) + 1) ≤ ∑ k ∈ Finset.Icc 1 N, (1 / k : ℝ) := by
    have h := log_add_one_le_harmonic N
    have hcast : ((harmonic N : ℚ) : ℝ) = ∑ k ∈ Finset.Icc 1 N, (1 / k : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp only [one_div]
    calc Real.log ((N : ℝ) + 1)
        = Real.log ((↑(N + 1) : ℝ)) := by push_cast; ring_nf
      _ ≤ ((harmonic N : ℚ) : ℝ) := h
      _ = ∑ k ∈ Finset.Icc 1 N, (1 / k : ℝ) := hcast
  -- Step B: ∑ 1/k ≤ Euler product
  set P := ∏ p ∈ primesLe N, (1 - 1 / (p : ℝ))⁻¹ with hP
  have hProdPos : 0 < P := euler_product_pos N
  have hLeProd : Real.log ((N : ℝ) + 1) ≤ P :=
    le_trans hHarm (harmonic_le_euler_product N)
  -- Step C: take logs
  have hlogmono : Real.log (Real.log ((N : ℝ) + 1)) ≤ Real.log P :=
    Real.log_le_log hlogpos hLeProd
  -- Step D: log of product = sum of logs
  have hlogprod : Real.log P = ∑ p ∈ primesLe N, Real.log ((1 - 1 / (p : ℝ))⁻¹) := by
    rw [hP, Real.log_prod]
    intro p hp
    exact euler_factor_ne (mem_primesLe.mp hp).2
  -- Step E: bound by Σ 1/p + 1
  have hbound := sum_log_euler_factor_le N
  -- Assemble
  rw [hlogprod] at hlogmono
  linarith [hlogmono, hbound]

end Erdos31PrimesDensityReciprocal
