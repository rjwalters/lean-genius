/-
  Chebyshev θ-gap lower bound for Erdős Problem #490.

  This file works toward eliminating the analytic axiom
  `chebyshev_theta_upper_half_lower_bound` in `Erdos490Problem.lean`, namely
  `∃ c > 0, ∀ N ≥ 4, c·N ≤ θ(N) − θ(N/2)`.

  The combinatorial heart is the classical central-binomial decomposition
  (the same estimate that powers Mathlib's proof of Bertrand's postulate):
  the prime factorisation of `centralBinom n = C(2n, n)` splits into
    * small primes `p ≤ 2n/3`, contributing at most `(2n)^√(2n) · 4^(2n/3)`, and
    * large primes `n < p ≤ 2n`, contributing exactly `∏_{n < p ≤ 2n} p`,
  with the middle band `(2n/3, n]` contributing nothing.  Hence
    `centralBinom n ≤ (2n)^√(2n) · 4^(2n/3) · ∏_{n < p ≤ 2n} p`.
  Combined with the standard lower bound `4^n < n · centralBinom n`, this yields
  a lower bound on `∏_{n < p ≤ 2n} p`, whose logarithm is the θ-gap.
-/
import Mathlib

open Finset

namespace Erdos490Cheb

open Nat

/-- **Small-prime contribution bound.** The primes `p ≤ 2n/3` contribute at most
`(2n)^√(2n) · 4^(2n/3)` to `centralBinom n`.  This is exactly the estimate inside
Mathlib's `Nat.centralBinom_le_of_no_bertrand_prime`, extracted as a standalone lemma
(the Bertrand proof only needs it under a "no large prime" hypothesis; we keep the large
primes as a separate factor). -/
lemma small_prime_prod_le (n : ℕ) (hn : 0 < n) :
    ∏ p ∈ {p ∈ range (2 * n / 3 + 1) | p.Prime}, p ^ (n.centralBinom.factorization p)
      ≤ (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) := by
  have n2_pos : 1 ≤ 2 * n := by omega
  let S := {p ∈ range (2 * n / 3 + 1) | p.Prime}
  let f : ℕ → ℕ := fun x => x ^ n.centralBinom.factorization x
  show ∏ p ∈ S, f p ≤ (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3)
  rw [← Finset.prod_filter_mul_prod_filter_not S (· ≤ Nat.sqrt (2 * n))]
  apply mul_le_mul'
  · -- primes `≤ √(2n)`: each contributes `≤ 2n`, and there are `≤ √(2n)` of them.
    refine (Finset.prod_le_prod' fun p _ => (?_ : f p ≤ 2 * n)).trans ?_
    · exact pow_factorization_choose_le (mul_pos two_pos hn)
    have hcard : (Finset.Icc 1 (Nat.sqrt (2 * n))).card = Nat.sqrt (2 * n) := by
      rw [Nat.card_Icc]; omega
    rw [Finset.prod_const]
    refine pow_right_mono₀ n2_pos ((Finset.card_le_card fun x hx => ?_).trans hcard.le)
    obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hx
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_filter.1 h1).2.one_lt.le, h2⟩
  · -- primes `√(2n) < p ≤ 2n/3`: each has multiplicity `≤ 1`, product `≤ primorial ≤ 4^(2n/3)`.
    refine le_trans ?_ (primorial_le_4_pow (2 * n / 3))
    refine (Finset.prod_le_prod' fun p hp => (?_ : f p ≤ p)).trans ?_
    · obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hp
      refine (pow_right_mono₀ (Finset.mem_filter.1 h1).2.one_lt.le ?_).trans (pow_one p).le
      exact Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp <| not_le.1 h2)
    refine Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _) ?_
    exact fun p hp _ => (Finset.mem_filter.1 hp).2.one_lt.le

/-- **Central-binomial decomposition (the combinatorial crux).**
The prime factorisation of `centralBinom n` splits so that the primes `p ≤ 2n/3`
contribute at most `(2n)^√(2n) · 4^(2n/3)` (see `small_prime_prod_le`), the primes in
`(2n/3, n]` contribute nothing, and the large primes `n < p ≤ 2n` contribute at most
`∏_{n < p ≤ 2n} p`.  Hence
`centralBinom n ≤ (2n)^√(2n) · 4^(2n/3) · ∏_{n < p ≤ 2n, p prime} p`. -/
theorem centralBinom_le_small_mul_large (n : ℕ) (hn : 2 < n) :
    n.centralBinom ≤
      (2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) *
        ∏ p ∈ {p ∈ range (2 * n + 1) | n < p ∧ p.Prime}, p := by
  have hn0 : 0 < n := by omega
  rw [← Nat.prod_pow_factorization_centralBinom n,
    ← Finset.prod_filter_mul_prod_filter_not (range (2 * n + 1)) (· ≤ n)
        (fun x => x ^ n.centralBinom.factorization x)]
  apply mul_le_mul'
  · -- small + middle band: reduces to the primes `≤ 2n/3`
    have hSsub : {p ∈ range (2 * n / 3 + 1) | p.Prime}
        ⊆ (range (2 * n + 1)).filter (· ≤ n) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
      exact ⟨by omega, by omega⟩
    have hone : ∀ x ∈ (range (2 * n + 1)).filter (· ≤ n),
        x ∉ {p ∈ range (2 * n / 3 + 1) | p.Prime} →
        x ^ n.centralBinom.factorization x = 1 := by
      intro x hx hxnot
      simp only [Finset.mem_filter, Finset.mem_range] at hx hxnot
      by_cases hxp : x.Prime
      · have hgt : 2 * n / 3 < x := by
          by_contra h; push_neg at h
          exact hxnot ⟨by omega, hxp⟩
        rw [Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hn (by omega) (by omega),
          pow_zero]
      · rw [Nat.factorization_eq_zero_of_not_prime _ hxp, pow_zero]
    rw [← Finset.prod_subset hSsub hone]
    exact small_prime_prod_le n hn0
  · -- large primes: multiplicity `≤ 1`, so `p ^ v_p ≤ p`
    have hLsub : {p ∈ range (2 * n + 1) | n < p ∧ p.Prime}
        ⊆ (range (2 * n + 1)).filter (fun x => ¬ x ≤ n) := by
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_range] at hp ⊢
      exact ⟨hp.1, by omega⟩
    have hone : ∀ x ∈ (range (2 * n + 1)).filter (fun x => ¬ x ≤ n),
        x ∉ {p ∈ range (2 * n + 1) | n < p ∧ p.Prime} →
        x ^ n.centralBinom.factorization x = 1 := by
      intro x hx hxnot
      simp only [Finset.mem_filter, Finset.mem_range] at hx hxnot
      have hnx : n < x := by omega
      have hxp : ¬ x.Prime := fun hp => hxnot ⟨hx.1, hnx, hp⟩
      rw [Nat.factorization_eq_zero_of_not_prime _ hxp, pow_zero]
    rw [← Finset.prod_subset hLsub hone]
    refine Finset.prod_le_prod' ?_
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_range] at hp
    obtain ⟨_, hnp, hpp⟩ := hp
    have hv1 : n.centralBinom.factorization p ≤ 1 := by
      have hp2 : 2 * n < p ^ 2 := by nlinarith [hnp]
      exact Nat.factorization_choose_le_one hp2
    calc p ^ n.centralBinom.factorization p
        ≤ p ^ 1 := Nat.pow_le_pow_right hpp.pos hv1
      _ = p := pow_one p

/-- **Lower bound on the large-prime product (nat).** Combining the decomposition with the
standard exponential lower bound `4^n < n · centralBinom n` gives an exponential lower bound
on `∏_{n < p ≤ 2n} p` (up to the sub-exponential factor `n · (2n)^√(2n) · 4^(2n/3)`). -/
theorem four_pow_lt_bound (n : ℕ) (hn : 4 ≤ n) :
    4 ^ n < n * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3)) *
      ∏ p ∈ {p ∈ range (2 * n + 1) | n < p ∧ p.Prime}, p := by
  have h1 : 4 ^ n < n * n.centralBinom := Nat.four_pow_lt_mul_centralBinom n hn
  have h2 := centralBinom_le_small_mul_large n (by omega)
  have h3 : n * n.centralBinom
      ≤ n * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3) *
          ∏ p ∈ {p ∈ range (2 * n + 1) | n < p ∧ p.Prime}, p) :=
    Nat.mul_le_mul le_rfl h2
  rw [← mul_assoc] at h3
  exact lt_of_lt_of_le h1 h3

/-- **The θ-gap equals the log of the large-prime product.** Since `θ x = ∑_{p ≤ x} log p`,
the difference `θ(2n) − θ(n)` sums `log p` over the primes `p ∈ (n, 2n]`, i.e. exactly the
`large` product used above.  (Mirror of `theta_gap_eq_sum_optimalB` in the main file, for the
interval `(n, 2n]`.) -/
theorem theta_gap_eq_log_prod (n : ℕ) :
    Chebyshev.theta ((2 * n : ℕ) : ℝ) - Chebyshev.theta ((n : ℕ) : ℝ)
      = Real.log ((∏ p ∈ {p ∈ range (2 * n + 1) | n < p ∧ p.Prime}, p : ℕ) : ℝ) := by
  have e1 : Chebyshev.theta ((2 * n : ℕ) : ℝ)
      = ∑ p ∈ {p ∈ Finset.Ioc 0 (2 * n) | p.Prime}, Real.log (p : ℝ) := by
    simp only [Chebyshev.theta, Nat.floor_natCast]
  have e2 : Chebyshev.theta ((n : ℕ) : ℝ)
      = ∑ p ∈ {p ∈ Finset.Ioc 0 n | p.Prime}, Real.log (p : ℝ) := by
    simp only [Chebyshev.theta, Nat.floor_natCast]
  have hsub : {p ∈ Finset.Ioc 0 n | p.Prime} ⊆ {p ∈ Finset.Ioc 0 (2 * n) | p.Prime} :=
    Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right (by omega))
  have hset : {p ∈ Finset.Ioc 0 (2 * n) | p.Prime} \ {p ∈ Finset.Ioc 0 n | p.Prime}
      = {p ∈ range (2 * n + 1) | n < p ∧ p.Prime} := by
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_range]
    constructor
    · rintro ⟨⟨⟨hp0, hp2n⟩, hpr⟩, hnot⟩
      refine ⟨by omega, ?_, hpr⟩
      by_contra h; push_neg at h; exact hnot ⟨⟨hp0, by omega⟩, hpr⟩
    · rintro ⟨_, hnp, hpr⟩
      exact ⟨⟨⟨hpr.pos, by omega⟩, hpr⟩, by rintro ⟨⟨_, h2⟩, _⟩; omega⟩
  rw [e1, e2, ← Finset.sum_sdiff_eq_sub hsub, hset, Nat.cast_prod]
  refine (Real.log_prod (fun p hp => ?_)).symm
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  exact_mod_cast hp.2.2.pos.ne'

/-- **Chebyshev θ-gap lower bound, reduced to an elementary expression (0 axioms, 0 sorries).**
For `n ≥ 4`,
`θ(2n) − θ(n) ≥ n·log 4 − ⌊2n/3⌋·log 4 − log n − √(2n)·log(2n)`
where `√` is `Nat.sqrt`.  The right-hand side is `≥ (n/3)·log 4 − log n − √(2n)·log(2n)`, which is
`≥ c·n` for all large `n` since `log n` and `√(2n)·log(2n)` are `o(n)`.  This is the classical
Chebyshev-strength lower bound, whose analytic tail (`√n·log n = o(n)`) and small-`n` reconciliation
(via Bertrand) are the only remaining steps to fully eliminate the axiom
`chebyshev_theta_upper_half_lower_bound` in `Erdos490Problem.lean`. -/
theorem theta_gap_lower_bound (n : ℕ) (hn : 4 ≤ n) :
    (n : ℝ) * Real.log 4 - ((2 * n / 3 : ℕ) : ℝ) * Real.log 4 - Real.log (n : ℝ)
        - (Nat.sqrt (2 * n) : ℝ) * Real.log (2 * (n : ℝ))
      ≤ Chebyshev.theta ((2 * n : ℕ) : ℝ) - Chebyshev.theta ((n : ℕ) : ℝ) := by
  rw [theta_gap_eq_log_prod]
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have h2n : (0 : ℝ) < 2 * (n : ℝ) := by linarith
  have hsmall_pos : (0 : ℝ) < (2 * (n : ℝ)) ^ Nat.sqrt (2 * n) * (4 : ℝ) ^ (2 * n / 3) :=
    mul_pos (pow_pos h2n _) (pow_pos (by norm_num) _)
  have hPpos : (0 : ℝ) < ((∏ p ∈ {p ∈ range (2 * n + 1) | n < p ∧ p.Prime}, p : ℕ) : ℝ) := by
    rw [Nat.cast_pos]
    exact Finset.prod_pos fun p hp => by
      simp only [Finset.mem_filter, Finset.mem_range] at hp; exact hp.2.2.pos
  have hnat : 4 ^ n < n * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3)) *
      ∏ p ∈ {p ∈ range (2 * n + 1) | n < p ∧ p.Prime}, p := four_pow_lt_bound n hn
  have hcast : (4 : ℝ) ^ n < (n : ℝ) *
      ((2 * (n : ℝ)) ^ Nat.sqrt (2 * n) * (4 : ℝ) ^ (2 * n / 3)) *
      ((∏ p ∈ {p ∈ range (2 * n + 1) | n < p ∧ p.Prime}, p : ℕ) : ℝ) := by
    have : ((4 ^ n : ℕ) : ℝ) < ((n * ((2 * n) ^ Nat.sqrt (2 * n) * 4 ^ (2 * n / 3)) *
        ∏ p ∈ {p ∈ range (2 * n + 1) | n < p ∧ p.Prime}, p : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at this ⊢
    linarith [this]
  have hlog : Real.log ((4 : ℝ) ^ n) < Real.log ((n : ℝ) *
      ((2 * (n : ℝ)) ^ Nat.sqrt (2 * n) * (4 : ℝ) ^ (2 * n / 3)) *
      ((∏ p ∈ {p ∈ range (2 * n + 1) | n < p ∧ p.Prime}, p : ℕ) : ℝ)) :=
    Real.log_lt_log (by positivity) hcast
  rw [Real.log_pow,
    Real.log_mul (mul_ne_zero (ne_of_gt hnR) (ne_of_gt hsmall_pos)) (ne_of_gt hPpos),
    Real.log_mul (ne_of_gt hnR) (ne_of_gt hsmall_pos),
    Real.log_mul (ne_of_gt (pow_pos h2n _)) (ne_of_gt (pow_pos (by norm_num : (0:ℝ) < 4) _)),
    Real.log_pow, Real.log_pow] at hlog
  linarith [hlog]

open Real Filter Asymptotics in
/-- **Analytic tail (0 axioms, 0 sorries).** The elementary lower bound supplied by
`theta_gap_lower_bound` eventually dominates a positive multiple of `n`:
`(n/3)·log 4 − log n − √(2n)·log(2n) ≥ (log 4 / 6)·n` for all large `n`, because both
`log n` and `√(2n)·log(2n)` are `o(n)` (`Real.isLittleO_log_id_atTop` and
`isLittleO_log_rpow_atTop` with exponent `1/2`).  This is the single remaining analytic
input needed to turn the axiom `chebyshev_theta_upper_half_lower_bound` in
`Erdos490Problem.lean` into a theorem.  Stated with the *real* `√` and `2n/3`; the nat
floor `⌊2n/3⌋` and `Nat.sqrt (2n)` of `theta_gap_lower_bound` only make its RHS larger, so
this real bound lower-bounds it directly. -/
theorem erdos490_analytic_tail :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      c * (n : ℝ) ≤ (n : ℝ) * Real.log 4 - (2 * (n : ℝ) / 3) * Real.log 4
        - Real.log (n : ℝ) - Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ)) := by
  have hL : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  -- `log n = o(n)`: eventually `log x ≤ (log 4 / 12)·x`.
  have hE1 : ∀ᶠ x : ℝ in atTop, Real.log x ≤ (Real.log 4 / 12) * x := by
    have h := (isLittleO_iff.mp Real.isLittleO_log_id_atTop)
      (show (0 : ℝ) < Real.log 4 / 12 by positivity)
    filter_upwards [h, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hlog : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
    have hx0 : (0 : ℝ) ≤ x := by linarith
    simpa [id_eq, Real.norm_of_nonneg hlog, Real.norm_of_nonneg hx0] using hx
  -- `√x·log x = o(x)`: eventually `√x · log x ≤ (log 4 / 24)·x`.
  have hE2 : ∀ᶠ x : ℝ in atTop, Real.sqrt x * Real.log x ≤ (Real.log 4 / 24) * x := by
    have hlo : (Real.log) =o[atTop] (fun x : ℝ => x ^ (1 / 2 : ℝ)) :=
      isLittleO_log_rpow_atTop (by norm_num)
    have h := (isLittleO_iff.mp hlo) (show (0 : ℝ) < Real.log 4 / 24 by positivity)
    filter_upwards [h, Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hx0 : (0 : ℝ) ≤ x := by linarith
    have hlog : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx1
    have hrp : (0 : ℝ) ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg hx0 _
    rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg hrp] at hx
    have hsqrt : Real.sqrt x = x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow x
    calc Real.sqrt x * Real.log x
        ≤ Real.sqrt x * ((Real.log 4 / 24) * x ^ (1 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_left hx (Real.sqrt_nonneg x)
      _ = (Real.log 4 / 24) * (Real.sqrt x * x ^ (1 / 2 : ℝ)) := by ring
      _ = (Real.log 4 / 24) * x := by rw [← hsqrt, Real.mul_self_sqrt hx0]
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.mp hE1
  obtain ⟨X2, hX2⟩ := Filter.eventually_atTop.mp hE2
  refine ⟨Real.log 4 / 6, by positivity, ⌈max X1 X2⌉₊, ?_⟩
  intro n hn
  have hnR : max X1 X2 ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
  have hn1 : X1 ≤ (n : ℝ) := le_trans (le_max_left _ _) hnR
  have hn2 : X2 ≤ 2 * (n : ℝ) := by
    have := le_trans (le_max_right _ _) hnR; linarith
  have e1 := hX1 (n : ℝ) hn1
  have e2 := hX2 (2 * (n : ℝ)) hn2
  nlinarith [e1, e2, hL]

/-- **Chebyshev θ-gap: eventual linear lower bound (0 axioms, 0 sorries).**
The two hard halves are now in place — the combinatorial central-binomial estimate
`theta_gap_lower_bound` (`θ(2n) − θ(n) ≥ n·log4 − ⌊2n/3⌋·log4 − log n − √(2n)·log(2n)`,
with nat `⌊·⌋` and `Nat.sqrt`) and the analytic tail `erdos490_analytic_tail`
(`c·n ≤ n·log4 − (2n/3)·log4 − log n − √(2n)·log(2n)` eventually). Combining them gives
the Chebyshev-strength statement in clean form:

  `∃ c > 0, ∀ large n,  c·n ≤ θ(2n) − θ(n).`

The bridge is a term-by-term comparison: `⌊2n/3⌋ ≤ 2n/3` (`Nat.cast_div_le`) and
`Nat.sqrt (2n) ≤ √(2n)` (`Real.nat_sqrt_le_real_sqrt`), both multiplied by nonnegative
logs, so the *nat* right-hand side of `theta_gap_lower_bound` is at least the *real*
right-hand side of `erdos490_analytic_tail`. Hence `c·n ≤ (real RHS) ≤ (nat RHS) ≤
θ(2n) − θ(n)`. Only the reindexing `(2n, n) ↦ (N, ⌊N/2⌋)` and a finite small-`N`
reconciliation (a prime in `(N/2, N]` by Bertrand) now separate this from the axiom
`chebyshev_theta_upper_half_lower_bound` in `Erdos490Problem.lean`. -/
theorem theta_gap_ge_linear :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
      c * (n : ℝ) ≤ Chebyshev.theta ((2 * n : ℕ) : ℝ) - Chebyshev.theta ((n : ℕ) : ℝ) := by
  obtain ⟨c, hc, N₀, hN₀⟩ := erdos490_analytic_tail
  refine ⟨c, hc, max N₀ 4, fun n hn => ?_⟩
  have hn4 : 4 ≤ n := le_trans (le_max_right _ _) hn
  have hnN0 : N₀ ≤ n := le_trans (le_max_left _ _) hn
  -- analytic tail: `c·n ≤ (real RHS)`
  have htail := hN₀ n hnN0
  -- combinatorial bound: `(nat RHS) ≤ θ(2n) − θ(n)`
  have hgap := theta_gap_lower_bound n hn4
  -- bridge: `(real RHS) ≤ (nat RHS)`, since the nat floors only enlarge the RHS
  have hnpos : 1 ≤ n := by omega
  have hL : (0 : ℝ) ≤ Real.log 4 := (Real.log_pos (by norm_num)).le
  have hlog2n : (0 : ℝ) ≤ Real.log (2 * (n : ℝ)) := by
    apply Real.log_nonneg
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnpos
    linarith
  have hfloor : ((2 * n / 3 : ℕ) : ℝ) ≤ 2 * (n : ℝ) / 3 := by
    have h := Nat.cast_div_le (α := ℝ) (m := 2 * n) (n := 3)
    push_cast at h
    linarith
  have hsqrt : (Nat.sqrt (2 * n) : ℝ) ≤ Real.sqrt (2 * (n : ℝ)) := by
    rw [show (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ) by push_cast; ring]
    exact Real.nat_sqrt_le_real_sqrt
  have t1 : ((2 * n / 3 : ℕ) : ℝ) * Real.log 4 ≤ (2 * (n : ℝ) / 3) * Real.log 4 :=
    mul_le_mul_of_nonneg_right hfloor hL
  have t2 : (Nat.sqrt (2 * n) : ℝ) * Real.log (2 * (n : ℝ))
      ≤ Real.sqrt (2 * (n : ℝ)) * Real.log (2 * (n : ℝ)) :=
    mul_le_mul_of_nonneg_right hsqrt hlog2n
  linarith [htail, hgap, t1, t2]

end Erdos490Cheb

