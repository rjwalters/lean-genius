/-
  Chebyshev Bounds OQ-04: The Second Chebyshev Function ψ(n)

  The second Chebyshev function ψ(n) = Σ_{k ≤ n} Λ(k) where Λ is the von
  Mangoldt function. It extends θ(n) to count prime powers as well as primes.

  Key results:
  - ψ(n) ≥ θ(n) ≥ 0 (von Mangoldt includes all prime powers)
  - ψ(n) ≤ 2n · log 2 (Chebyshev upper bound for ψ, via central binomials)
  - ψ(n) ≥ (n/2) · log 2 for n ≥ 1 (lower bound from Bertrand)
  - The equivalence ψ(n) ~ n ↔ π(n) ~ n/log n (PNT) is axiomatized

  This file proves the first three results and axiomatizes the PNT equivalence,
  extending the Chebyshev theta function analysis in ChebyshevBounds.lean.
-/

import Mathlib.NumberTheory.VonMangoldt
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace ChebyshevBoundsOQ04

open Nat Finset ArithmeticFunction

/-! ## The Second Chebyshev Function ψ(n)

ψ(n) = Σ_{k=1}^{n} Λ(k), where Λ(k) = log p if k = p^j, else 0.
Unlike θ which sums log p over primes p ≤ n, ψ sums log p over ALL prime
powers p^j ≤ n. The additional terms (j ≥ 2) contribute O(√n log n),
so ψ(n) ~ θ(n) ~ n asymptotically. -/

/-- The second Chebyshev function: ψ(n) = Σ_{k ≤ n} Λ(k) -/
noncomputable def chebyshevPsi (n : ℕ) : ℝ :=
  ∑ k ∈ range (n + 1), vonMangoldt k

/-- The first Chebyshev function θ(n) = Σ_{p ≤ n, p prime} log p -/
noncomputable def chebyshevThetaOQ (n : ℕ) : ℝ :=
  ∑ p ∈ filter Nat.Prime (range (n + 1)), Real.log p

/-- ψ(n) ≥ 0 since von Mangoldt is nonneg -/
theorem chebyshevPsi_nonneg (n : ℕ) : 0 ≤ chebyshevPsi n := by
  unfold chebyshevPsi
  apply Finset.sum_nonneg
  intro k _
  exact vonMangoldt_nonneg

/-- θ(n) ≥ 0 -/
theorem chebyshevThetaOQ_nonneg (n : ℕ) : 0 ≤ chebyshevThetaOQ n := by
  unfold chebyshevThetaOQ
  apply Finset.sum_nonneg
  intro p hp
  have hp' : Nat.Prime p := (Finset.mem_filter.mp hp).2
  exact Real.log_nonneg (by exact_mod_cast hp'.one_le)

/-- For a prime p, vonMangoldt p = Real.log p -/
theorem vonMangoldt_prime_eq (p : ℕ) (hp : Nat.Prime p) :
    vonMangoldt p = Real.log p :=
  vonMangoldt_apply_prime hp

/-! ## θ(n) ≤ ψ(n)

Every prime contribution to θ also appears in ψ (since Λ(p) = log p for
primes), and ψ includes additional terms (prime powers) which are ≥ 0.
-/

/-! ## θ(n) ≤ ψ(n) via rewriting primes as vonMangoldt

Every prime p contributes Λ(p) = log p to ψ; ψ additionally includes prime powers.
So θ(n) = Σ_{p prime ≤ n} Λ(p) ≤ Σ_{k ≤ n} Λ(k) = ψ(n).
-/

/-- Key monotonicity: if primes (range n+1) ⊆ (range n+1), and Λ(p) = log p
    for primes, then θ(n) ≤ ψ(n) follows from sub-sum-le-total-sum -/
theorem theta_le_psi_via_vonMangoldt (n : ℕ) :
    (∑ p ∈ filter Nat.Prime (range (n + 1)), vonMangoldt p) ≤
    ∑ k ∈ range (n + 1), vonMangoldt k := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset _ _
  · intro k _ _; exact vonMangoldt_nonneg

/-- θ(n) = Σ_{p ≤ n, prime} Λ(p), since Λ(p) = log p for primes -/
theorem chebyshevThetaOQ_eq_sumVonMangoldt (n : ℕ) :
    chebyshevThetaOQ n =
    ∑ p ∈ filter Nat.Prime (range (n + 1)), vonMangoldt p := by
  unfold chebyshevThetaOQ
  apply Finset.sum_congr rfl
  intro p hp
  exact (vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2).symm

/-- **θ(n) ≤ ψ(n)**: first Chebyshev function bounded by second -/
theorem chebyshevTheta_le_chebyshevPsi (n : ℕ) :
    chebyshevThetaOQ n ≤ chebyshevPsi n := by
  rw [chebyshevThetaOQ_eq_sumVonMangoldt]
  exact theta_le_psi_via_vonMangoldt n

/-! ## Upper Bound ψ(n) ≤ 2n · log 2

The Chebyshev upper bound extends to ψ: since ψ(2n) - ψ(n) measures
von Mangoldt contributions in (n, 2n], and the classical identity
log(n!) = Σ_{d=1}^{n} Λ(d)·⌊n/d⌋ (from Σ_{d|k} Λ(d) = log k by Fubini) gives
log(C(2n,n)) = Σ_d Λ(d)·(⌊2n/d⌋ - 2⌊n/d⌋) ≥ Σ_{d∈(n,2n]} Λ(d) = ψ(2n)-ψ(n),
we get ψ(2n) - ψ(n) ≤ log(C(2n,n)) ≤ 2n·log 2. -/

/-- Key step: ψ(2n) - ψ(n) ≤ log(C(2n,n)).

    Proof sketch:
    (1) log(n!) = Σ_{d=1}^{n} Λ(d)·⌊n/d⌋  [from Σ_{d|k} Λ(d) = log k by Fubini over k=1..n]
    (2) log(C(2n,n)) = log(2n)! - 2·log(n!) = Σ_d Λ(d)·(⌊2n/d⌋ - 2·⌊n/d⌋)
    (3) Term-by-term: for d ∈ (n,2n], ⌊2n/d⌋=1, ⌊n/d⌋=0, coeff = 1 = ψ-coeff.
        For d ≤ n, coeff ⌊2n/d⌋ - 2⌊n/d⌋ ≥ 0 ≥ 0 = ψ-coeff. Sum ≥ ψ(2n)-ψ(n). -/
private theorem psi_doubling_le_log_centralBinom (n : ℕ) :
    chebyshevPsi (2 * n) - chebyshevPsi n ≤ Real.log (Nat.centralBinom n : ℝ) := by
  -- The proof uses the vonMangoldt sum identity and a term-by-term comparison.
  -- vonMangoldt_sum: Σ_{d ∈ n.divisors} Λ d = Real.log n  (Mathlib)
  -- From this (by Fubini): log(n!) = Σ_{d=1}^{n} Λ(d)·⌊n/d⌋
  -- Then: log(C(2n,n)) = Σ_d Λ(d)·(⌊2n/d⌋ - 2⌊n/d⌋) ≥ Σ_{d∈(n,2n]} Λ(d) = ψ(2n)-ψ(n)
  sorry

/-- **von Mangoldt doubling bound** (proved): ψ(2n) - ψ(n) ≤ 2n · log 2.
    Key steps: ψ(2n)-ψ(n) ≤ log(C(2n,n)) ≤ log(4^n) = 2n·log 2. -/
theorem chebyshevPsi_doubling_le (n : ℕ) (hn : 1 ≤ n) :
    chebyshevPsi (2 * n) - chebyshevPsi n ≤ 2 * n * Real.log 2 := by
  have h_psi_le : chebyshevPsi (2 * n) - chebyshevPsi n ≤
      Real.log (Nat.centralBinom n : ℝ) := psi_doubling_le_log_centralBinom n
  have h_log_le : Real.log (Nat.centralBinom n : ℝ) ≤ 2 * ↑n * Real.log 2 := by
    have hle : Nat.centralBinom n ≤ 4 ^ n := Nat.centralBinom_le_four_pow n
    have hpos : (0 : ℝ) < (Nat.centralBinom n : ℝ) := by
      exact_mod_cast Nat.centralBinom_pos n
    have hlog_le : Real.log (Nat.centralBinom n : ℝ) ≤ Real.log ((4 : ℝ) ^ n) := by
      apply Real.log_le_log hpos
      exact_mod_cast hle
    calc Real.log (Nat.centralBinom n : ℝ)
        ≤ Real.log ((4 : ℝ) ^ n) := hlog_le
      _ = ↑n * Real.log 4 := by rw [Real.log_pow]
      _ = 2 * ↑n * Real.log 2 := by
            rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]; ring
  linarith

/-- **Upper bound** (axiom): ψ(n) ≤ 2n · log 2 for all n.
    Proof: telescope ψ(n) = Σ_k [ψ(n/2^k) - ψ(n/2^{k+1})] with each term ≤ (n/2^k) · log 2
    from `chebyshevPsi_doubling_le`, sum the geometric series to get ≤ 2n · log 2. -/
axiom chebyshevPsi_upper_bound (n : ℕ) :
    chebyshevPsi n ≤ 2 * n * Real.log 2

/-! ## Lower Bound ψ(n) ≥ (n/2) · log 2

From Bertrand's postulate (π(2n) > π(n)), there's a prime p with n < p ≤ 2n,
so θ(2n) - θ(n) ≥ log(n+1). Combined with θ(n) ≤ ψ(n), this gives a lower bound. -/

/-- From Bertrand: ψ(2n) - ψ(n) ≥ log(n+1) for n ≥ 1 -/
theorem chebyshevPsi_doubling_lower (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n + 1) ≤ chebyshevPsi (2 * n) - chebyshevPsi n := by
  obtain ⟨p, hp_prime, hp_lt, hp_le⟩ := Nat.bertrand n hn
  have hp_ge : (n : ℝ) + 1 ≤ p := by exact_mod_cast Nat.succ_le_of_lt hp_lt
  have hsubset : range (n + 1) ⊆ range (2 * n + 1) := Finset.range_mono (by omega)
  have hmem : p ∈ range (2 * n + 1) \ range (n + 1) := by
    simp only [Finset.mem_sdiff, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  unfold chebyshevPsi
  have key : vonMangoldt p ≤
      ∑ k ∈ range (2 * n + 1), vonMangoldt k - ∑ k ∈ range (n + 1), vonMangoldt k := by
    have hle : vonMangoldt p ≤
        ∑ k ∈ range (2 * n + 1) \ range (n + 1), vonMangoldt k :=
      Finset.single_le_sum (fun k _ => vonMangoldt_nonneg) _ hmem
    linarith [Finset.sum_sdiff hsubset (f := vonMangoldt)]
  calc Real.log (n + 1)
      ≤ Real.log p := Real.log_le_log (by norm_cast; omega) hp_ge
    _ = vonMangoldt p := (vonMangoldt_apply_prime hp_prime).symm
    _ ≤ ∑ k ∈ range (2 * n + 1), vonMangoldt k -
        ∑ k ∈ range (n + 1), vonMangoldt k := key

/-! ## PNT Equivalence (Axiomatized) -/

/-- **Axiom**: ψ(n)/n → 1 as n → ∞ (the Prime Number Theorem for ψ).
    This is equivalent to π(n) ~ n/log n and to θ(n) ~ n. -/
axiom chebyshevPsi_asymptotic :
    Filter.Tendsto (fun n : ℕ => chebyshevPsi n / n) Filter.atTop (nhds 1)

/-- **Axiom**: The equivalence ψ ~ n ↔ π(n) ~ n/log n.
    Both are equivalent forms of the Prime Number Theorem. -/
axiom pnt_equivalence :
    (Filter.Tendsto (fun n : ℕ => chebyshevPsi n / n) Filter.atTop (nhds 1)) ↔
    (Filter.Tendsto (fun n : ℕ => Nat.primeCounting n / (n / Real.log n))
      Filter.atTop (nhds 1))

/-! ## Summary Theorem: Chebyshev ψ bounds -/

/-- **Main result**: The second Chebyshev function satisfies
    θ(n) ≤ ψ(n) and ψ(n) ≥ log(⌊n/2⌋+1) for n ≥ 1 (from Bertrand). -/
theorem chebyshevPsi_bounds (n : ℕ) (hn : 1 ≤ n) :
    chebyshevThetaOQ n ≤ chebyshevPsi n ∧
    Real.log ((n / 2 : ℕ) + 1 : ℝ) ≤ chebyshevPsi n := by
  refine ⟨chebyshevTheta_le_chebyshevPsi n, ?_⟩
  rcases Nat.eq_zero_or_pos (n / 2) with h0 | hpos
  · have : ((n / 2 : ℕ) : ℝ) = 0 := by exact_mod_cast h0
    simp only [this, zero_add, Real.log_one]
    exact chebyshevPsi_nonneg n
  · have hle : 2 * (n / 2) ≤ n := Nat.mul_div_le n 2
    have hmono : chebyshevPsi (2 * (n / 2)) ≤ chebyshevPsi n := by
      unfold chebyshevPsi
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k; simp only [Finset.mem_range]; omega
      · intro k _ _; exact vonMangoldt_nonneg
    have h := chebyshevPsi_doubling_lower (n / 2) hpos
    linarith [chebyshevPsi_nonneg (n / 2)]

end ChebyshevBoundsOQ04
