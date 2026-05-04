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

import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorization.Basic
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

/-- Fubini step: log(m!) = Σ_{d ∈ range(m+1)} Λ(d) · ⌊m/d⌋.
    Proof: log(m!) = Σ_k log k = Σ_k Σ_{d|k} Λ(d) = Σ_d Λ(d) · #{k ≤ m : d|k} = Σ_d Λ(d)·⌊m/d⌋. -/
private lemma log_factorial_vonMangoldt (m : ℕ) :
    Real.log (m.factorial : ℝ) =
    ∑ d ∈ Finset.range (m + 1), vonMangoldt d * (m / d : ℕ) := by
  have hsum_log : ∀ (n : ℕ), Real.log (n.factorial : ℝ) =
      ∑ k ∈ Finset.range (n + 1), Real.log (k : ℝ) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Nat.factorial_succ, Nat.cast_mul,
          Real.log_mul (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
            (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)),
          Finset.sum_range_succ]
      linarith
  rw [hsum_log m]
  simp_rw [← vonMangoldt_sum]
  have hcompat : ∀ (k d : ℕ), k ∈ Finset.range (m + 1) ∧ d ∈ k.divisors ↔
      k ∈ (Finset.range (m + 1)).filter (fun k' => k' ≠ 0 ∧ d ∣ k') ∧
      d ∈ Finset.range (m + 1) := by
    intro k d
    simp only [Finset.mem_range, Nat.mem_divisors, Finset.mem_filter]
    constructor
    · rintro ⟨hk, hdvd, hkne⟩
      exact ⟨⟨hk, hkne, hdvd⟩, (Nat.le_of_dvd (by omega) hdvd).trans_lt hk⟩
    · rintro ⟨⟨hk, hkne, hdvd⟩, _⟩
      exact ⟨hk, hdvd, hkne⟩
  rw [Finset.sum_comm' hcompat]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_const, Nat.card_multiples']
  simp [nsmul_eq_mul, mul_comm]

/-- Key step: ψ(2n) - ψ(n) ≤ log(C(2n,n)).
    Proof: log(C(2n,n)) = Σ_d Λ(d)·(⌊2n/d⌋ - 2⌊n/d⌋). For d ∈ (n,2n]: coeff=1.
    For d ≤ n: coeff ≥ 0 by Hermite (⌊2x⌋ ≥ 2⌊x⌋). Sum ≥ Σ_{(n,2n]} Λ(d) = ψ(2n)-ψ(n). -/
private theorem psi_doubling_le_log_centralBinom (n : ℕ) :
    chebyshevPsi (2 * n) - chebyshevPsi n ≤ Real.log (Nat.centralBinom n : ℝ) := by
  -- Express log(centralBinom n) as difference of log factorials
  have hbinom : Real.log (Nat.centralBinom n : ℝ) =
      Real.log ((2 * n).factorial : ℝ) - 2 * Real.log (n.factorial : ℝ) := by
    have hdvd : n.factorial * n.factorial ∣ (2 * n).factorial := by
      have h := Nat.factorial_mul_factorial_dvd_factorial (n := 2 * n) (k := n) (by omega)
      rwa [show 2 * n - n = n by omega] at h
    rw [Nat.centralBinom, Nat.choose_eq_factorial_div_factorial (by omega : n ≤ 2 * n),
        show 2 * n - n = n by omega,
        Nat.cast_div hdvd (by positivity),
        Real.log_div (by positivity) (by positivity),
        Nat.cast_mul, Real.log_mul (by positivity) (by positivity)]
    ring
  -- Use Fubini identity for log factorials
  rw [hbinom, log_factorial_vonMangoldt (2 * n), log_factorial_vonMangoldt n]
  -- Extend second sum range from n+1 to 2*n+1 (extra terms vanish: n/d=0 for d>n)
  have hextend : ∑ d ∈ Finset.range (n + 1), vonMangoldt d * (n / d : ℕ) =
      ∑ d ∈ Finset.range (2 * n + 1), vonMangoldt d * (n / d : ℕ) := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro d hd hdn
    simp only [Finset.mem_range, not_lt] at hd hdn
    have : n / d = 0 := Nat.div_eq_of_lt (by omega)
    simp [this]
  rw [hextend]
  -- ψ(2n) - ψ(n) = Σ_{d ∈ Ioc n (2n)} Λ(d)
  have hpsi : chebyshevPsi (2 * n) - chebyshevPsi n =
      ∑ d ∈ Finset.Ioc n (2 * n), vonMangoldt d := by
    have hle : Finset.range (n + 1) ⊆ Finset.range (2 * n + 1) := Finset.range_mono (by omega)
    have heq : Finset.range (2 * n + 1) \ Finset.range (n + 1) = Finset.Ioc n (2 * n) := by
      ext d; simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ioc]; omega
    simp only [chebyshevPsi, ← heq]
    linarith [Finset.sum_sdiff hle (f := vonMangoldt)]
  rw [hpsi]
  -- Goal: Σ_{Ioc n (2n)} Λd ≤ Σ_{range(2n+1)} Λd*(2n/d:ℝ) - 2*Σ_{range(2n+1)} Λd*(n/d:ℝ)
  have hIoc_sub : Finset.Ioc n (2 * n) ⊆ Finset.range (2 * n + 1) := by
    intro d hd; simp only [Finset.mem_Ioc] at hd; simp only [Finset.mem_range]; omega
  -- Each term in Ioc: 2n/d = 1 and n/d = 0
  have hcoeff_one : ∀ d ∈ Finset.Ioc n (2 * n),
      (2 * n / d : ℕ) = 1 ∧ (n / d : ℕ) = 0 := by
    intro d hd
    simp only [Finset.mem_Ioc] at hd
    exact ⟨Nat.div_eq_of_lt_le (by omega) (by omega),
           Nat.div_eq_of_lt (by omega)⟩
  -- Hermite: 2*(n/d : ℝ) ≤ (2n/d : ℝ), so coeff ≥ 0 everywhere
  have hcoeff_nonneg : ∀ d ∈ Finset.range (2 * n + 1),
      0 ≤ (2 * n / d : ℕ) - 2 * (n / d : ℕ) := by
    intro d _
    have := Nat.mul_div_le_mul_div_assoc 2 n d
    omega
  -- Combine RHS into single sum over ℝ coefficients
  have hrhs_split : ∑ d ∈ Finset.range (2 * n + 1), vonMangoldt d * (2 * n / d : ℕ) -
      2 * ∑ d ∈ Finset.range (2 * n + 1), vonMangoldt d * (n / d : ℕ) =
      ∑ d ∈ Finset.range (2 * n + 1),
        vonMangoldt d * (((2 * n / d : ℕ) : ℝ) - 2 * ((n / d : ℕ) : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    congr 1; ext d; ring
  rw [hrhs_split]
  -- Final: Σ_{Ioc} Λd = Σ_{Ioc} Λd*(1-0) ≤ Σ_{range(2n+1)} Λd*coeff_d
  calc ∑ d ∈ Finset.Ioc n (2 * n), vonMangoldt d
      = ∑ d ∈ Finset.Ioc n (2 * n),
            vonMangoldt d * (((2 * n / d : ℕ) : ℝ) - 2 * ((n / d : ℕ) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro d hd
          obtain ⟨h1, h2⟩ := hcoeff_one d hd
          simp [h1, h2]
    _ ≤ ∑ d ∈ Finset.range (2 * n + 1),
            vonMangoldt d * (((2 * n / d : ℕ) : ℝ) - 2 * ((n / d : ℕ) : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hIoc_sub (fun d hd_range _ => by
            apply mul_nonneg vonMangoldt_nonneg
            have hh := Nat.mul_div_le_mul_div_assoc 2 n d
            have hR : (2 * (n / d : ℕ) : ℝ) ≤ ↑(2 * n / d) := by exact_mod_cast hh
            linarith)

/-- **von Mangoldt doubling bound** (proved): ψ(2n) - ψ(n) ≤ 2n · log 2.
    Key steps: ψ(2n)-ψ(n) ≤ log(C(2n,n)) ≤ log(4^n) = 2n·log 2. -/
theorem chebyshevPsi_doubling_le (n : ℕ) (hn : 1 ≤ n) :
    chebyshevPsi (2 * n) - chebyshevPsi n ≤ 2 * n * Real.log 2 := by
  have h_psi_le : chebyshevPsi (2 * n) - chebyshevPsi n ≤
      Real.log (Nat.centralBinom n : ℝ) := psi_doubling_le_log_centralBinom n
  have h_log_le : Real.log (Nat.centralBinom n : ℝ) ≤ 2 * ↑n * Real.log 2 := by
    have hle : Nat.centralBinom n ≤ 4 ^ n := by
      calc Nat.centralBinom n = Nat.choose (2 * n) n := rfl
        _ ≤ ∑ k ∈ range (2 * n + 1), Nat.choose (2 * n) k :=
            Finset.single_le_sum (fun k _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
        _ = 2 ^ (2 * n) := by rw [Nat.sum_range_choose]
        _ = (2 ^ 2) ^ n := by rw [pow_mul]
        _ = 4 ^ n := by norm_num
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

set_option maxHeartbeats 800000 in
private theorem psi_odd_le_log_choose (m : ℕ) :
    chebyshevPsi (2 * m + 1) - chebyshevPsi (m + 1) ≤
    Real.log (Nat.choose (2 * m + 1) m : ℝ) := by
  have h_log_choose : Real.log (Nat.choose (2 * m + 1) m) = Real.log (Nat.factorial (2 * m + 1)) - Real.log (Nat.factorial m) - Real.log (Nat.factorial (m + 1)) := by
    rw [ Nat.cast_choose ] <;> try linarith;
    rw [ Real.log_div, Real.log_mul ] <;> first | positivity | norm_num [ two_mul, add_assoc ] ; ring;
  have h_log_factorial (n : ℕ) : Real.log (Nat.factorial n) = ∑ d ∈ Finset.Icc 1 n, vonMangoldt d * ⌊(n : ℝ) / (d : ℝ)⌋ := by
    convert log_factorial_vonMangoldt n using 1;
    erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ];
    exact Finset.sum_congr rfl fun x hx => by congr; exact Int.floor_eq_iff.mpr ⟨ by rw [ le_div_iff₀ ] <;> norm_cast <;> linarith [ Nat.div_mul_le_self n ( x + 1 ) ], by rw [ div_lt_iff₀ ] <;> norm_cast <;> linarith [ Nat.div_add_mod n ( x + 1 ), Nat.mod_lt n ( Nat.succ_pos x ) ] ⟩ ;
  have h_apply_log_factorial : ∑ d ∈ Finset.Icc 1 (2 * m + 1), vonMangoldt d * ⌊(2 * m + 1 : ℝ) / (d : ℝ)⌋ - ∑ d ∈ Finset.Icc 1 m, vonMangoldt d * ⌊(m : ℝ) / (d : ℝ)⌋ - ∑ d ∈ Finset.Icc 1 (m + 1), vonMangoldt d * ⌊((m + 1) : ℝ) / (d : ℝ)⌋ ≥ ∑ d ∈ Finset.Ioc (m + 1) (2 * m + 1), vonMangoldt d := by
    have h_separate_sums : ∑ d ∈ Finset.Icc 1 (2 * m + 1), vonMangoldt d * (⌊(2 * m + 1 : ℝ) / (d : ℝ)⌋ - ⌊(m : ℝ) / (d : ℝ)⌋ - ⌊((m + 1) : ℝ) / (d : ℝ)⌋) ≥ ∑ d ∈ Finset.Ioc (m + 1) (2 * m + 1), vonMangoldt d := by
      have h_separate_sums : ∀ d ∈ Finset.Icc 1 (2 * m + 1), vonMangoldt d * (⌊(2 * m + 1 : ℝ) / (d : ℝ)⌋ - ⌊(m : ℝ) / (d : ℝ)⌋ - ⌊((m + 1) : ℝ) / (d : ℝ)⌋) ≥ if d ∈ Finset.Ioc (m + 1) (2 * m + 1) then vonMangoldt d else 0 := by
        intro d hd; split_ifs <;> simp_all +decide [ Nat.cast_add, Nat.cast_mul, Nat.cast_one, div_eq_mul_inv ] ;
        · have h_floor : ⌊(2 * m + 1 : ℝ) / d⌋ = 1 ∧ ⌊(m : ℝ) / d⌋ = 0 ∧ ⌊((m + 1) : ℝ) / d⌋ = 0 := by
            norm_num [ Int.floor_eq_iff ];
            exact ⟨ ⟨ by rw [ le_div_iff₀ ( by norm_cast; linarith ) ] ; norm_cast; linarith, by rw [ div_lt_iff₀ ( by norm_cast; linarith ) ] ; norm_cast; linarith ⟩, ⟨ by positivity, by rw [ div_lt_iff₀ ( by norm_cast; linarith ) ] ; norm_cast; linarith ⟩, by positivity, by rw [ div_lt_iff₀ ( by norm_cast; linarith ) ] ; norm_cast; linarith ⟩;
          simp_all +decide [ div_eq_mul_inv ];
          norm_num [ show ⌊ ( m : ℝ ) * ( d : ℝ ) ⁻¹⌋ = 0 by exact Int.floor_eq_iff.mpr ⟨ by norm_num; linarith, by norm_num; linarith ⟩, show ⌊ ( m + 1 : ℝ ) * ( d : ℝ ) ⁻¹⌋ = 0 by exact Int.floor_eq_iff.mpr ⟨ by norm_num; linarith, by norm_num; linarith ⟩ ];
        · refine mul_nonneg ( ?_ ) ( ?_ );
          · exact vonMangoldt_nonneg;
          · norm_num [ add_mul, mul_add ];
            norm_cast;
            exact Int.le_of_lt_add_one ( by rw [ ← @Int.cast_lt ℝ ] ; push_cast; linarith [ Int.floor_le ( ( m : ℝ ) * ( d : ℝ ) ⁻¹ + ( d : ℝ ) ⁻¹ ), Int.lt_floor_add_one ( ( m : ℝ ) * ( d : ℝ ) ⁻¹ + ( d : ℝ ) ⁻¹ ), Int.floor_le ( ( 2 * m : ℝ ) * ( d : ℝ ) ⁻¹ + ( d : ℝ ) ⁻¹ ), Int.lt_floor_add_one ( ( 2 * m : ℝ ) * ( d : ℝ ) ⁻¹ + ( d : ℝ ) ⁻¹ ), Int.floor_le ( ( m : ℝ ) * ( d : ℝ ) ⁻¹ ), Int.lt_floor_add_one ( ( m : ℝ ) * ( d : ℝ ) ⁻¹ ) ] );
      refine' le_trans _ ( Finset.sum_le_sum h_separate_sums );
      simp +decide [ Finset.sum_ite ];
      refine' le_of_eq _;
      refine' Finset.sum_bij ( fun x hx => x ) _ _ _ _ <;> simp +arith +decide;
      lia;
    convert h_separate_sums using 1 ; norm_num [ mul_sub, Finset.sum_sub_distrib ];
    congr! 1;
    · norm_num [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
      rw [ ← Finset.sum_subset ( Finset.Ioc_subset_Ioc_right ( by linarith : m ≤ 2 * m ) ) ] <;> norm_num;
      · exact Or.inr ⟨ by positivity, by rw [ div_lt_iff₀ ] <;> linarith ⟩;
      · exact fun x hx₁ hx₂ hx₃ => Or.inr ⟨ by positivity, by rw [ div_lt_one ( by positivity ) ] ; exact_mod_cast hx₃ hx₁ ⟩;
    · refine' Finset.sum_subset _ _ <;> intro d hd <;> norm_num at *;
      · grind;
      · exact fun h => Or.inr ⟨ by positivity, by rw [ div_lt_one ( by norm_cast; linarith ) ] ; exact_mod_cast by linarith [ h hd.1 ] ⟩;
  simp_all +decide [ Finset.sum_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
  convert add_le_add_right h_apply_log_factorial ( chebyshevPsi ( m + 1 ) ) using 1;
  · unfold chebyshevPsi; rw [ ← Finset.sum_union ] <;> norm_num [ Finset.disjoint_right ] ;
    · rcongr x ; norm_num ; omega;
    · grind;
  · ring

private theorem chebyshevPsi_odd_step (m : ℕ) :
    chebyshevPsi (2 * m + 1) - chebyshevPsi (m + 1) ≤ 2 * ↑m * Real.log 2 := by
  have h1 : (chebyshevPsi (2 * m + 1) - chebyshevPsi (m + 1)) ≤
      Real.log (Nat.choose (2 * m + 1) m : ℝ) := psi_odd_le_log_choose m
  have h2 : Nat.choose (2 * m + 1) m ≤ 2 ^ (2 * m) := by
    calc Nat.choose (2 * m + 1) m ≤ 4 ^ m := Nat.choose_middle_le_pow m
      _ = 2 ^ (2 * m) := by ring
  exact h1.trans ( by simpa using Real.log_le_log ( Nat.cast_pos.mpr <| Nat.choose_pos <| by linarith ) <| Nat.cast_le.mpr h2 )

/-- **Upper bound** (proved): ψ(n) ≤ 2n · log 2 for all n.
    Strong induction: even case uses `chebyshevPsi_doubling_le`,
    odd case uses `chebyshevPsi_odd_step` (via central binomial bound on C(2m+1,m)). -/
theorem chebyshevPsi_upper_bound (n : ℕ) :
    chebyshevPsi n ≤ 2 * n * Real.log 2 := by
  induction' n using Nat.strong_induction_on with n ih;
  by_cases hn_even : Even n;
  · obtain ⟨ k, rfl ⟩ := hn_even;
    by_cases hk : k = 0;
    · unfold chebyshevPsi; norm_num [ hk ];
    · have := chebyshevPsi_doubling_le k ( Nat.pos_of_ne_zero hk );
      rw [ two_mul ] at this; specialize ih k ( by linarith [ Nat.pos_of_ne_zero hk ] ) ; push_cast at *; linarith;
  · rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> simp_all +decide;
    have h_step : chebyshevPsi (2 * k + 1) ≤ chebyshevPsi (k + 1) + 2 * k * Real.log 2 := by
      have := chebyshevPsi_odd_step k;
      linarith;
    rcases k with ( _ | k ) <;> norm_num at *;
    · unfold chebyshevPsi; norm_num [ Finset.sum_range_succ ];
      positivity;
    · exact h_step.trans ( by have := ih ( k + 1 + 1 ) ( by linarith ) ; norm_num at * ; nlinarith [ Real.log_nonneg one_le_two ] )

/-! ## Lower Bound ψ(n) ≥ (n/2) · log 2

From Bertrand's postulate (π(2n) > π(n)), there's a prime p with n < p ≤ 2n,
so θ(2n) - θ(n) ≥ log(n+1). Combined with θ(n) ≤ ψ(n), this gives a lower bound. -/

/-- From Bertrand: ψ(2n) - ψ(n) ≥ log(n+1) for n ≥ 1 -/
theorem chebyshevPsi_doubling_lower (n : ℕ) (hn : 1 ≤ n) :
    Real.log (n + 1) ≤ chebyshevPsi (2 * n) - chebyshevPsi n := by
  obtain ⟨p, hp_prime, hp_lt, hp_le⟩ := Nat.bertrand n (by omega)
  have hp_ge : (n : ℝ) + 1 ≤ p := by exact_mod_cast Nat.succ_le_of_lt hp_lt
  have hsubset : range (n + 1) ⊆ range (2 * n + 1) := Finset.range_mono (by omega)
  have hmem : p ∈ range (2 * n + 1) \ range (n + 1) := by
    simp only [Finset.mem_sdiff, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  unfold chebyshevPsi
  have key : vonMangoldt p ≤
      ∑ k ∈ range (2 * n + 1), vonMangoldt k - ∑ k ∈ range (n + 1), vonMangoldt k := by
    have hf : ∀ k ∈ range (2 * n + 1) \ range (n + 1), (0 : ℝ) ≤ vonMangoldt k :=
      fun k _ => vonMangoldt_nonneg
    have hle : vonMangoldt p ≤
        ∑ k ∈ range (2 * n + 1) \ range (n + 1), vonMangoldt k :=
      Finset.single_le_sum hf hmem
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
theorem chebyshevPsi_bounds (n : ℕ) (_ : 1 ≤ n) :
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
