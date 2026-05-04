/-
  Aristotle targets for ChebyshevBoundsOQ04
  See ChebyshevBoundsOQ04.lean for the main formalization.

  psi_doubling_le_log_centralBinom is now PROVED in the main file.
  This companion targets chebyshevPsi_upper_bound (psi(n) <= 2n*log2).
  Aristotle project: ee80194a-af54-472a-ad2b-3786509c2e6e
-/
import Mathlib.NumberTheory.VonMangoldt
import Mathlib.NumberTheory.Primorial
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Bertrand
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace ChebyshevBoundsOQ04Aristotle

open Nat Finset ArithmeticFunction

noncomputable def chebyshevPsi (n : ℕ) : ℝ :=
  ∑ k ∈ range (n + 1), vonMangoldt k

private lemma chebyshevPsi_mono {m n : ℕ} (h : m ≤ n) :
    chebyshevPsi m ≤ chebyshevPsi n :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_mono (Nat.succ_le_succ h))
    (fun k _ _ => vonMangoldt_nonneg)

private lemma log_factorial_vonMangoldt (m : ℕ) :
    Real.log (m.factorial : ℝ) =
    ∑ d ∈ Finset.range (m + 1), vonMangoldt d * (m / d : ℕ) := by
  have hsum_log : Real.log (m.factorial : ℝ) =
      ∑ k ∈ Finset.range (m + 1), Real.log (k : ℝ) := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.factorial_succ, Nat.cast_mul,
          Real.log_mul (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m))
            (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)),
          Finset.sum_range_succ]
      linarith
  rw [hsum_log]
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

private theorem psi_doubling_le_log_centralBinom (n : ℕ) :
    chebyshevPsi (2 * n) - chebyshevPsi n ≤ Real.log (Nat.centralBinom n : ℝ) := by
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
  rw [hbinom, log_factorial_vonMangoldt (2 * n), log_factorial_vonMangoldt n]
  have hextend : ∑ d ∈ Finset.range (n + 1), vonMangoldt d * (n / d : ℕ) =
      ∑ d ∈ Finset.range (2 * n + 1), vonMangoldt d * (n / d : ℕ) := by
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro d hd hdn
    simp only [Finset.mem_range, not_lt] at hd hdn
    simp [Nat.div_eq_of_lt (by omega)]
  rw [hextend]
  have hpsi : chebyshevPsi (2 * n) - chebyshevPsi n =
      ∑ d ∈ Finset.Ioc n (2 * n), vonMangoldt d := by
    have hle : Finset.range (n + 1) ⊆ Finset.range (2 * n + 1) := Finset.range_mono (by omega)
    have heq : Finset.range (2 * n + 1) \ Finset.range (n + 1) = Finset.Ioc n (2 * n) := by
      ext d; simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ioc]; omega
    simp only [chebyshevPsi, ← heq]
    linarith [Finset.sum_sdiff hle (f := vonMangoldt)]
  rw [hpsi]
  have hIoc_sub : Finset.Ioc n (2 * n) ⊆ Finset.range (2 * n + 1) := by
    intro d hd; simp only [Finset.mem_Ioc] at hd; simp only [Finset.mem_range]; omega
  have hcoeff_one : ∀ d ∈ Finset.Ioc n (2 * n),
      (2 * n / d : ℕ) = 1 ∧ (n / d : ℕ) = 0 := fun d hd => by
    simp only [Finset.mem_Ioc] at hd
    exact ⟨Nat.div_eq_of_lt_le (by omega) (by omega), Nat.div_eq_of_lt (by omega)⟩
  have hrhs_split : ∑ d ∈ Finset.range (2 * n + 1), vonMangoldt d * (2 * n / d : ℕ) -
      2 * ∑ d ∈ Finset.range (2 * n + 1), vonMangoldt d * (n / d : ℕ) =
      ∑ d ∈ Finset.range (2 * n + 1),
        vonMangoldt d * (((2 * n / d : ℕ) : ℝ) - 2 * ((n / d : ℕ) : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]; congr 1; ext d; push_cast; ring
  rw [hrhs_split]
  calc ∑ d ∈ Finset.Ioc n (2 * n), vonMangoldt d
      = ∑ d ∈ Finset.Ioc n (2 * n),
            vonMangoldt d * (((2 * n / d : ℕ) : ℝ) - 2 * ((n / d : ℕ) : ℝ)) := by
          apply Finset.sum_congr rfl; intro d hd
          obtain ⟨h1, h2⟩ := hcoeff_one d hd; simp [h1, h2]
    _ ≤ ∑ d ∈ Finset.range (2 * n + 1),
            vonMangoldt d * (((2 * n / d : ℕ) : ℝ) - 2 * ((n / d : ℕ) : ℝ)) :=
          Finset.sum_le_sum_of_subset_of_nonneg hIoc_sub (fun d _ _ => by
            apply mul_nonneg vonMangoldt_nonneg
            have hh := Nat.mul_div_le_mul_div_assoc 2 n d
            linarith [show (2 * (n / d : ℕ) : ℝ) ≤ ↑(2 * n / d) from by exact_mod_cast hh])

private theorem chebyshevPsi_doubling_le (n : ℕ) (hn : 1 ≤ n) :
    chebyshevPsi (2 * n) - chebyshevPsi n ≤ 2 * n * Real.log 2 := by
  have h1 := psi_doubling_le_log_centralBinom n
  have h2 : Real.log (Nat.centralBinom n : ℝ) ≤ 2 * ↑n * Real.log 2 := by
    have hle : Nat.centralBinom n ≤ 4 ^ n := by
      calc Nat.centralBinom n = Nat.choose (2 * n) n := rfl
        _ ≤ ∑ k ∈ range (2 * n + 1), Nat.choose (2 * n) k :=
            Finset.single_le_sum (fun k _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
        _ = 2 ^ (2 * n) := by rw [Nat.sum_range_choose]
        _ = (2 ^ 2) ^ n := by rw [pow_mul]
        _ = 4 ^ n := by norm_num
    calc Real.log (Nat.centralBinom n : ℝ)
        ≤ Real.log ((4 : ℝ) ^ n) :=
            Real.log_le_log (by exact_mod_cast Nat.centralBinom_pos n) (by exact_mod_cast hle)
      _ = ↑n * Real.log 4 := Real.log_pow n 4
      _ = 2 * ↑n * Real.log 2 := by
            rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]; ring
  linarith

/-- **Target for Aristotle**: ψ(n) ≤ 2n · log 2 for all n.
    Aristotle project: ee80194a-af54-472a-ad2b-3786509c2e6e -/
theorem chebyshevPsi_upper_bound (n : ℕ) :
    chebyshevPsi n ≤ 2 * n * Real.log 2 := by
  sorry

end ChebyshevBoundsOQ04Aristotle
