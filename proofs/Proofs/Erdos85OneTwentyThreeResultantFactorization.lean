import Proofs.Erdos85ResultantFactorization
import Proofs.Erdos85OneTwentyThreeNormCertificate

/-!
# Resultant factorization at scalar 123

This file supplies the algebraic half of the scalar-123 certificate bridge.
It identifies the executable Chebyshev recurrence with `C_n(123)`, computes
the conductor-one and conductor-two resultants, and factors the cycle value
as the product of all conductor resultants at least three.
-/

open Polynomial

namespace Erdos85

noncomputable section

/-- Joint invariant for the executable Chebyshev loop at scalar `123`. -/
theorem chebyshevOneTwentyThreeLoop_spec (m : ℕ) :
    ∀ (k : ℤ) (a b : ℕ), 2 ≤ a → a ≤ b →
      (a : ℤ) = (Chebyshev.C ℤ k).eval 123 →
      (b : ℤ) = (Chebyshev.C ℤ (k + 1)).eval 123 →
      2 ≤ chebyshevOneTwentyThreeLoop m a b ∧
        ((chebyshevOneTwentyThreeLoop m a b : ℕ) : ℤ) =
          (Chebyshev.C ℤ (k + m)).eval 123 := by
  induction m with
  | zero =>
      intro k a b h2 hab ha hb
      exact ⟨h2, by simpa [chebyshevOneTwentyThreeLoop] using ha⟩
  | succ m IH =>
      intro k a b h2 hab ha hb
      have hb2 : 2 ≤ b := h2.trans hab
      have hle : b ≤ 123 * b - a := by omega
      have hcast : ((123 * b - a : ℕ) : ℤ) = 123 * (b : ℤ) - (a : ℤ) := by
        omega
      have hnext : ((123 * b - a : ℕ) : ℤ) =
          (Chebyshev.C ℤ (k + 1 + 1)).eval 123 := by
        rw [hcast, ha, hb, show k + 1 + 1 = k + 2 from by ring,
          Polynomial.Chebyshev.C_add_two]
        simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_X]
      have hstep := IH (k + 1) b (123 * b - a) hb2 hle hb hnext
      refine ⟨hstep.1, ?_⟩
      rw [show chebyshevOneTwentyThreeLoop (m + 1) a b =
          chebyshevOneTwentyThreeLoop m b (123 * b - a) from rfl,
        show ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 from by push_cast; ring,
        show k + ((m : ℤ) + 1) = k + 1 + (m : ℤ) from by ring]
      exact hstep.2

theorem chebyshevOneTwentyThree_spec (n : ℕ) :
    2 ≤ chebyshevOneTwentyThree n ∧
      (chebyshevOneTwentyThree n : ℤ) =
        (Chebyshev.C ℤ (n : ℤ)).eval 123 := by
  have h := chebyshevOneTwentyThreeLoop_spec n 0 2 123
    (by norm_num) (by norm_num)
    (by simp [Polynomial.Chebyshev.C_zero])
    (by simp [Polynomial.Chebyshev.C_one])
  simpa [chebyshevOneTwentyThree] using h

theorem two_le_chebyshevOneTwentyThree (n : ℕ) :
    2 ≤ chebyshevOneTwentyThree n :=
  (chebyshevOneTwentyThree_spec n).1

theorem chebyshevOneTwentyThree_cast (n : ℕ) :
    (chebyshevOneTwentyThree n : ℤ) =
      (Chebyshev.C ℤ (n : ℤ)).eval 123 :=
  (chebyshevOneTwentyThree_spec n).2

theorem cycleChebyshevOneTwentyThree_cast (n : ℕ) :
    (cycleChebyshevOneTwentyThree n : ℤ) =
      (Chebyshev.C ℤ (n : ℤ)).eval 123 - 2 := by
  unfold cycleChebyshevOneTwentyThree
  rw [Nat.cast_sub (two_le_chebyshevOneTwentyThree n),
    chebyshevOneTwentyThree_cast]
  norm_num

/-- Conductor one contributes `123 - 2 = 121`. -/
theorem cyclotomicResultantAt_oneTwentyThree_one :
    cyclotomicResultantAt 123 1 = 121 := by
  unfold cyclotomicResultantAt
  rw [Polynomial.cyclotomic_one ℤ, cyclotomicQuadraticIntAt_natDegree,
    show (Polynomial.X - 1 : Polynomial ℤ) = Polynomial.X - Polynomial.C 1 by
      rw [Polynomial.C_1],
    Polynomial.natDegree_X_sub_C,
    Polynomial.resultant_X_sub_C_left (cyclotomicQuadraticIntAt 123) 2 1
      (le_of_eq (cyclotomicQuadraticIntAt_natDegree 123))]
  simp [cyclotomicQuadraticIntAt]

/-- Conductor two contributes `-(123 + 2) = -125`. -/
theorem cyclotomicResultantAt_oneTwentyThree_two :
    cyclotomicResultantAt 123 2 = -125 := by
  unfold cyclotomicResultantAt
  rw [Polynomial.cyclotomic_two ℤ, cyclotomicQuadraticIntAt_natDegree,
    show (Polynomial.X + 1 : Polynomial ℤ) = Polynomial.X + Polynomial.C 1 by
      rw [Polynomial.C_1],
    Polynomial.natDegree_X_add_C,
    Polynomial.resultant_X_add_C_left (cyclotomicQuadraticIntAt 123) 2 1
      (le_of_eq (cyclotomicQuadraticIntAt_natDegree 123))]
  simp [cyclotomicQuadraticIntAt]

/-- **Algebraic scalar-123 divisor-product factorization.** -/
theorem oneTwentyThree_frequency_mul_prod_resultant {n : ℕ} (hn : 0 < n) :
    ((121 * if 2 ∣ n then 125 else 1 : ℕ) : ℤ) *
        ∏ k ∈ n.divisors.filter (fun k => 3 ≤ k),
          cyclotomicResultantAt 123 k =
      (cycleChebyshevOneTwentyThree n : ℤ) := by
  have hsplit := Finset.prod_filter_mul_prod_filter_not n.divisors
    (fun k => 3 ≤ k) (cyclotomicResultantAt 123)
  have hmain := prod_cyclotomicResultantAt_eq_X_pow_sub_one_resultant
    (a := 123) hn
  rw [X_pow_sub_one_resultant_at' 123 hn] at hmain
  rw [cycleChebyshevOneTwentyThree_cast]
  by_cases heven : 2 ∣ n
  · rw [divisors_filter_not_three_even hn heven,
      Finset.prod_pair (by norm_num : (1 : ℕ) ≠ 2),
      cyclotomicResultantAt_oneTwentyThree_one,
      cyclotomicResultantAt_oneTwentyThree_two] at hsplit
    have hpow : ((-1 : ℤ)) ^ (n + 1) = -1 :=
      Odd.neg_one_pow (Nat.odd_iff.mpr (by
        obtain ⟨c, rfl⟩ := heven
        omega))
    rw [hpow] at hmain
    simp only [if_pos heven, Nat.cast_mul, Nat.cast_ofNat]
    linarith [hsplit, hmain]
  · rw [divisors_filter_not_three_odd hn heven, Finset.prod_singleton,
      cyclotomicResultantAt_oneTwentyThree_one] at hsplit
    have hpow : ((-1 : ℤ)) ^ (n + 1) = 1 :=
      Even.neg_one_pow (Nat.even_iff.mpr (by
        rcases Nat.mod_two_eq_zero_or_one n with h | h
        · exact absurd (Nat.dvd_of_mod_eq_zero h) heven
        · omega))
    rw [hpow, one_mul] at hmain
    simp only [if_neg heven, mul_one, Nat.cast_ofNat]
    linarith [hsplit, hmain]

theorem primitiveNormCandidateOTT_ne_zero {n : ℕ} (h3 : 3 ≤ n)
    (hmax : n ≤ 15255) : primitiveNormCandidateOTT n ≠ 0 := by
  intro hzero
  have hnsq := (primitiveNormOTT_not_isSquare h3 hmax).2
  apply hnsq
  refine ⟨0, ?_⟩
  simp [hzero]

/-- Strong-induction cancellation, parameterized by the native stage-2
divisor-product certificate.  This isolates the proof-theoretic bridge from
the expensive executable verification. -/
theorem cyclotomicResultantAt_oneTwentyThree_eq_sq_of_factorization
    (hcert : ∀ n : ℕ, 3 ≤ n → n ≤ 15255 →
      cycleChebyshevOneTwentyThree n =
        (121 * if 2 ∣ n then 125 else 1) *
          ∏ k ∈ (Finset.Icc 3 n).filter (fun k => k ∣ n),
            (primitiveNormCandidateOTT k) ^ 2) :
    ∀ n : ℕ, 3 ≤ n → n ≤ 15255 →
      cyclotomicResultantAt 123 n =
        (primitiveNormCandidateOTT n : ℤ) ^ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro h3 hmax
    have hn0 : 0 < n := by omega
    have hF := oneTwentyThree_frequency_mul_prod_resultant hn0
    rw [divisors_filter_three_eq_Icc_filter hn0] at hF
    have hcertN := hcert n h3 hmax
    have hcertZ : (cycleChebyshevOneTwentyThree n : ℤ) =
        ((121 * if 2 ∣ n then 125 else 1 : ℕ) : ℤ) *
          ∏ k ∈ (Finset.Icc 3 n).filter (fun k => k ∣ n),
            (primitiveNormCandidateOTT k : ℤ) ^ 2 := by
      exact_mod_cast hcertN
    have hfreq : ((121 * if 2 ∣ n then 125 else 1 : ℕ) : ℤ) ≠ 0 := by
      split <;> norm_num
    have hprods :
        ∏ k ∈ (Finset.Icc 3 n).filter (fun k => k ∣ n),
            cyclotomicResultantAt 123 k =
          ∏ k ∈ (Finset.Icc 3 n).filter (fun k => k ∣ n),
            (primitiveNormCandidateOTT k : ℤ) ^ 2 :=
      mul_left_cancel₀ hfreq (by rw [hF, hcertZ])
    have hnmem : n ∈ (Finset.Icc 3 n).filter (fun k => k ∣ n) :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨h3, le_refl n⟩, dvd_refl n⟩
    rw [← Finset.mul_prod_erase _ _ hnmem,
      ← Finset.mul_prod_erase _ _ hnmem] at hprods
    have herase :
        ∏ k ∈ ((Finset.Icc 3 n).filter (fun k => k ∣ n)).erase n,
            cyclotomicResultantAt 123 k =
          ∏ k ∈ ((Finset.Icc 3 n).filter (fun k => k ∣ n)).erase n,
            (primitiveNormCandidateOTT k : ℤ) ^ 2 := by
      refine Finset.prod_congr rfl fun k hk => ?_
      obtain ⟨hkne, hkA⟩ := Finset.mem_erase.mp hk
      obtain ⟨hkIcc, hkdvd⟩ := Finset.mem_filter.mp hkA
      obtain ⟨hk3, hkn⟩ := Finset.mem_Icc.mp hkIcc
      exact IH k (lt_of_le_of_ne hkn hkne) hk3 (le_trans hkn hmax)
    rw [herase] at hprods
    have hne :
        ∏ k ∈ ((Finset.Icc 3 n).filter (fun k => k ∣ n)).erase n,
            (primitiveNormCandidateOTT k : ℤ) ^ 2 ≠ 0 := by
      rw [Finset.prod_ne_zero_iff]
      intro k hk
      obtain ⟨hkne, hkA⟩ := Finset.mem_erase.mp hk
      obtain ⟨hkIcc, hkdvd⟩ := Finset.mem_filter.mp hkA
      obtain ⟨hk3, hkn⟩ := Finset.mem_Icc.mp hkIcc
      exact pow_ne_zero 2 (Int.ofNat_ne_zero.mpr
        (primitiveNormCandidateOTT_ne_zero hk3 (le_trans hkn hmax)))
    exact mul_right_cancel₀ hne hprods

end

end Erdos85
