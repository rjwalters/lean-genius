import Proofs.Erdos85LargePrimeTripleSize

/-!
# The five-prime boundary scalar is nonsquare

If the exact boundary order is five times a prime, a hypothetical square
`d - 3 = s²` factors that order into two nearby nontrivial factors.  Primality
then leaves only the tiny values excluded by evenness and `p ≥ 7`.
-/

namespace Erdos85

/-- At an even boundary of order `5p`, with `p ≥ 7` prime, the transverse
quotient scalar `d - 3` is not a rational/natural square. -/
theorem not_isSquare_d_sub_three_of_boundary_eq_five_mul_prime
    {d p : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hp : p.Prime) (hp7 : 7 ≤ p)
    (hboundary : d * (d - 1) + 3 = 5 * p) :
    ¬ IsSquare (d - 3) := by
  intro hsquare
  obtain ⟨s, hs⟩ := hsquare
  have hspos : 0 < s := by
    by_contra h
    have hs0 : s = 0 := Nat.eq_zero_of_not_pos h
    simp [hs0] at hs
    omega
  have hdEq : d = s * s + 3 := by omega
  let A := s * s - s + 3
  let B := s * s + s + 3
  have hss : s ≤ s * s := by nlinarith
  have hfactor : A * B = 5 * p := by
    have hcastA : (A : ℤ) = (s : ℤ) * s - s + 3 := by
      dsimp [A]
      rw [Nat.cast_sub hss]
      push_cast
      ring
    have hcastB : (B : ℤ) = (s : ℤ) * s + s + 3 := by
      simp [B]
    have hboundaryZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hboundary
    have hdEqZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hdEq
    push_cast at hboundaryZ hdEqZ
    have hcastPred : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      norm_num
    have hfactorZ : (A : ℤ) * B = 5 * p := by
      rw [hcastA, hcastB]
      calc
        ((s : ℤ) * s - s + 3) * ((s : ℤ) * s + s + 3) =
            ((s : ℤ) * s + 3) * (((s : ℤ) * s + 3) - 1) + 3 := by ring
        _ = (d : ℤ) * ((d : ℤ) - 1) + 3 := by rw [← hdEqZ]
        _ = (d : ℤ) * ((d - 1 : ℕ) : ℤ) + 3 := by rw [hcastPred]
        _ = 5 * p := hboundaryZ
    exact_mod_cast hfactorZ
  have hA3 : 3 ≤ A := by
    dsimp [A]
    omega
  have hB3 : 3 ≤ B := by simp [B]
  have h5dvd : 5 ∣ A ∨ 5 ∣ B := by
    have : 5 ∣ A * B := by rw [hfactor]; exact dvd_mul_right 5 p
    exact (show Nat.Prime 5 by norm_num).dvd_mul.mp this
  rcases h5dvd with h5A | h5B
  · obtain ⟨q, hAq⟩ := h5A
    have hqB : q * B = p := by
      rw [hAq] at hfactor
      apply Nat.eq_of_mul_eq_mul_left (show 0 < 5 by omega)
      simpa [mul_assoc] using hfactor
    have hqDvd : q ∣ p := ⟨B, hqB.symm⟩
    rcases hp.eq_one_or_self_of_dvd q hqDvd with hq1 | hqp
    · subst q
      have hA5 : A = 5 := by omega
      have hs2 : s = 2 := by
        dsimp [A] at hA5
        have hdiff : s * s - s = 2 := by omega
        have hrecover : s * s - s + s = s * s := Nat.sub_add_cancel hss
        have hsge : 2 ≤ s := by
          by_contra h
          have : s = 1 := by omega
          subst s
          norm_num at hA5
        have hsle : s ≤ 2 := by
          by_contra h
          have : 3 ≤ s := by omega
          nlinarith [hdiff, hrecover]
        omega
      subst s
      have hd7 : d = 7 := by omega
      subst d
      norm_num at heven
    · rw [hqp] at hqB
      have : B = 1 := Nat.eq_of_mul_eq_mul_left hp.pos (by
        simpa using hqB)
      omega
  · obtain ⟨q, hBq⟩ := h5B
    have hAq : A * q = p := by
      rw [hBq] at hfactor
      apply Nat.eq_of_mul_eq_mul_left (show 0 < 5 by omega)
      nlinarith [hfactor]
    have hqDvd : q ∣ p := ⟨A, by simpa [mul_comm] using hAq.symm⟩
    rcases hp.eq_one_or_self_of_dvd q hqDvd with hq1 | hqp
    · subst q
      have hB5 : B = 5 := by omega
      have hs1 : s = 1 := by
        dsimp [B] at hB5
        have hsle : s ≤ 1 := by
          by_contra h
          have : 2 ≤ s := by omega
          nlinarith
        omega
      subst s
      have hd4 : d = 4 := by omega
      subst d
      norm_num at hboundary
      omega
    · rw [hqp] at hAq
      have : A = 1 := Nat.eq_of_mul_eq_mul_right hp.pos (by
        simpa using hAq)
      omega

end Erdos85
