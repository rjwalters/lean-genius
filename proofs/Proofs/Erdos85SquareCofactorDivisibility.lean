import Proofs.Erdos85FiveBoundaryNonsquare

/-!
# Cofactor divisibility in the square large-prime branch

Writing the boundary order as `N p`, a square transverse scalar
`d - 3 = s²` gives the factorization

`d² - d + 3 = (d - s)(d + s)`.

For a prime `p > d`, the prime cannot divide the first factor.  It therefore
divides the second, and cancellation shows that `d - s` divides the cofactor
`N`.  This is a uniform replacement for separate small-cofactor
factorizations.
-/

namespace Erdos85

/-- **Square-branch cofactor divisor.**  If an exact boundary order is `N*p`,
where `p` is prime and larger than the degree, and `d-3` is square, then for
some square root `s` the large integer `d-s` divides `N`. -/
theorem square_boundary_cofactor_divisibility
    {d p N : ℕ} (hd : 4 ≤ d) (hp : p.Prime) (hdp : d < p)
    (hboundary : d * (d - 1) + 3 = N * p)
    (hsquare : IsSquare (d - 3)) :
    ∃ s : ℕ, d = s * s + 3 ∧ d - s ∣ N ∧ d - s ≤ N := by
  obtain ⟨s, hs⟩ := hsquare
  have hdEq : d = s * s + 3 := by omega
  have hsd : s ≤ d := by nlinarith
  have hApos : 0 < d - s := by
    apply Nat.sub_pos_of_lt
    rw [hdEq]
    nlinarith
  have hAle : d - s ≤ d := Nat.sub_le _ _
  have hfactor : (d - s) * (d + s) = N * p := by
    have hcastSub : ((d - s : ℕ) : ℤ) = (d : ℤ) - s := by
      rw [Nat.cast_sub hsd]
    have hcastPred : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      norm_num
    have hsZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hs
    have hbZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hboundary
    push_cast at hsZ hbZ
    have hfactorZ : ((d - s : ℕ) : ℤ) * (d + s) = N * p := by
      rw [hcastSub]
      rw [hcastPred] at hbZ
      nlinarith [hsZ, hbZ]
    exact_mod_cast hfactorZ
  have hpProd : p ∣ (d - s) * (d + s) := by
    rw [hfactor]
    exact dvd_mul_left p N
  have hpNotA : ¬ p ∣ d - s := by
    intro hpA
    have hpLe : p ≤ d - s := Nat.le_of_dvd hApos hpA
    omega
  have hpB : p ∣ d + s := (hp.dvd_mul.mp hpProd).resolve_left hpNotA
  obtain ⟨q, hBq⟩ := hpB
  have hcancel : (d - s) * q = N := by
    rw [hBq] at hfactor
    apply Nat.eq_of_mul_eq_mul_right hp.pos
    simpa [mul_assoc, mul_comm, mul_left_comm] using hfactor
  have hqpos : 0 < q := by
    by_contra h
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos h
    rw [hq0, mul_zero] at hBq
    omega
  have hNpos : 0 < N := by
    rw [← hcancel]
    exact Nat.mul_pos hApos hqpos
  refine ⟨s, hdEq, ⟨q, hcancel.symm⟩, ?_⟩
  exact Nat.le_of_dvd hNpos ⟨q, hcancel.symm⟩

/-- **Square-branch thin window.**  Under the same hypotheses, the large
prime lies at most one square root above the degree.  More precisely, for
the square root `s` of `d-3` there is a positive cofactor `q` such that
`d+s = p*q` and `N = (d-s)*q`; in particular `p ≤ d+s`. -/
theorem square_boundary_prime_thin_window
    {d p N : ℕ} (hd : 4 ≤ d) (hp : p.Prime) (hdp : d < p)
    (hboundary : d * (d - 1) + 3 = N * p)
    (hsquare : IsSquare (d - 3)) :
    ∃ s q : ℕ, d = s * s + 3 ∧ 0 < q ∧
      d + s = p * q ∧ N = (d - s) * q ∧ p ≤ d + s := by
  obtain ⟨s, hs⟩ := hsquare
  have hdEq : d = s * s + 3 := by omega
  have hsd : s ≤ d := by nlinarith
  have hApos : 0 < d - s := by
    apply Nat.sub_pos_of_lt
    rw [hdEq]
    nlinarith
  have hfactor : (d - s) * (d + s) = N * p := by
    have hcastSub : ((d - s : ℕ) : ℤ) = (d : ℤ) - s := by
      rw [Nat.cast_sub hsd]
    have hcastPred : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ d)]
      norm_num
    have hsZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hs
    have hbZ := congrArg (fun n : ℕ ↦ (n : ℤ)) hboundary
    push_cast at hsZ hbZ
    have hfactorZ : ((d - s : ℕ) : ℤ) * (d + s) = N * p := by
      rw [hcastSub]
      rw [hcastPred] at hbZ
      nlinarith [hsZ, hbZ]
    exact_mod_cast hfactorZ
  have hpProd : p ∣ (d - s) * (d + s) := by
    rw [hfactor]
    exact dvd_mul_left p N
  have hpNotA : ¬ p ∣ d - s := by
    intro hpA
    have hpLe : p ≤ d - s := Nat.le_of_dvd hApos hpA
    omega
  have hpB : p ∣ d + s := (hp.dvd_mul.mp hpProd).resolve_left hpNotA
  obtain ⟨q, hBq⟩ := hpB
  have hcancel : (d - s) * q = N := by
    rw [hBq] at hfactor
    apply Nat.eq_of_mul_eq_mul_right hp.pos
    simpa [mul_assoc, mul_comm, mul_left_comm] using hfactor
  have hqpos : 0 < q := by
    by_contra h
    have hq0 : q = 0 := Nat.eq_zero_of_not_pos h
    rw [hq0, mul_zero] at hBq
    omega
  refine ⟨s, q, hdEq, hqpos, hBq, hcancel.symm, ?_⟩
  rw [hBq]
  exact Nat.le_mul_of_pos_right p hqpos

/-- **Exact square-branch factorization.**  Since `p > d` while `s < d`,
the positive multiplier in the thin-window theorem must equal one.  Thus
the apparently continuous square branch is confined to the single
factorization `p = d+s`, `N = d-s`. -/
theorem square_boundary_exact_factors
    {d p N : ℕ} (hd : 4 ≤ d) (hp : p.Prime) (hdp : d < p)
    (hboundary : d * (d - 1) + 3 = N * p)
    (hsquare : IsSquare (d - 3)) :
    ∃ s : ℕ, d = s * s + 3 ∧ p = d + s ∧ N = d - s := by
  obtain ⟨s, q, hdEq, hqpos, hsum, hcofactor, _⟩ :=
    square_boundary_prime_thin_window hd hp hdp hboundary hsquare
  have hsd : s < d := by
    rw [hdEq]
    nlinarith
  have hqOne : q = 1 := by
    by_contra hq
    have hqTwo : 2 ≤ q := by omega
    have htwoP : 2 * p ≤ p * q := by
      simpa [mul_comm] using Nat.mul_le_mul_left p hqTwo
    have hsumLt : d + s < 2 * p := by omega
    rw [← hsum] at htwoP
    omega
  subst q
  simp only [mul_one] at hsum hcofactor
  exact ⟨s, hdEq, hsum.symm, hcofactor⟩

/-- At an even degree, the exact square family has `s ≡ 1 (mod 6)` and
its cofactor is divisible by three.  Thus every surviving square case feeds
directly into the three-primary part of the structural program. -/
theorem three_dvd_cofactor_of_square_boundary
    {d p N : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hp : p.Prime) (hdp : d < p)
    (hboundary : d * (d - 1) + 3 = N * p)
    (hsquare : IsSquare (d - 3)) :
    ∃ s : ℕ, d = s * s + 3 ∧ p = d + s ∧ N = d - s ∧
      s % 6 = 1 ∧ 3 ∣ N := by
  obtain ⟨s, hdEq, hpEq, hNEq⟩ :=
    square_boundary_exact_factors hd hp hdp hboundary hsquare
  have hsOdd : Odd s := by
    rw [← Nat.not_even_iff_odd]
    intro hsEven
    have hsSqEven : Even (s * s) := (Nat.even_mul).2 (Or.inl hsEven)
    obtain ⟨a, ha⟩ := heven
    obtain ⟨b, hb⟩ := hsSqEven
    omega
  have hpNotThree : p ≠ 3 := by omega
  have hsModThree : s % 3 = 1 := by
    have hcases : s % 3 = 0 ∨ s % 3 = 1 ∨ s % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · exfalso
      have h3p : 3 ∣ p := by
        rw [Nat.dvd_iff_mod_eq_zero]
        rw [hpEq, hdEq]
        simp [Nat.add_mod, Nat.mul_mod, h0]
      have : 3 = p :=
        (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3p
      exact hpNotThree this.symm
    · exact h1
    · exfalso
      have h3p : 3 ∣ p := by
        rw [Nat.dvd_iff_mod_eq_zero]
        rw [hpEq, hdEq]
        simp [Nat.add_mod, Nat.mul_mod, h2]
      have : 3 = p :=
        (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3p
      exact hpNotThree this.symm
  have hsModSix : s % 6 = 1 := by
    obtain ⟨k, hk⟩ := hsOdd
    have hdecompThree := Nat.mod_add_div s 3
    have hdecompSix := Nat.mod_add_div s 6
    omega
  have h3N : 3 ∣ N := by
    have hdecompThree := Nat.mod_add_div s 3
    let k := s / 3
    have hsForm : s = 3 * k + 1 := by omega
    refine ⟨3 * k * k + k + 1, ?_⟩
    rw [hNEq]
    have hdSplit : d = 3 * (3 * k * k + k + 1) + s := by
      rw [hdEq, hsForm]
      ring
    rw [hdSplit]
    omega
  exact ⟨s, hdEq, hpEq, hNEq, hsModSix, h3N⟩

end Erdos85
