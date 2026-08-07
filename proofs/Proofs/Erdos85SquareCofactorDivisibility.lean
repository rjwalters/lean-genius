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

end Erdos85
