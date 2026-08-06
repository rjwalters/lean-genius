import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Sign-stable algebraic orbits have zero trace

The global number-field reduction for the positive-excess program uses a
simple polynomial fact.  A multiset of algebraic eigenvalues stable under
`θ ↦ -θ` has zero sum.  At the polynomial level, a monic degree-`r`
polynomial fixed by reflection up to the leading sign has vanishing
next-to-leading coefficient.
-/

namespace Erdos85

open Polynomial

/-- Substitution `X ↦ -X` multiplies the coefficient of degree `n` by
`(-1)^n`. -/
theorem Polynomial.coeff_comp_neg_X
    {K : Type*} [CommRing K] (p : K[X]) (n : ℕ) :
    (p.comp (-X)).coeff n = (-1 : K) ^ n * p.coeff n := by
  rw [comp_eq_sum_left, coeff_sum, sum_def]
  classical
  calc
    (∑ x ∈ p.support, (C (p.coeff x) * (-X) ^ x).coeff n) =
        ∑ x ∈ p.support,
          if x = n then (-1 : K) ^ n * p.coeff n else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hxn : x = n
      · subst x
        have hpow : (-X : K[X]) ^ n = (-1 : K) ^ n • X ^ n := by
          rw [show (-X : K[X]) = (-1 : K) • X by simp, smul_pow]
        simp [hpow, mul_comm]
      · have hpow : (-X : K[X]) ^ x = (-1 : K) ^ x • X ^ x := by
          rw [show (-X : K[X]) = (-1 : K) • X by simp, smul_pow]
        simp [hpow, hxn, Ne.symm hxn]
    _ = (-1 : K) ^ n * p.coeff n := by
      by_cases hn : n ∈ p.support
      · rw [Finset.sum_eq_single n]
        · simp
        · intro b hb hbn
          simp [hbn]
        · exact fun h => (h hn).elim
      · have hcoeff : p.coeff n = 0 := by
          simpa [mem_support_iff] using hn
        simp [hcoeff]

/-- A sign-stable polynomial has zero next-to-leading coefficient.  This is
the coefficient form of “every nonprincipal sign-paired orbit contributes
zero trace”. -/
theorem Polynomial.coeff_natDegree_sub_one_eq_zero_of_signStable
    {K : Type*} [Field K] [CharZero K]
    (p : K[X]) (hdeg : 0 < p.natDegree)
    (hsign : p.comp (-X) = (-1 : K) ^ p.natDegree • p) :
    p.coeff (p.natDegree - 1) = 0 := by
  let n := p.natDegree
  have hnpos : 0 < n := by simpa [n] using hdeg
  have hcoeff := congrArg (fun q : K[X] => q.coeff (n - 1)) hsign
  rw [Polynomial.coeff_comp_neg_X] at hcoeff
  simp only [coeff_smul, smul_eq_mul] at hcoeff
  have hpow : (-1 : K) ^ n = -((-1 : K) ^ (n - 1)) := by
    have hnk : n = (n - 1) + 1 := by omega
    rw [hnk]
    simp [pow_succ]
  rw [hpow] at hcoeff
  have hunit : (-1 : K) ^ (n - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have htwo : (2 : K) ≠ 0 := by norm_num
  have hz : (2 : K) * ((-1 : K) ^ (n - 1)) * p.coeff (n - 1) = 0 := by
    calc
      (2 : K) * ((-1 : K) ^ (n - 1)) * p.coeff (n - 1) =
          ((-1 : K) ^ (n - 1) * p.coeff (n - 1)) -
            (-((-1 : K) ^ (n - 1)) * p.coeff (n - 1)) := by ring
      _ = 0 := sub_eq_zero.mpr hcoeff
  have hc : p.coeff (n - 1) = 0 :=
    (mul_eq_zero.mp hz).resolve_left (mul_ne_zero htwo hunit)
  simpa [n] using hc

/-- Removing a monic linear factor `X-d` from a trace-zero monic
characteristic polynomial leaves next-to-leading coefficient `d`.  Thus for
`d ≠ 0` the nonprincipal factor cannot be sign-stable. -/
theorem Polynomial.coeff_natDegree_sub_one_eq_of_linearFactor_trace_zero
    {K : Type*} [Field K]
    (q : K[X]) (hq : q.Monic) (hdeg : 0 < q.natDegree) (d : K)
    (htrace : ((X - C d) * q).coeff q.natDegree = 0) :
    q.coeff (q.natDegree - 1) = d := by
  let n := q.natDegree
  have hnpos : 0 < n := by simpa [n] using hdeg
  have hnk : n = (n - 1) + 1 := by omega
  have hlead : q.coeff n = 1 := by
    simpa [n] using hq.coeff_natDegree
  change ((X - C d) * q).coeff n = 0 at htrace
  rw [sub_mul, coeff_sub, hnk, coeff_X_mul, coeff_C_mul] at htrace
  rw [Nat.sub_add_cancel hnpos, hlead, mul_one] at htrace
  change q.coeff (n - 1) = d
  exact sub_eq_zero.mp htrace

/-- A trace-zero polynomial with a nonzero principal root has a
non-sign-stable complementary factor. -/
theorem Polynomial.not_signStable_of_linearFactor_trace_zero
    {K : Type*} [Field K] [CharZero K]
    (q : K[X]) (hq : q.Monic) (hdeg : 0 < q.natDegree)
    (d : K) (hd : d ≠ 0)
    (htrace : ((X - C d) * q).coeff q.natDegree = 0) :
    q.comp (-X) ≠ (-1 : K) ^ q.natDegree • q := by
  intro hsign
  have hz := Erdos85.Polynomial.coeff_natDegree_sub_one_eq_zero_of_signStable
    q hdeg hsign
  have hdcoeff :=
    Erdos85.Polynomial.coeff_natDegree_sub_one_eq_of_linearFactor_trace_zero
      q hq hdeg d htrace
  exact hd (hdcoeff ▸ hz)

end Erdos85
