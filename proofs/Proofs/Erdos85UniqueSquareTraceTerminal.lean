import Proofs.Erdos85QuadraticTrace

/-!
# The unique square-sector trace terminal

Suppose the defect-spectrum decomposition of an adjacency operator has one
principal sector, trace `d`, one exceptional rational sector on which the
operator squares to `t²`, and only nonsquare sectors otherwise.  The latter
have trace zero, while the total adjacency trace is zero.  Hence the
exceptional trace is `-d`.  But an endomorphism whose square is `t² I` has
trace an integral multiple of `t`; consequently `t ∣ d`.

This elementary terminal simultaneously targets the currently exceptional
rational conductors:

* `d = 8`, `μ = -2`, `t = 3`;
* `d = 18`, `μ = 1`, `t = 4`;
* `d = 26`, `μ = 0`, `t = 5`.

The file deliberately separates the terminal linear algebra from the
primary-decomposition theorem that will supply its trace hypotheses.
-/

namespace Erdos85

noncomputable section

/-- If a rational endomorphism squares to `t² I` and has trace `-d`, then
`t` divides `d`. -/
theorem nat_dvd_of_trace_eq_neg_of_sq_eq_square_nat
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (T : E →ₗ[ℚ] E) {d t : ℕ} (ht : 0 < t)
    (hT : T * T = ((t * t : ℕ) : ℚ) • LinearMap.id)
    (htrace : LinearMap.trace ℚ E T = -(d : ℚ)) :
    t ∣ d := by
  obtain ⟨z, hz⟩ :=
    LinearMap.exists_int_mul_eq_trace_of_sq_eq_square_nat T t ht hT
  have hq : -(d : ℚ) = (z : ℚ) * t := htrace.symm.trans hz
  have hz' : -(d : ℤ) = z * t := by exact_mod_cast hq
  have hdZ : (t : ℤ) ∣ (d : ℤ) := by
    refine ⟨-z, ?_⟩
    calc
      (d : ℤ) = -(z * t) := by omega
      _ = (t : ℤ) * (-z) := by ring
  exact Int.natCast_dvd_natCast.mp hdZ

/-- Contradiction form of the unique square-sector terminal. -/
theorem false_of_trace_eq_neg_of_sq_eq_square_nat_of_not_dvd
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (T : E →ₗ[ℚ] E) {d t : ℕ} (ht : 0 < t)
    (hT : T * T = ((t * t : ℕ) : ℚ) • LinearMap.id)
    (htrace : LinearMap.trace ℚ E T = -(d : ℚ))
    (hnotdvd : ¬ t ∣ d) : False := by
  exact hnotdvd
    (nat_dvd_of_trace_eq_neg_of_sq_eq_square_nat T ht hT htrace)

/-- Trace-bookkeeping form.  A principal contribution `d`, zero residual
contribution, and total trace zero force the unique square sector to have
trace `-d`, hence force `t ∣ d`. -/
theorem unique_square_sector_forces_dvd
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (T : E →ₗ[ℚ] E) {d t : ℕ} (ht : 0 < t)
    (hT : T * T = ((t * t : ℕ) : ℚ) • LinearMap.id)
    (principalTrace residualTrace totalTrace : ℚ)
    (hprincipal : principalTrace = d) (hresidual : residualTrace = 0)
    (htotal : totalTrace = 0)
    (hsplit : totalTrace = principalTrace + LinearMap.trace ℚ E T +
      residualTrace) :
    t ∣ d := by
  have htrace : LinearMap.trace ℚ E T = -(d : ℚ) := by
    rw [htotal, hprincipal, hresidual] at hsplit
    linarith
  exact nat_dvd_of_trace_eq_neg_of_sq_eq_square_nat T ht hT htrace

/-- The conductor-two obstruction at degree eight cannot be the unique
square trace sector. -/
theorem false_of_degreeEight_unique_conductorTwo_trace
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (T : E →ₗ[ℚ] E)
    (hT : T * T = (9 : ℚ) • LinearMap.id)
    (htrace : LinearMap.trace ℚ E T = -(8 : ℚ)) : False := by
  apply false_of_trace_eq_neg_of_sq_eq_square_nat_of_not_dvd
    T (d := 8) (t := 3) (by norm_num)
  · norm_num at hT ⊢
    exact hT
  · exact htrace
  · norm_num

/-- The rational `μ = 1` obstruction at degree eighteen cannot be the
unique square trace sector. -/
theorem false_of_degreeEighteen_unique_trace_four
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (T : E →ₗ[ℚ] E)
    (hT : T * T = (16 : ℚ) • LinearMap.id)
    (htrace : LinearMap.trace ℚ E T = -(18 : ℚ)) : False := by
  apply false_of_trace_eq_neg_of_sq_eq_square_nat_of_not_dvd
    T (d := 18) (t := 4) (by norm_num)
  · norm_num at hT ⊢
    exact hT
  · exact htrace
  · norm_num

/-- The conductor-four obstruction at degree twenty-six cannot be the
unique square trace sector. -/
theorem false_of_degreeTwentySix_unique_conductorFour_trace
    {E : Type*} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E]
    (T : E →ₗ[ℚ] E)
    (hT : T * T = (25 : ℚ) • LinearMap.id)
    (htrace : LinearMap.trace ℚ E T = -(26 : ℚ)) : False := by
  apply false_of_trace_eq_neg_of_sq_eq_square_nat_of_not_dvd
    T (d := 26) (t := 5) (by norm_num)
  · norm_num at hT ⊢
    exact hT
  · exact htrace
  · norm_num

end

end Erdos85
