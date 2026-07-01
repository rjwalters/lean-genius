import Mathlib

/-
# IVT — OQ-04: Bolzano's Theorem for Polynomials

## Research Problem: intermediate-value-theorem-oq-04

**Statement.** Every real polynomial of odd degree has a real root:
`P : ℝ[X]`, `Odd P.natDegree` ⟹ `∃ x, P.eval x = 0`.

This is the classical corollary of the Intermediate Value Theorem that is usually
stated informally as "an odd-degree curve must cross the axis". The parent gallery
entry `intermediate-value-theorem` states a *placeholder* version
`odd_degree_poly_has_root` for a generic continuous function that is *assumed* to take
both a negative and a positive value; it explicitly punts the polynomial case
("specific polynomial case follows from this"). The genuine mathematical content — the
part that is NOT a hypothesis — is precisely showing that an odd-degree polynomial
actually *attains both signs*. That is what this entry proves.

## Why the sign-attainment is the real theorem

A real polynomial `P` of odd degree behaves at the two ends of the real line like its
leading term `c·xⁿ` with `n` odd: as `x → +∞` it runs off to `+∞` (if `c > 0`) and as
`x → -∞` it runs off to `-∞`, because `(-x)ⁿ = -xⁿ` for odd `n`. So `P` takes arbitrarily
large positive and arbitrarily large negative values, and the IVT then forces a zero.
Mathlib supplies the two asymptotic facts
(`Polynomial.tendsto_atTop_of_leadingCoeff_nonneg`,
`Polynomial.tendsto_atBot_of_leadingCoeff_nonpos`); the odd-degree sign flip at `-∞` is
realised here by composing with `-X` (which negates the leading coefficient exactly when
the degree is odd) rather than by any hypothesis.

## Results
- `exists_neg_and_pos_of_pos_leadingCoeff` — an odd-degree polynomial with positive leading
  coefficient attains a negative value and a positive value (the sign-attainment lemma).
- `exists_root_of_both_signs` — IVT wrapper: a value `≤ 0` and a value `≥ 0` force a root.
- `exists_root_of_odd_natDegree` — **Bolzano.** Every odd-degree real polynomial has a root.
- `not_irreducible_of_odd_natDegree_ge_three` — structural corollary: no real polynomial of
  odd degree `≥ 3` is irreducible (it splits off a linear factor at the root).

All results are `sorry`-free and axiom-free (no `native_decide`).

Tags: analysis, ivt, bolzano, polynomials, real-roots, irreducibility
-/

open Polynomial Filter Topology

namespace IntermediateValueTheoremOQ04

/-- **Sign-attainment lemma.** A real polynomial of *odd* degree with *positive* leading
coefficient attains both a strictly negative value and a strictly positive value.

The positive value comes from `P(x) → +∞` as `x → +∞`. The negative value comes from
`P(x) → -∞` as `x → -∞`: we realise the left end by composing with `-X`, whose leading
coefficient `(-1)^{deg P} = -1` (odd degree) makes `P.comp (-X)` a polynomial with negative
leading coefficient, hence running off to `-∞` at `+∞`. -/
theorem exists_neg_and_pos_of_pos_leadingCoeff (P : ℝ[X]) (hodd : Odd P.natDegree)
    (hlc : 0 < P.leadingCoeff) :
    (∃ a : ℝ, P.eval a < 0) ∧ (∃ b : ℝ, 0 < P.eval b) := by
  have hpos_nd : 0 < P.natDegree := by rcases hodd with ⟨m, hm⟩; omega
  have hdeg : 0 < P.degree := natDegree_pos_iff_degree_pos.mp hpos_nd
  refine ⟨?_, ?_⟩
  · -- negative value: study `R = P.comp (-X)`, which has negative leading coefficient.
    set R := P.comp (-X) with hR
    have hne : (-X : ℝ[X]).natDegree ≠ 0 := by rw [natDegree_neg, natDegree_X]; exact one_ne_zero
    have hndR : R.natDegree = P.natDegree := by
      rw [hR, natDegree_comp, natDegree_neg, natDegree_X, mul_one]
    have hdegR : 0 < R.degree :=
      natDegree_pos_iff_degree_pos.mp (by rw [hndR]; exact hpos_nd)
    have hlcR : R.leadingCoeff ≤ 0 := by
      rw [hR, leadingCoeff_comp hne, leadingCoeff_neg, leadingCoeff_X, Odd.neg_one_pow hodd,
        mul_neg_one]
      linarith
    have htend : Tendsto (fun x => R.eval x) atTop atBot :=
      R.tendsto_atBot_of_leadingCoeff_nonpos hdegR hlcR
    obtain ⟨c, hc⟩ := (htend.eventually (eventually_lt_atBot 0)).exists
    refine ⟨-c, ?_⟩
    have hval : R.eval c = P.eval (-c) := by rw [hR, eval_comp, eval_neg, eval_X]
    rwa [hval] at hc
  · -- positive value: `P(x) → +∞` as `x → +∞`.
    have htend : Tendsto (fun x => P.eval x) atTop atTop :=
      P.tendsto_atTop_of_leadingCoeff_nonneg hdeg hlc.le
    exact (htend.eventually (eventually_gt_atTop 0)).exists

/-- IVT wrapper: if a real polynomial takes a value `≤ 0` and a value `≥ 0`, it has a root.
Immediate from `intermediate_value_univ₂` applied to `P.eval` and the zero function on the
(pre)connected space `ℝ`. -/
theorem exists_root_of_both_signs (P : ℝ[X]) {a b : ℝ}
    (ha : P.eval a ≤ 0) (hb : 0 ≤ P.eval b) : ∃ x : ℝ, P.eval x = 0 := by
  have h := intermediate_value_univ₂ (a := a) (b := b) P.continuous continuous_const ha hb
  simpa using h

/-- **Bolzano's theorem for polynomials.** Every real polynomial of odd degree has a real
root. The odd degree guarantees the leading term dominates with opposite signs at `±∞`, so
the polynomial attains both signs and the IVT delivers a zero. -/
theorem exists_root_of_odd_natDegree (P : ℝ[X]) (hodd : Odd P.natDegree) :
    ∃ x : ℝ, P.eval x = 0 := by
  have hP : P ≠ 0 := by
    rintro rfl; rw [natDegree_zero] at hodd; rcases hodd with ⟨m, hm⟩; omega
  rcases lt_trichotomy P.leadingCoeff 0 with hlc | hlc | hlc
  · -- negative leading coefficient: run the lemma on `-P` (same roots) and swap signs.
    have hodd' : Odd (-P).natDegree := by rwa [natDegree_neg]
    have hlc' : 0 < (-P).leadingCoeff := by rw [leadingCoeff_neg]; linarith
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := exists_neg_and_pos_of_pos_leadingCoeff (-P) hodd' hlc'
    rw [eval_neg] at ha hb
    -- `ha : -P.eval a < 0` (so `P.eval a > 0`), `hb : 0 < -P.eval b` (so `P.eval b < 0`)
    exact exists_root_of_both_signs P (show P.eval b ≤ 0 by linarith)
      (show (0 : ℝ) ≤ P.eval a by linarith)
  · exact absurd hlc (leadingCoeff_ne_zero.mpr hP)
  · obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := exists_neg_and_pos_of_pos_leadingCoeff P hodd hlc
    exact exists_root_of_both_signs P ha.le hb.le

/-- **Structural corollary.** No real polynomial of odd degree `≥ 3` is irreducible: it has a
real root by Bolzano, hence splits off a linear factor `X - C a`, leaving a cofactor of
degree `≥ 2`; neither factor is a unit, contradicting irreducibility. (Together with the
degree-2 case this is the odd half of "irreducible real polynomials have degree `≤ 2`".) -/
theorem not_irreducible_of_odd_natDegree_ge_three (P : ℝ[X])
    (hodd : Odd P.natDegree) (h3 : 3 ≤ P.natDegree) : ¬ Irreducible P := by
  obtain ⟨a, ha⟩ := exists_root_of_odd_natDegree P hodd
  intro hirr
  obtain ⟨Q, hQ⟩ := dvd_iff_isRoot.mpr ha
  rcases hirr.isUnit_or_isUnit hQ with hu | hu
  · -- `X - C a` cannot be a unit: it has degree `1`.
    have h := natDegree_eq_zero_of_isUnit hu
    rw [natDegree_X_sub_C] at h
    exact one_ne_zero h
  · -- `Q` a unit forces `natDegree P = 1`, contradicting `3 ≤ natDegree P`.
    have hQ0 : Q ≠ 0 := hu.ne_zero
    have hXne : (X - C a : ℝ[X]) ≠ 0 := X_sub_C_ne_zero a
    have hnd : P.natDegree = (X - C a).natDegree + Q.natDegree := by
      rw [hQ, natDegree_mul hXne hQ0]
    rw [natDegree_X_sub_C, natDegree_eq_zero_of_isUnit hu] at hnd
    omega

/-- A concrete instance: the cubic `X³ - X - 1` has a real root (odd degree `3`). -/
example : ∃ x : ℝ, (X ^ 3 - X - 1 : ℝ[X]).eval x = 0 := by
  apply exists_root_of_odd_natDegree
  have h : (X ^ 3 - X - 1 : ℝ[X]).natDegree = 3 := by compute_degree!
  rw [h]
  exact ⟨1, rfl⟩

#check @exists_root_of_odd_natDegree
#check @not_irreducible_of_odd_natDegree_ge_three

end IntermediateValueTheoremOQ04
