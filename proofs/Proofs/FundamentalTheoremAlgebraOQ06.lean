import Mathlib

/-
# Every Odd-Degree Real Polynomial Has a Real Root (Intermediate Value Form)

## What This Proves
Every polynomial `P ∈ ℝ[X]` of odd degree has a real root: `∃ x : ℝ, P.IsRoot x`.

This is the **odd-degree intermediate value step** singled out in the parent entry's
open question on Gauss's (1849) purely algebraic proof of the Fundamental Theorem of
Algebra. Gauss's argument reduces the analytic content of FTA to exactly two facts:
1. every odd-degree real polynomial has a real root (this entry), and
2. every complex number has a complex square root.

## Approach
A degree-`n` real polynomial with `n` odd behaves like `c · xⁿ` at infinity, and an odd
power flips sign between `+∞` and `−∞`. Concretely:

- `0 < P.degree`, and `P.eval` is continuous.
- The reflected polynomial `Q(x) = P(-x) = P.comp (-X)` has
  `leadingCoeff Q = (-1)^(deg P) · leadingCoeff P = -leadingCoeff P` (oddness),
  so `P` and `Q` have opposite end-behaviour at `+∞`.
- Whatever the sign of `leadingCoeff P`, one of `{P, Q}` tends to `+∞` and the other to
  `−∞` along `atTop`. Reading `Q.eval x = P.eval (-x)` back, `P.eval` therefore takes a
  strictly negative value at some `a` and a strictly positive value at some `b`.
- The intermediate value theorem on `[[a, b]]` then produces a root.

## Mathlib Ingredients
- `Polynomial.tendsto_atTop_of_leadingCoeff_nonneg` / `tendsto_atBot_of_leadingCoeff_nonpos`
- `Polynomial.leadingCoeff_comp`, `Polynomial.natDegree_comp`, `Polynomial.eval_comp`
- `intermediate_value_uIcc`, `Polynomial.continuousOn`
- `Polynomial.dvd_iff_isRoot`

Mathlib has no standalone "odd-degree real polynomial has a root" theorem; the result is
built here from the end-behaviour lemmas and the IVT.

Historical note: this is the ℝ-specialisation of the order-theoretic fact underlying
real-closed fields (Artin–Schreier, 1927); for ℝ it is the IVT step of Gauss's 1849 proof.
-/

open Polynomial Filter Topology

namespace FTAOddDegreeRoot

/-- An odd-degree real polynomial takes both a strictly negative and a strictly positive
value: the leading term dominates at `±∞` and an odd power flips sign. -/
theorem exists_neg_and_pos_eval (P : ℝ[X]) (hodd : Odd P.natDegree) :
    (∃ a : ℝ, P.eval a < 0) ∧ (∃ b : ℝ, 0 < P.eval b) := by
  obtain ⟨m, hm⟩ := hodd
  have hpos_deg : 0 < P.natDegree := by omega
  have hdeg : 0 < P.degree := natDegree_pos_iff_degree_pos.mp hpos_deg
  -- The reflected polynomial Q(x) = P(-x).
  set Q : ℝ[X] := P.comp (-X) with hQ
  have hnd_negX : (-X : ℝ[X]).natDegree = 1 := by rw [natDegree_neg, natDegree_X]
  have hlc_negX : (-X : ℝ[X]).leadingCoeff = -1 := by rw [leadingCoeff_neg, leadingCoeff_X]
  have hne : (-X : ℝ[X]).natDegree ≠ 0 := by rw [hnd_negX]; norm_num
  have hQdeg_nd : Q.natDegree = P.natDegree := by
    rw [hQ, natDegree_comp, hnd_negX, mul_one]
  have hQdeg : 0 < Q.degree := by
    rw [← natDegree_pos_iff_degree_pos, hQdeg_nd]; exact hpos_deg
  have hQlc : Q.leadingCoeff = -P.leadingCoeff := by
    rw [hQ, leadingCoeff_comp hne, hlc_negX, Odd.neg_one_pow ⟨m, hm⟩]; ring
  have hevalQ : ∀ x : ℝ, Q.eval x = P.eval (-x) := by
    intro x; rw [hQ, eval_comp]; simp
  rcases le_total 0 P.leadingCoeff with hlc | hlc
  · -- leadingCoeff P ≥ 0: P → +∞ (positive value); Q → −∞ (negative value of P at -x).
    have hP : Tendsto (fun x => P.eval x) atTop atTop :=
      P.tendsto_atTop_of_leadingCoeff_nonneg hdeg hlc
    have hb : ∃ b : ℝ, 0 < P.eval b := (hP.eventually (eventually_gt_atTop 0)).exists
    have hQlc_nonpos : Q.leadingCoeff ≤ 0 := by rw [hQlc]; linarith
    have hQt : Tendsto (fun x => Q.eval x) atTop atBot :=
      Q.tendsto_atBot_of_leadingCoeff_nonpos hQdeg hQlc_nonpos
    obtain ⟨x, hx⟩ := (hQt.eventually (eventually_lt_atBot 0)).exists
    rw [hevalQ] at hx
    exact ⟨⟨-x, hx⟩, hb⟩
  · -- leadingCoeff P ≤ 0: P → −∞ (negative value); Q → +∞ (positive value of P at -x).
    have hP : Tendsto (fun x => P.eval x) atTop atBot :=
      P.tendsto_atBot_of_leadingCoeff_nonpos hdeg hlc
    have ha : ∃ a : ℝ, P.eval a < 0 := (hP.eventually (eventually_lt_atBot 0)).exists
    have hQlc_nonneg : 0 ≤ Q.leadingCoeff := by rw [hQlc]; linarith
    have hQt : Tendsto (fun x => Q.eval x) atTop atTop :=
      Q.tendsto_atTop_of_leadingCoeff_nonneg hQdeg hQlc_nonneg
    obtain ⟨x, hx⟩ := (hQt.eventually (eventually_gt_atTop 0)).exists
    rw [hevalQ] at hx
    exact ⟨ha, ⟨-x, hx⟩⟩

/-- **Odd-degree real root theorem.** Every real polynomial of odd degree has a real root. -/
theorem odd_natDegree_has_real_root (P : ℝ[X]) (hodd : Odd P.natDegree) :
    ∃ x : ℝ, P.IsRoot x := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := exists_neg_and_pos_eval P hodd
  have hcont : ContinuousOn (fun x => P.eval x) (Set.uIcc a b) := P.continuousOn
  have h0mem : (0 : ℝ) ∈ Set.uIcc (P.eval a) (P.eval b) := by
    rw [Set.mem_uIcc]; exact Or.inl ⟨le_of_lt ha, le_of_lt hb⟩
  obtain ⟨c, _, hc⟩ := intermediate_value_uIcc hcont h0mem
  exact ⟨c, hc⟩

/-- Structural consequence: an odd-degree real polynomial has a linear factor `X - C x`. -/
theorem odd_natDegree_has_linear_factor (P : ℝ[X]) (hodd : Odd P.natDegree) :
    ∃ x : ℝ, (X - C x) ∣ P := by
  obtain ⟨x, hx⟩ := odd_natDegree_has_real_root P hodd
  exact ⟨x, dvd_iff_isRoot.mpr hx⟩

/-- Every odd-degree polynomial splits off a real root, so an **irreducible** real
polynomial of degree `> 1` must have **even** degree. (Quadratics such as `X² + 1`,
with no real root, are exactly the obstruction to ℝ being algebraically closed.) -/
theorem natDegree_even_of_irreducible_of_one_lt
    (P : ℝ[X]) (hirr : Irreducible P) (h1 : 1 < P.natDegree) : Even P.natDegree := by
  rcases Nat.even_or_odd P.natDegree with he | hodd
  · exact he
  exfalso
  obtain ⟨x, q, hq⟩ := odd_natDegree_has_linear_factor P hodd
  rcases hirr.isUnit_or_isUnit hq with hu | hu
  · -- `X - C x` a unit: impossible, its natDegree is `1 ≠ 0`.
    have h1deg : (X - C x : ℝ[X]).natDegree = 1 := natDegree_X_sub_C x
    have h0deg : (X - C x : ℝ[X]).natDegree = 0 := natDegree_eq_zero_of_isUnit hu
    omega
  · -- the cofactor `q` a unit: then `natDegree P = 1`, contradicting `1 < natDegree P`.
    have hqne : q ≠ 0 := by rintro rfl; rw [mul_zero] at hq; exact hirr.ne_zero hq
    have hqdeg : q.natDegree = 0 := natDegree_eq_zero_of_isUnit hu
    have hPdeg : P.natDegree = 1 := by
      rw [hq, natDegree_mul (X_sub_C_ne_zero x) hqne, natDegree_X_sub_C, hqdeg]
    omega

end FTAOddDegreeRoot
