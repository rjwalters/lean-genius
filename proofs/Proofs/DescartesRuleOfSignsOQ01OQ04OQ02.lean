import Mathlib

/-
# Descartes' Rule of Signs, OQ-01-OQ-04-OQ-02: exact positive-root count in the boundary cases

## Background

Descartes' Rule of Signs (Mathlib's `Polynomial.roots_countP_pos_le_signVariations`) gives only an
*upper bound*: the number of positive roots of a real polynomial is at most its number of sign
variations,

      #{positive roots} ≤ signVariations P.

The *parity refinement* sharpens this to `#{positive roots} ≡ signVariations P (mod 2)`, which would
pin the count exactly in the two boundary cases `signVariations P ∈ {0, 1}`. But the parity
refinement is the genuinely hard, FTA-flavoured content of Descartes' Rule (the statement
`[sign p(a) ≠ sign p(b)] ⟺ Odd #{roots in (a,b)}`), and it is *not* available in Mathlib nor in the
gallery — every gallery file that uses parity takes `Even (signVariations + #pos)` as a hypothesis.

## What this file proves (and why it sidesteps the open parity)

The key observation is that the **boundary cases need only the sign-change root *existence*, not the
full odd-multiplicity parity**:

* `signVariations P = 0` ⟹ `#{positive roots} = 0` — immediate from Descartes' bound alone
  (`no_pos_roots_of_signVariations_zero`).
* `signVariations P = 1` ⟹ `#{positive roots} = 1` — the bound gives `≤ 1`; the *lower* bound `≥ 1`
  needs only that *one* positive root exists. And a positive root exists as soon as the leading and
  trailing coefficients have **opposite signs**, by the Intermediate Value Theorem
  (`exists_pos_root_of_sign_opposition`, `exactly_one_pos_root_of_sign_opposition`).

The analytic argument is the content. Factor out the largest power of `X`, writing `P = Xᵐ · Q` with
`Q.eval 0 = trailingCoeff ≠ 0` and `Q.leadingCoeff = P.leadingCoeff`. The deflated `Q` has positive
degree (else `P` is a monomial, whose leading and trailing coefficients coincide — excluded by the
sign opposition), so `Q.eval` tends to `±∞` with the sign of its leading coefficient; pick `b > 0`
where `Q.eval b` carries that sign. Since `Q.eval 0` carries the opposite (trailing) sign, the
Intermediate Value Theorem produces `c ∈ (0, b)` with `Q.eval c = 0`, hence `P.eval c = cᵐ·Q.eval c =
0`. **This existence-by-IVT is exactly what replaces the unavailable parity argument in the boundary
case, and it is fully machine-checked here.**

## Honesty / scope

Stated over `ℝ` (not `ℚ`): over `ℚ` the exact count is *false* — `X² - 2` has one sign variation but
no rational positive root. The "exactly one" statement is genuinely a real-closed-field phenomenon,
recovered here from completeness via the IVT.

The sign opposition `sign(leadingCoeff) ≠ sign(trailingCoeff)` is taken as a hypothesis: it is the
purely combinatorial consequence of a single sign variation (the coefficient sign-sequence changes
exactly once, so its endpoints lie in opposite blocks), and carries no analytic or FTA content. The
file therefore reduces the open boundary-exact-count to that one combinatorial bridge plus the
*verified* IVT existence — entirely bypassing the open parity refinement.

Main results:
* `no_pos_roots_of_signVariations_zero`        — `0` sorries, `0` axioms
* `exists_pos_root_of_sign_opposition`         — `0` sorries, `0` axioms
* `exactly_one_pos_root_of_sign_opposition`    — `0` sorries, `0` axioms
-/

namespace DescartesExactCount

open Polynomial Filter

variable {P : ℝ[X]}

/-! ## The easy boundary case: zero sign variations ⟹ no positive roots -/

/-- **Boundary case `signVariations = 0`.** A real polynomial with no sign variations has no positive
roots. Immediate from Descartes' bound — no parity needed. -/
theorem no_pos_roots_of_signVariations_zero (h : P.signVariations = 0) :
    P.roots.countP (0 < ·) = 0 := by
  have hle := P.roots_countP_pos_le_signVariations
  rw [h] at hle
  exact Nat.le_zero.mp hle

/-! ## Existence of a positive root from opposite leading/trailing signs (IVT) -/

/-- **Opposite leading/trailing signs force a positive root.** If the leading and trailing
coefficients of a nonzero real polynomial have strictly opposite signs, then `P` has a root in
`(0, ∞)`. This is the Intermediate Value Theorem applied to the polynomial deflated by the largest
power of `X`; it is the analytic core that replaces the parity argument in the boundary case. -/
theorem exists_pos_root_of_sign_opposition (hP : P ≠ 0)
    (hopp : SignType.sign P.leadingCoeff ≠ SignType.sign P.trailingCoeff) :
    ∃ x : ℝ, 0 < x ∧ P.eval x = 0 := by
  -- factor out the largest power of X:  P = X^m * Q
  obtain ⟨Q, hPQ⟩ := pow_rootMultiplicity_dvd P 0
  rw [map_zero, sub_zero] at hPQ
  set m := rootMultiplicity 0 P with hm
  have hQne : Q ≠ 0 := by
    rintro rfl; rw [mul_zero] at hPQ; exact hP hPQ
  -- maximality of the root multiplicity ⟹ deflated constant term is nonzero
  have hmax : ¬ (X : ℝ[X]) ^ (m + 1) ∣ P := by
    have h1 := (rootMultiplicity_le_iff hP 0 m).mp le_rfl
    rwa [map_zero, sub_zero] at h1
  have hQ0 : Q.eval 0 ≠ 0 := by
    intro hQe
    refine hmax ?_
    have hdvd : (X : ℝ[X]) ∣ Q := by
      have hr : IsRoot Q 0 := hQe
      rw [← dvd_iff_isRoot] at hr
      rwa [map_zero, sub_zero] at hr
    obtain ⟨R, rfl⟩ := hdvd
    exact ⟨R, by rw [hPQ]; ring⟩
  -- leading coefficient is unchanged by deflation
  have hlead : P.leadingCoeff = Q.leadingCoeff := by
    rw [hPQ, leadingCoeff_mul, leadingCoeff_X_pow, one_mul]
  -- trailing coefficient equals the deflated constant term
  have hQ0coeff : Q.coeff 0 ≠ 0 := by rwa [coeff_zero_eq_eval_zero]
  have htrail : P.trailingCoeff = Q.eval 0 := by
    have hQnT : Q.natTrailingDegree = 0 := natTrailingDegree_eq_zero.mpr (Or.inr hQ0coeff)
    have hPnT : P.natTrailingDegree = m := by
      rw [hPQ, show (X : ℝ[X]) ^ m * Q = Q * X ^ m from by ring,
        natTrailingDegree_mul_X_pow hQne, hQnT, zero_add]
    have hcoeff : (X ^ m * Q).coeff m = Q.coeff 0 := by
      have := coeff_X_pow_mul Q m 0
      rwa [zero_add] at this
    rw [trailingCoeff, hPnT, hPQ, hcoeff, coeff_zero_eq_eval_zero]
  -- the deflated polynomial has positive degree (else P is a monomial: leading = trailing sign)
  have hQdeg : 0 < Q.degree := by
    rw [← natDegree_pos_iff_degree_pos]
    by_contra hcon
    push_neg at hcon
    have hnd : Q.natDegree = 0 := Nat.le_zero.mp hcon
    have hlc_eq : Q.leadingCoeff = Q.eval 0 := by
      rw [leadingCoeff, hnd, coeff_zero_eq_eval_zero]
    exact hopp (by rw [hlead, htrail, hlc_eq])
  -- abbreviations
  have hcont : Continuous fun x : ℝ => Q.eval x := Q.continuous
  rw [hlead, htrail] at hopp
  have hQlc : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQne
  -- the deflated root transports back to a root of P
  have hback : ∀ c : ℝ, Q.eval c = 0 → P.eval c = 0 := fun c hc => by
    rw [hPQ, eval_mul, hc, mul_zero]
  -- split on the sign of the leading coefficient; the opposition fixes the other sign
  rcases lt_or_gt_of_ne hQlc with hlcneg | hlcpos
  · -- leadingCoeff < 0, hence Q.eval 0 > 0
    have hQ0pos : 0 < Q.eval 0 := by
      rcases lt_or_gt_of_ne hQ0 with h | h
      · exact absurd (by rw [sign_eq_neg_one_iff.mpr hlcneg, sign_eq_neg_one_iff.mpr h]) hopp
      · exact h
    -- Q.eval → -∞, so some b > 0 has Q.eval b < 0
    have hT : Tendsto (fun x : ℝ => Q.eval x) atTop atBot :=
      Q.tendsto_atBot_of_leadingCoeff_nonpos hQdeg hlcneg.le
    obtain ⟨b, hb0, hbneg⟩ : ∃ b : ℝ, 0 < b ∧ Q.eval b < 0 :=
      ((eventually_gt_atTop 0).and (hT.eventually (eventually_lt_atBot 0))).exists
    -- IVT: 0 lies between Q.eval b < 0 and Q.eval 0 > 0
    obtain ⟨c, hcmem, hc0⟩ :=
      intermediate_value_Icc' hb0.le hcont.continuousOn ⟨hbneg.le, hQ0pos.le⟩
    have hcne : c ≠ 0 := by rintro rfl; exact hQ0 hc0
    exact ⟨c, hcmem.1.lt_of_ne (Ne.symm hcne), hback c hc0⟩
  · -- leadingCoeff > 0, hence Q.eval 0 < 0
    have hQ0neg : Q.eval 0 < 0 := by
      rcases lt_or_gt_of_ne hQ0 with h | h
      · exact h
      · exact absurd (by rw [sign_eq_one_iff.mpr hlcpos, sign_eq_one_iff.mpr h]) hopp
    -- Q.eval → +∞, so some b > 0 has Q.eval b > 0
    have hT : Tendsto (fun x : ℝ => Q.eval x) atTop atTop :=
      Q.tendsto_atTop_of_leadingCoeff_nonneg hQdeg hlcpos.le
    obtain ⟨b, hb0, hbpos⟩ : ∃ b : ℝ, 0 < b ∧ 0 < Q.eval b :=
      ((eventually_gt_atTop 0).and (hT.eventually (eventually_gt_atTop 0))).exists
    -- IVT: 0 lies between Q.eval 0 < 0 and Q.eval b > 0
    obtain ⟨c, hcmem, hc0⟩ :=
      intermediate_value_Icc hb0.le hcont.continuousOn ⟨hQ0neg.le, hbpos.le⟩
    have hcne : c ≠ 0 := by rintro rfl; exact hQ0 hc0
    exact ⟨c, hcmem.1.lt_of_ne (Ne.symm hcne), hback c hc0⟩

/-! ## The boundary result, conditional on the sign opposition -/

/-- **Boundary case `signVariations = 1`, given the sign opposition.** A real polynomial with exactly
one sign variation whose leading and trailing coefficients have opposite signs has exactly one
positive root (with multiplicity). The upper bound `≤ 1` is Descartes' Rule; the lower bound `≥ 1` is
the IVT existence of a positive root. No parity refinement is used.

The hypothesis `hopp` is the only non-analytic input; it is the purely combinatorial consequence of a
single sign variation. -/
theorem exactly_one_pos_root_of_sign_opposition (h : P.signVariations = 1)
    (hopp : SignType.sign P.leadingCoeff ≠ SignType.sign P.trailingCoeff) :
    P.roots.countP (0 < ·) = 1 := by
  have hP : P ≠ 0 := by rintro rfl; simp at h
  have hle : P.roots.countP (0 < ·) ≤ 1 := by
    have := P.roots_countP_pos_le_signVariations; rw [h] at this; exact this
  obtain ⟨x, hx0, hxroot⟩ := exists_pos_root_of_sign_opposition hP hopp
  have hxmem : x ∈ P.roots := (mem_roots hP).mpr hxroot
  have hge : 1 ≤ P.roots.countP (0 < ·) := Multiset.countP_pos_of_mem hxmem hx0
  omega

end DescartesExactCount

-- Axiom audit: only the standard foundational axioms — no `Lean.ofReduceBool`
-- (no `native_decide`) and no `sorryAx`.
#print axioms DescartesExactCount.no_pos_roots_of_signVariations_zero
#print axioms DescartesExactCount.exists_pos_root_of_sign_opposition
#print axioms DescartesExactCount.exactly_one_pos_root_of_sign_opposition
