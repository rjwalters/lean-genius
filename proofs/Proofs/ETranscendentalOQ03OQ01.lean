/-
  e-transcendental-oq-03-oq-01

  Continued-fraction convergent quality: the two-sided error bracket underlying
  the irrationality measure μ(e) = 2, formalized against Mathlib's `GenContFract`
  (GeneralizedContinuedFraction) API.

  ────────────────────────────────────────────────────────────────────────────
  RESULT.  For any real `v` whose regular continued fraction has not terminated
  by step `n` (in particular, any irrational `v`), the `n`-th convergent
  `pₙ/qₙ := (of v).convs n` satisfies the sharp two-sided bracket

      1 / (qₙ (qₙ₊₁ + qₙ))  <  |v - pₙ/qₙ|  ≤  1 / qₙ²,       qₙ := (of v).dens n.

  Mathlib supplies the RIGHT inequality (`GenContFract.abs_sub_convs_le`, giving
  `≤ 1/(qₙ qₙ₊₁)`) and the exact error identity (`GenContFract.sub_convs_eq`),
  but NOT the LEFT (lower) inequality as a public lemma.  `convs_dist_lower`
  below fills that gap.  It is e-independent — the natural upstream contribution
  — and is exactly the ingredient needed to turn "partial quotients aₙ = O(n)"
  into "irrationality measure ≤ 2".

  ────────────────────────────────────────────────────────────────────────────
  RELATION TO THE PARENT.  The parent entry `e-transcendental-oq-03` proves
  μ(e) = 2 modulo one axiom, `e_not_liouvilleWith_gt_two` (the μ(e) ≤ 2 half).
  Closing that axiom needs two things: (1) this general convergent lower bound,
  and (2) Euler's specific continued-fraction expansion of e together with the
  bound aₙ = O(n) on its partial quotients (Hermite / Cohn).  This file delivers
  (1), the tractable e-independent half; (2) — the CF expansion of e — is absent
  from Mathlib and remains the genuine deep obstruction.  See
  `research/problems/e-transcendental-oq-03-oq-01/knowledge.md` for the full gap
  analysis.
-/
import Mathlib

open GenContFract

namespace ETranscendentalOQ03OQ01

variable {v : ℝ} {n : ℕ}

/-- **Upper bound (sharpened, `1/qₙ²` form).**  For any real `v` whose continued
fraction has not terminated by step `n`, the `n`-th convergent approximates `v`
to within `1 / qₙ²`.  Immediate from `GenContFract.abs_sub_convs_le`
(`|v - convs n| ≤ 1/(qₙ qₙ₊₁)`) together with denominator monotonicity
(`of_den_mono`, `qₙ ≤ qₙ₊₁`) and positivity (`succ_nth_fib_le_of_nth_den`,
`qₙ ≥ fib(n+1) ≥ 1`). -/
theorem convs_dist_le_one_div_den_sq (h : ¬ (of v).TerminatedAt n) :
    |v - (of v).convs n| ≤ 1 / ((of v).dens n) ^ 2 := by
  have hub := abs_sub_convs_le (v := v) (n := n) h
  -- qₙ ≥ fib (n+1) ≥ 1 > 0
  have hfib : ((Nat.fib (n + 1) : ℕ) : ℝ) ≤ (of v).dens n :=
    succ_nth_fib_le_of_nth_den (v := v)
      (Or.inr (mt (terminated_stable (Nat.sub_le n 1)) h))
  have hpos : (0 : ℝ) < (of v).dens n :=
    lt_of_lt_of_le (by exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos n)) hfib
  have hmono : (of v).dens n ≤ (of v).dens (n + 1) := of_den_mono
  refine hub.trans ?_
  rw [sq]
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith [hpos, hmono]

/-- **Lower bound (the Mathlib gap).**  The `n`-th convergent of any real `v`
whose continued fraction is not terminated at `n` is no closer than
`1 / (qₙ (qₙ₊₁ + qₙ))`.  Together with `convs_dist_le_one_div_den_sq` this gives
the two-sided bracket that pins the irrationality measure of numbers with
controlled partial-quotient growth.

The proof is the strict companion of `GenContFract.abs_sub_convs_le`: from the
exact error identity `sub_convs_eq`,
`|v - convs n| = 1 / (Bₙ (frₙ⁻¹ Bₙ + Bₙ₋₁))`, and the strict bound
`frₙ⁻¹ < bₙ₊₁ + 1` (because `bₙ₊₁ = ⌊frₙ⁻¹⌋`), together with the continuant
recurrence `Bₙ₊₁ = bₙ₊₁ Bₙ + Bₙ₋₁`, one gets
`frₙ⁻¹ Bₙ + Bₙ₋₁ < Bₙ₊₁ + Bₙ`, hence the claim. -/
theorem convs_dist_lower (h : ¬ (of v).TerminatedAt n) :
    1 / ((of v).dens n * ((of v).dens (n + 1) + (of v).dens n))
      < |v - (of v).convs n| := by
  -- Continuant shorthand: Bₙ = conts.b, Bₙ₋₁ = pred_conts.b, Bₙ₊₁ = nextConts.b.
  set conts := (of v).contsAux (n + 1) with conts_eq
  set pred_conts := (of v).contsAux n with pred_conts_eq
  set nextConts := (of v).contsAux (n + 2) with nextConts_eq
  have hdn : (of v).dens n = conts.b := by
    rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux, conts_eq]
  have hdn1 : (of v).dens (n + 1) = nextConts.b := by
    rw [den_eq_conts_b, nth_cont_eq_succ_nth_contAux, nextConts_eq]
  -- Stream / partial-denominator data at index n.
  obtain ⟨gp, s_nth_eq⟩ : ∃ gp, (of v).s.get? n = some gp :=
    Option.ne_none_iff_exists'.1 h
  have gp_a_eq_one : gp.a = 1 := of_partNum_eq_one (partNum_eq_s_a s_nth_eq)
  -- Continuant recurrence: Bₙ₊₁ = Bₙ₋₁ + bₙ₊₁ Bₙ.
  have nextConts_b_eq : nextConts.b = pred_conts.b + gp.b * conts.b := by
    simp [nextConts_eq, contsAux_recurrence s_nth_eq pred_conts_eq conts_eq, gp_a_eq_one,
      pred_conts_eq.symm, conts_eq.symm, add_comm]
  obtain ⟨ifp_succ_n, succ_nth_stream_eq, ifp_succ_n_b_eq_gp_b⟩ :
      ∃ ifp, IntFractPair.stream v (n + 1) = some ifp ∧ (ifp.b : ℝ) = gp.b :=
    IntFractPair.exists_succ_get?_stream_of_gcf_of_get?_eq_some s_nth_eq
  obtain ⟨ifp_n, stream_nth_eq, stream_nth_fr_ne_zero, if_of_eq_ifp_succ_n⟩ :
      ∃ ifp, IntFractPair.stream v n = some ifp ∧ ifp.fr ≠ 0
        ∧ IntFractPair.of ifp.fr⁻¹ = ifp_succ_n :=
    IntFractPair.succ_nth_stream_eq_some_iff.1 succ_nth_stream_eq
  -- Positivity of the continuant denominators (Fibonacci lower bounds).
  have conts_b_ineq : (Nat.fib (n + 1) : ℝ) ≤ conts.b :=
    haveI : ¬(of v).TerminatedAt (n - 1) := mt (terminated_stable n.pred_le) h
    fib_le_of_contsAux_b <| Or.inr this
  have zero_lt_conts_b : (0 : ℝ) < conts.b :=
    conts_b_ineq.trans_lt' <| by exact_mod_cast Nat.fib_pos.2 n.succ_pos
  have zero_le_pred : (0 : ℝ) ≤ pred_conts.b := by
    have hfib : (Nat.fib n : ℝ) ≤ pred_conts.b :=
      haveI : ¬(of v).TerminatedAt (n - 2) := mt (terminated_stable (n.sub_le 2)) h
      fib_le_of_contsAux_b <| Or.inr this
    exact le_trans (by positivity) hfib
  -- Positivity of the n-th fractional part and its inverse.
  have zero_lt_fr : (0 : ℝ) < ifp_n.fr :=
    (IntFractPair.nth_stream_fr_nonneg stream_nth_eq).lt_of_ne' stream_nth_fr_ne_zero
  have zero_lt_fr_inv : (0 : ℝ) < ifp_n.fr⁻¹ := inv_pos.2 zero_lt_fr
  -- KEY strict bound: frₙ⁻¹ < bₙ₊₁ + 1, since bₙ₊₁ = ⌊frₙ⁻¹⌋.
  have hb_eq : ((ifp_succ_n.b : ℝ)) = (⌊ifp_n.fr⁻¹⌋ : ℝ) := by
    rw [← if_of_eq_ifp_succ_n]; simp [IntFractPair.of]
  have key : ifp_n.fr⁻¹ < (gp.b : ℝ) + 1 := by
    rw [← ifp_succ_n_b_eq_gp_b, hb_eq]; exact Int.lt_floor_add_one _
  -- Exact error term |v - convs n| = 1 / (Bₙ (frₙ⁻¹ Bₙ + Bₙ₋₁)).
  set den' := conts.b * (ifp_n.fr⁻¹ * conts.b + pred_conts.b) with den'_eq
  have zero_lt_den' : (0 : ℝ) < den' := by rw [den'_eq]; positivity
  have habs : |v - (of v).convs n| = 1 / den' := by
    have hEq := sub_convs_eq (v := v) (n := n) stream_nth_eq
    simp only [stream_nth_fr_ne_zero, if_false, ← conts_eq, ← pred_conts_eq, ← den'_eq] at hEq
    rw [hEq, abs_div, abs_neg_one_pow, abs_of_pos zero_lt_den']
  -- Assemble: 1/(Bₙ(Bₙ₊₁+Bₙ)) < 1/den' via den' < Bₙ(Bₙ₊₁+Bₙ).
  rw [habs, hdn, hdn1]
  apply one_div_lt_one_div_of_lt zero_lt_den'
  rw [den'_eq, nextConts_b_eq]
  nlinarith [key, zero_lt_conts_b, zero_le_pred,
    mul_pos zero_lt_conts_b zero_lt_conts_b]

/-- **Two-sided convergent bracket.**  Combining the two bounds above:
`1 / (qₙ (qₙ₊₁ + qₙ)) < |v - pₙ/qₙ| ≤ 1 / qₙ²` for any non-terminating index. -/
theorem convs_dist_bracket (h : ¬ (of v).TerminatedAt n) :
    1 / ((of v).dens n * ((of v).dens (n + 1) + (of v).dens n)) < |v - (of v).convs n|
      ∧ |v - (of v).convs n| ≤ 1 / ((of v).dens n) ^ 2 :=
  ⟨convs_dist_lower h, convs_dist_le_one_div_den_sq h⟩

end ETranscendentalOQ03OQ01
