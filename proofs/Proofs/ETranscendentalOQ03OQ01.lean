/-
  e-transcendental-oq-03-oq-01

  Continued-fraction convergent quality: feasibility of formalizing μ(e) = 2
  via Mathlib's `GenContFract` (GeneralizedContinuedFraction) API.

  ════════════════════════════════════════════════════════════════════════════
  ⚠ VERIFICATION STATUS: UNVERIFIED DRAFT — DO NOT MARK "verified".
  This file was authored in a session with NO working Lean build (Docker daemon
  down, no host elan/lake toolchain, Aristotle prover API returning HTTP 404).
  The upper-bound proof below is a best-effort attempt against the documented
  Mathlib API and has NOT been compiled. The lower bound (`convs_dist_lower`)
  is the genuinely new content and is left as a structured `sorry` with its
  proof route. Build & verify before relying on anything here, and before wiring
  to the gallery.
  ════════════════════════════════════════════════════════════════════════════

  PURPOSE.  The parent entry `e-transcendental-oq-03` proves μ(e) = 2 modulo one
  axiom, `e_not_liouvilleWith_gt_two` (the μ(e) ≤ 2 half).  Closing it needs a
  two-sided bracket on continued-fraction convergent error:

      1 / (qₙ (qₙ₊₁ + qₙ))  <  |v - pₙ/qₙ|  ≤  1 / (qₙ qₙ₊₁),     qₙ := (of v).dens n.

  Mathlib supplies the RIGHT inequality (`GenContFract.abs_sub_convs_le`) and the
  exact error identity (`GenContFract.sub_convs_eq`), but NOT the LEFT inequality
  as a public lemma.  `convs_dist_lower` below fills that gap; it is e-independent
  and is the natural upstream contribution.  See
  `research/problems/e-transcendental-oq-03-oq-01/knowledge.md` for the full gap
  analysis (the remaining deep blocker is Euler's CF expansion of e, absent from
  Mathlib).
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
`qₙ ≥ fib(n+1) ≥ 1`).

⚠ UNVERIFIED — best-effort proof, not compiled this session. -/
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
(continued fraction not terminated at `n`) is no closer than
`1 / (qₙ (qₙ₊₁ + qₙ))`.  Together with `convs_dist_le_one_div_den_sq` this gives
the two-sided bracket that pins the irrationality measure of numbers with
controlled partial-quotient growth.

PROOF ROUTE (from `GenContFract.sub_convs_eq`):
  Let `ifp := IntFractPair.stream v n` (some, as `¬ TerminatedAt n`), `Bₙ := qₙ`,
  `Bₙ₋₁ := (contsAux n).b`.  Then `sub_convs_eq` gives
      v - convs n = (-1)^n / (Bₙ (ifp.fr⁻¹ Bₙ + Bₙ₋₁)),
  so |v - convs n| = 1 / (Bₙ (ifp.fr⁻¹ Bₙ + Bₙ₋₁)).
  Since `ifp.fr⁻¹ < bₙ₊₁ + 1` (`0 ≤ fract(ifp.fr⁻¹) < 1`, via
  `IntFractPair.nth_stream_fr_lt_one`) and the continuant recurrence
  `contsAux_recurrence` gives `qₙ₊₁ = bₙ₊₁ Bₙ + Bₙ₋₁`, we obtain
      ifp.fr⁻¹ Bₙ + Bₙ₋₁ < (bₙ₊₁+1) Bₙ + Bₙ₋₁ = qₙ₊₁ + qₙ,
  and `qₙ > 0`, giving the strict bound.

⚠ UNVERIFIED — proof not completed/compiled this session. -/
theorem convs_dist_lower (h : ¬ (of v).TerminatedAt n) :
    1 / ((of v).dens n * ((of v).dens (n + 1) + (of v).dens n))
      < |v - (of v).convs n| := by
  sorry

end ETranscendentalOQ03OQ01
