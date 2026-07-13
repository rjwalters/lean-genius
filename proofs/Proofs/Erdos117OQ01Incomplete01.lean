/-
  Erdős #117 OQ-01 (incomplete-01): the oscillation of the growth rate

  Companion to `Proofs.Erdos117OQ01`, which studies whether the normalized
  logarithmic growth rate `growthRate n = log(h n)/n` of the abelian covering
  number `h(n)` converges (equivalently, whether `h(n)` has a single exponential
  base — Erdős #117 OQ-01).  The parent pins the open question down to the
  cluster values `growthRateLimInf`, `growthRateLimSup` and their difference
  (the *oscillation* `limsup − liminf`), and shows

      converges ⟺ liminf = limsup ⟺ oscillation = 0 ⟺ exponential base exists,

  together with the one-sided window bound
  `oscillation ≤ log c₂ − log c₁` (`growthRate_oscillation_le_window`).

  This file supplies the missing lower side and the negation form, so the
  oscillation is fully trapped and the open question has a clean "is the
  oscillation strictly positive?" phrasing.  All results are proved from the
  parent's API and add **no new axioms** (they inherit only the parent's three
  Pyber-bound assumptions `h`, `h_pos`, `pyber_bounds`).

  ## What this file proves (0 new axioms, 0 sorries)

  * `growthRate_oscillation_nonneg` — `0 ≤ limsup − liminf` (from `limInf_le_limSup`).
  * `oscillation_mem_window` — the oscillation lies in `[0, log c₂ − log c₁]`,
    combining the new lower bound with the parent's upper bound.
  * `exponentialBaseExists_iff_oscillation_zero` — the open question restated:
    a single exponential base exists iff the oscillation vanishes.
  * `not_exponentialBaseExists_iff_oscillation_pos` — the negation: **no** single
    base exists iff the oscillation is strictly positive (`0 < limsup − liminf`),
    the crispest form of "does the limit fail to exist?".

  Parent: Erdos117OQ01.lean
-/

import Mathlib
import Proofs.Erdos117OQ01

open Real Filter

namespace Erdos117OQ01Incomplete01

open Erdos117OQ01

/-- **The oscillation is nonnegative.**  `0 ≤ growthRateLimSup − growthRateLimInf`:
the limsup of a sequence always dominates its liminf (`limInf_le_limSup`).  The lower
companion of `growthRate_oscillation_le_window`, so the oscillation of the growth rate is
trapped in `[0, log c₂ − log c₁]`. -/
theorem growthRate_oscillation_nonneg :
    0 ≤ growthRateLimSup - growthRateLimInf :=
  sub_nonneg.mpr limInf_le_limSup

/-- **The oscillation lies in Pyber's log-window.**  Combining the new lower bound
`growthRate_oscillation_nonneg` with the parent's upper bound
`growthRate_oscillation_le_window`, the oscillation `limsup − liminf` of the growth rate
is trapped in `[0, log c₂ − log c₁]` for Pyber's constants `1 < c₁ < c₂`.  Even without
knowing whether the limit exists, the amount by which the growth rate can oscillate is
bounded by the fixed log-width of Pyber's exponential window. -/
theorem oscillation_mem_window :
    ∃ c₁ c₂ : ℝ, 1 < c₁ ∧ c₁ < c₂ ∧
      0 ≤ growthRateLimSup - growthRateLimInf ∧
      growthRateLimSup - growthRateLimInf ≤ Real.log c₂ - Real.log c₁ := by
  obtain ⟨c₁, c₂, h1, h12, hle⟩ := growthRate_oscillation_le_window
  exact ⟨c₁, c₂, h1, h12, growthRate_oscillation_nonneg, hle⟩

/-- **The open question ⟺ zero oscillation.**  Chaining
`exponentialBaseExists_iff_converges` with `converges_iff_oscillation_zero`:
`h(n)` has a single exponential base iff the oscillation `limsup − liminf` of the growth
rate is exactly `0`.  The oscillation form of `exponentialBaseExists_iff_limInfEqLimSup`. -/
theorem exponentialBaseExists_iff_oscillation_zero :
    exponentialBaseExists ↔ growthRateLimSup - growthRateLimInf = 0 :=
  exponentialBaseExists_iff_converges.trans converges_iff_oscillation_zero

/-- **The negation of the open question ⟺ strictly positive oscillation.**  No single
exponential base exists iff the oscillation is strictly positive: since the oscillation is
nonnegative (`growthRate_oscillation_nonneg`), failing to vanish means being `> 0`.  This
is the crispest form of "the limit `lim log h(n)/n` fails to exist" — it is exactly the
statement that the growth rate genuinely oscillates within Pyber's window. -/
theorem not_exponentialBaseExists_iff_oscillation_pos :
    ¬ exponentialBaseExists ↔ 0 < growthRateLimSup - growthRateLimInf := by
  rw [exponentialBaseExists_iff_oscillation_zero]
  exact ⟨fun h => lt_of_le_of_ne growthRate_oscillation_nonneg (Ne.symm h), fun h => h.ne'⟩

/-- **Both endpoints of the oscillation lie in Pyber's window individually.**  The parent's
`limInfLimSup_window` bounds `growthRateLimInf` from *below* by `log c₁` and `growthRateLimSup`
from *above* by `log c₂`.  Chaining with `limInf_le_limSup` closes the gap: *each* of the
liminf and the limsup lies in the full closed window `[log c₁, log c₂]`.  This is the
individual-endpoint companion of `oscillation_mem_window` (which traps only their *difference*),
and in particular shows both are genuine finite reals confined to Pyber's exponential window,
whether or not the growth rate converges. -/
theorem limInf_limSup_mem_window :
    ∃ c₁ c₂ : ℝ, 1 < c₁ ∧ c₁ < c₂ ∧
      growthRateLimInf ∈ Set.Icc (Real.log c₁) (Real.log c₂) ∧
      growthRateLimSup ∈ Set.Icc (Real.log c₁) (Real.log c₂) := by
  obtain ⟨c₁, c₂, hc1, hc12, hlo, hhi⟩ := limInfLimSup_window
  have hle := limInf_le_limSup
  exact ⟨c₁, c₂, hc1, hc12, ⟨hlo, hle.trans hhi⟩, ⟨hlo.trans hle, hhi⟩⟩

/-! ### A sufficient condition that resolves the open question: submultiplicativity

The results above only *characterise* the open question (as "is the oscillation
positive?").  This section supplies the first *sufficient condition* that answers it,
lifting the parent's Fekete result `submultiplicative_implies_convergence` into the
oscillation / exponential-base language of this file: if the covering number `h` is
submultiplicative (`h(m+n) ≤ h(m)·h(n)`), the oscillation vanishes, a single exponential
base exists, and the open question is resolved *yes*.  Contrapositively, a genuinely
oscillating growth rate (no exponential base) forces `h` to violate submultiplicativity —
a concrete necessary condition on any counterexample to Erdős #117 OQ-01. -/

/-- **Submultiplicativity ⟹ zero oscillation.**  If `h(m+n) ≤ h(m)·h(n)` for all `m, n`,
then the oscillation `limsup − liminf` of the growth rate is exactly `0`.  Fekete's lemma
(`submultiplicative_implies_convergence`) gives convergence, and
`converges_iff_oscillation_zero` turns that into vanishing oscillation. -/
theorem submultiplicative_implies_oscillation_zero
    (hsub : ∀ m n : ℕ, h (m + n) ≤ h m * h n) :
    growthRateLimSup - growthRateLimInf = 0 :=
  converges_iff_oscillation_zero.mp (submultiplicative_implies_convergence hsub)

/-- **Submultiplicativity ⟹ a single exponential base exists.**  The exponential-base form
of `submultiplicative_implies_oscillation_zero`: a submultiplicative covering number `h` has
a well-defined exponential base, so Erdős #117 OQ-01 is answered *yes* under this hypothesis.
Fekete convergence (`submultiplicative_implies_convergence`) transported through
`exponentialBaseExists_iff_converges`. -/
theorem submultiplicative_implies_exponentialBaseExists
    (hsub : ∀ m n : ℕ, h (m + n) ≤ h m * h n) :
    exponentialBaseExists :=
  exponentialBaseExists_iff_converges.mpr (submultiplicative_implies_convergence hsub)

/-- **A counterexample must break submultiplicativity.**  The contrapositive: if no single
exponential base exists (the growth rate genuinely oscillates), then `h` is *not*
submultiplicative — there exist `m, n` with `h(m+n) > h(m)·h(n)`.  A concrete necessary
condition on any counterexample to Erdős #117 OQ-01. -/
theorem not_exponentialBaseExists_implies_not_submultiplicative
    (hno : ¬ exponentialBaseExists) :
    ¬ (∀ m n : ℕ, h (m + n) ≤ h m * h n) :=
  fun hsub => hno (submultiplicative_implies_exponentialBaseExists hsub)

end Erdos117OQ01Incomplete01
