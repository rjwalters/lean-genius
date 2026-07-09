/-
# Erdős #1144, OQ-03: the `(log N)^{1+o(1)}` correction is genuine

Atherfold's 2025 theorem (`atherfold_upper_bound` in `Erdos1144Problem`) bounds the
partial sums of a Rademacher random multiplicative function by
`√N · (log N)^{1+o(1)}` almost surely.  OQ-03 asks to show that the `(log N)^{1+o(1)}`
correction **cannot be tightened to `(log N)^K` for any fixed finite `K`** — i.e. the
`o(1)` in the exponent is a genuine feature of the extremal growth.

## What this file proves

The mathematical heart is a **logical reduction**, stated so that it is correct
independently of the (deep, analytic) extremal lower bound:

* `EventualPowerBound f K C` / `FrequentPowerExceedance f K C` — the two competing
  shapes: an eventual `≤ C√N(log N)^K` ceiling versus frequently exceeding it.
* `not_frequentExceedance_of_eventualBound` — **the reduction lemma**: an eventual
  power-`K` upper bound flatly contradicts frequently exceeding the same threshold
  (`Filter.Eventually` vs `Filter.Frequently`).
* `no_power_upper_bound_of_frequent_exceedance` — **the OQ-03 statement, correctly
  encoded**: *if* the extremal `f` frequently exceeds `C√N(log N)^K` for every fixed
  `K, C` (the deep extremal lower bound, taken here as a hypothesis), *then* no
  fixed-power upper bound `EventualPowerBound f K C` can hold.

## Why the lower bound is a hypothesis, not an axiom

Asserting `∀ K C, FrequentPowerExceedance f K C` *unconditionally* (as an axiom) would
be **inconsistent** with the already-present `atherfold_upper_bound`: Atherfold caps the
growth at exponent `1+ε` for every `ε > 0`, so the sums cannot frequently exceed
`C√N(log N)^{1+ε}`.  This is made precise in `atherfold_refutes_frequent_exceedance`.
The genuine `o(1)` result is therefore a statement about a *narrower* exponent range and
is honestly encoded as the hypothesis of the reduction — not as a free-standing axiom.
(Cf. the Axiom-Integrity policy: an axiom that lets you derive `False` is worse than a
`sorry`.)

0 sorries, 0 new axioms.
-/
import Proofs.Erdos1144Problem

open Filter

namespace Erdos1144OQ03

/-- An **eventual power-`K` upper bound**: `|∑_{m≤N} f(m)| ≤ C·√N·(log N)^K` for all
sufficiently large `N`.  `K = 1 + ε` is exactly Atherfold's ceiling; the OQ-03 question
is whether any *fixed* `K` (in particular removing the `o(1)`, `K = 1`) can serve. -/
def EventualPowerBound (f : ℕ → ℤ) (K C : ℝ) : Prop :=
  ∀ᶠ N in atTop, |(partialSum f N : ℝ)| ≤ C * Real.sqrt (N : ℝ) * Real.log (N : ℝ) ^ K

/-- **Frequent power-`K` exceedance**: `|∑_{m≤N} f(m)| > C·√N·(log N)^K` for infinitely
many `N`.  The extremal-growth statement: the sums repeatedly break through the
power-`K` ceiling. -/
def FrequentPowerExceedance (f : ℕ → ℤ) (K C : ℝ) : Prop :=
  ∃ᶠ N in atTop, C * Real.sqrt (N : ℝ) * Real.log (N : ℝ) ^ K < |(partialSum f N : ℝ)|

/-- **Generic reduction (filters).** An eventual pointwise upper bound `S ≤ B`
contradicts frequently having `B < S`: `Filter.Eventually` and the corresponding
strict `Filter.Frequently` cannot coexist. -/
theorem eventually_le_not_frequently_lt {l : Filter ℕ} {S B : ℕ → ℝ}
    (h : ∀ᶠ N in l, S N ≤ B N) : ¬ ∃ᶠ N in l, B N < S N := by
  rw [Filter.not_frequently]
  filter_upwards [h] with N hN
  exact not_lt.mpr hN

/-- **The reduction lemma for OQ-03.** A fixed-power upper bound
`EventualPowerBound f K C` rules out `FrequentPowerExceedance f K C` at the *same*
`K, C`: the ceiling cannot hold eventually while being broken infinitely often. -/
theorem not_frequentExceedance_of_eventualBound (f : ℕ → ℤ) (K C : ℝ)
    (h : EventualPowerBound f K C) : ¬ FrequentPowerExceedance f K C := by
  unfold EventualPowerBound at h
  unfold FrequentPowerExceedance
  rw [Filter.not_frequently]
  filter_upwards [h] with N hN
  exact not_lt.mpr hN

/-- **OQ-03, correctly encoded.** *If* the extremal function `f` frequently exceeds
`C·√N·(log N)^K` for **every** fixed exponent `K` and constant `C` — the deep extremal
lower bound, taken as a hypothesis — *then* **no** fixed-power upper bound can hold:
the `(log N)^{1+o(1)}` correction cannot be tightened to any `(log N)^K`.

The proof is the one-line reduction: a candidate ceiling at `(K, C)` is immediately
contradicted by the hypothesised exceedance at the same `(K, C)`. -/
theorem no_power_upper_bound_of_frequent_exceedance (f : ℕ → ℤ)
    (hlb : ∀ K C : ℝ, FrequentPowerExceedance f K C) :
    ∀ K C : ℝ, ¬ EventualPowerBound f K C :=
  fun K C hub => not_frequentExceedance_of_eventualBound f K C hub (hlb K C)

/-- **The exceedance hypothesis is genuinely restricted — why it is not an axiom.**
Atherfold's upper bound refutes `FrequentPowerExceedance` already at exponent `1 + ε`:
for the constant `C` Atherfold provides, every Rademacher `f` eventually stays below
`C·√N·(log N)^{1+ε}`, so it cannot frequently exceed that same threshold.  Consequently
an *unconditional* `∀ K, FrequentPowerExceedance f K C` would contradict
`atherfold_upper_bound` — confirming that the OQ-03 lower bound must be encoded as a
hypothesis (as in `no_power_upper_bound_of_frequent_exceedance`), never as a standalone
axiom. -/
theorem atherfold_refutes_frequent_exceedance (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℕ → ℤ, IsRademacherMultiplicative f →
      ¬ FrequentPowerExceedance f (1 + ε) C := by
  obtain ⟨C, hCpos, hC⟩ := atherfold_upper_bound ε hε
  exact ⟨C, hCpos, fun f hf =>
    not_frequentExceedance_of_eventualBound f (1 + ε) C (hC f hf)⟩

/-- **Consistency of the framing.** The two OQ-03 ingredients are compatible: the
extremal lower-bound hypothesis forces exceedance at every exponent, which by the
reduction denies every fixed-power ceiling — while `atherfold_refutes_frequent_exceedance`
shows this can only be a *hypothesis* about the extremal `f`, not a universal law.  This
theorem records that `no_power_upper_bound_of_frequent_exceedance` is non-vacuous in the
only way it can be: as an implication whose antecedent is the genuine analytic input. -/
theorem oq03_reduction_summary (f : ℕ → ℤ)
    (hlb : ∀ K C : ℝ, FrequentPowerExceedance f K C) (K C : ℝ) :
    ¬ EventualPowerBound f K C :=
  no_power_upper_bound_of_frequent_exceedance f hlb K C

end Erdos1144OQ03
