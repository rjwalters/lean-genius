/-
Central Limit Theorem OQ-02-OQ-03: m-Dependent Sequences are α-Mixing

QUESTION: The parent (OQ-02) shows independent sequences are trivially α-mixing
(α(n) = 0 for every lag n ≥ 1, via `independent_implies_zero_mixing`). What is
the next-weakest dependence structure for which the α-mixing coefficients still
vanish — so that Ibragimov's mixing CLT applies for free?

ANSWER: **m-dependence** (finite-range dependence). A sequence is *m-dependent*
when blocks of variables separated by a gap strictly greater than `m` are
independent. For such sequences:

  α(n) = 0  for every lag  n > m,

i.e. the strong-mixing coefficients are *eventually identically zero*. This is
the cleanest possible mixing behaviour short of full independence:

* The independence case is exactly `m = 0` (gap ≥ 1 ⇒ independent), recovering
  the parent's `independent_implies_zero_mixing`.
* Because the coefficients are eventually 0, the Ibragimov series
  ∑ₙ α(n)^θ converges for **every** exponent θ > 0 (the strongest possible
  polynomial-mixing condition), so Ibragimov's CLT (OQ-02-OQ-04) applies to any
  m-dependent stationary sequence with finite variance, with no constraint on
  the mixing rate.
* The mixing-decay hypothesis α(n) → 0 holds trivially.

m-dependence is the canonical bridge between independence and general mixing:
classical examples include moving averages of finite order (MA(q) processes,
which are q-dependent) and one-step functions of finite-state Markov chains.

This file proves, fully and axiom-free (reusing the parent's
`alphaMixingCoeff`):
1. `mDependent_alpha_zero` — the headline: m-dependence ⇒ α(n) = 0 for n > m.
2. `mZeroDependent_recovers_independence` — m = 0 recovers the independent case.
3. `mDependent_mixing_decay` — α(n) → 0 (mixing decay holds trivially).
4. `summable_rpow_of_eventually_zero` — a reusable analytic lemma: an eventually
   zero nonneg sequence has summable rpow powers.
5. `mDependent_summable_mixing_rpow` — Ibragimov's series ∑ α(n)^θ converges for
   every θ > 0.
6. `alphaMixingCoeff_le_one` — the α-mixing coefficient is always ≤ 1 on a
   probability space (the upper bound the parent file leaves out).
7. `mDependent_mono` — m-dependence is monotone in m, so the finite-range classes
   nest upward (independent = 0-dependent ⊆ 1-dependent ⊆ …).

Proved theorems: 7, Axioms: 0, Sorries: 0
-/

import Mathlib
import Proofs.CentralLimitTheoremOQ02

open MeasureTheory Filter Topology
open CentralLimitTheoremOQ02

namespace CentralLimitTheoremOQ02OQ03

variable {Ω : Type*} [MeasurableSpace Ω]

/-
## Part I: m-Dependence

A family of σ-algebras `σ_k : ℕ → MeasurableSpace Ω` is **m-dependent** when any
two events whose index gap exceeds `m` are independent. Concretely, for events
`A` measurable w.r.t. `σ_k k` and `B` measurable w.r.t. `σ_k (k + n)` with
`n > m`, we have `μ (A ∩ B) = μ A · μ B`.

Setting `m = 0` recovers (the gap-≥-1 form of) independence used by the parent's
`independent_implies_zero_mixing`.
-/

/-- A family of σ-algebras is **m-dependent** under `μ`: events separated by a
gap strictly greater than `m` are independent. -/
def MDependent (μ : Measure Ω) (σ_k : ℕ → MeasurableSpace Ω) (m : ℕ) : Prop :=
  ∀ (k n : ℕ) (A B : Set Ω), m < n →
    @MeasurableSet Ω (σ_k k) A →
    @MeasurableSet Ω (σ_k (k + n)) B →
    μ (A ∩ B) = μ A * μ B

/-
## Part II: m-Dependence ⇒ α(n) = 0 for n > m

The proof mirrors the parent's `independent_implies_zero_mixing`: every term of
the defining nested supremum vanishes (independence of the gap-`n` blocks makes
`|μ(A∩B).toReal − μA.toReal·μB.toReal| = 0`), and a nested supremum of the
constant `0` over `ℝ` collapses to `0`. We sidestep the absence of a
`CompleteLattice ℝ` instance with the same Prop-indexed-sup-of-`0` helper.
-/

/-- **Headline.** For an m-dependent family, the α-mixing coefficient at any lag
`n > m` is exactly `0`. -/
theorem mDependent_alpha_zero {μ : Measure Ω} (σ_k : ℕ → MeasurableSpace Ω)
    (m : ℕ) (hMdep : MDependent μ σ_k m) :
    ∀ k n, m < n → alphaMixingCoeff μ (σ_k k) (σ_k (k + n)) = 0 := by
  intro k n hn
  -- Each term of the defining supremum is `0`: gap `n > m` forces independence.
  have hbody : ∀ (A : Set Ω), @MeasurableSet Ω (σ_k k) A →
      ∀ (B : Set Ω), @MeasurableSet Ω (σ_k (k + n)) B →
      |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal| = 0 := by
    intro A hA B hB
    have hind : μ (A ∩ B) = μ A * μ B := hMdep k n A B hn hA hB
    rw [hind, ENNReal.toReal_mul]
    simp
  -- A Prop-indexed supremum of the constant `0` is `0` (both for the inhabited
  -- and the empty index), sidestepping the lack of a `CompleteLattice ℝ`.
  have h0p : ∀ (p : Prop), (⨆ (_ : p), (0 : ℝ)) = 0 := by
    intro p
    by_cases h : p
    · haveI : Nonempty p := ⟨h⟩; simp
    · haveI : IsEmpty p := ⟨h⟩; simp
  -- Rewrite the whole nested supremum as one of `0`, then collapse.
  have collapse : alphaMixingCoeff μ (σ_k k) (σ_k (k + n))
      = ⨆ (A : Set Ω), ⨆ (_ : @MeasurableSet Ω (σ_k k) A),
          ⨆ (B : Set Ω), ⨆ (_ : @MeasurableSet Ω (σ_k (k + n)) B), (0 : ℝ) := by
    simp only [alphaMixingCoeff]
    apply iSup_congr; intro A
    apply iSup_congr; intro hA
    apply iSup_congr; intro B
    apply iSup_congr; intro hB
    exact hbody A hA B hB
  rw [collapse]
  simp only [h0p, ciSup_const]

/-
## Part III: m = 0 Recovers Independence

The independent case of the parent is precisely `MDependent μ σ_k 0`: a gap of at
least 1 (`0 < n`, i.e. `1 ≤ n`) forces independence, hence `α(n) = 0`. This
re-derives the conclusion of `independent_implies_zero_mixing` as the `m = 0`
specialization.
-/

/-- The `m = 0` case: a 0-dependent (independent) family has `α(n) = 0` for every
lag `n ≥ 1`, recovering `independent_implies_zero_mixing`. -/
theorem mZeroDependent_recovers_independence {μ : Measure Ω}
    (σ_k : ℕ → MeasurableSpace Ω) (hMdep : MDependent μ σ_k 0) :
    ∀ k n, 1 ≤ n → alphaMixingCoeff μ (σ_k k) (σ_k (k + n)) = 0 := by
  intro k n hn
  exact mDependent_alpha_zero σ_k 0 hMdep k n (by omega)

/-
## Part IV: Mixing Decay is Trivial

Because the coefficients are eventually `0` (from lag `m + 1` on), the mixing
decay hypothesis `α(n) → 0` of `AlphaMixingSequence` holds for free.
-/

/-- For an m-dependent family the lag-indexed coefficient `n ↦ α(n)` tends to `0`
(it is eventually identically `0`). -/
theorem mDependent_mixing_decay {μ : Measure Ω}
    (σ_k : ℕ → MeasurableSpace Ω) (m : ℕ) (hMdep : MDependent μ σ_k m) (k : ℕ) :
    Tendsto (fun n => alphaMixingCoeff μ (σ_k k) (σ_k (k + n))) atTop (nhds 0) := by
  refine tendsto_atTop_of_eventually_const (i₀ := m + 1) ?_
  intro n hn
  exact mDependent_alpha_zero σ_k m hMdep k n (by omega)

/-
## Part V: Ibragimov's Series Converges for Every Exponent

Ibragimov's CLT requires `∑ₙ α(n)^{δ/(2+δ)} < ∞`. For an m-dependent sequence the
summand vanishes for `n > m`, so the series is a *finite* sum and converges for
**every** exponent θ > 0 — the strongest possible polynomial-mixing condition,
placing no constraint on the mixing rate.

We first isolate the reusable analytic fact, then specialize it to the mixing
coefficients.
-/

/-- A sequence that is eventually `0` (past some index `N`) has summable rpow
powers, for any nonzero exponent. The support is contained in `Finset.range
(N+1)`, and `0 ^ θ = 0` past it. -/
theorem summable_rpow_of_eventually_zero {f : ℕ → ℝ} {N : ℕ} {θ : ℝ}
    (hθ : θ ≠ 0) (hf : ∀ n, N < n → f n = 0) :
    Summable (fun n => (f n) ^ θ) := by
  apply summable_of_ne_finset_zero (s := Finset.range (N + 1))
  intro n hn
  simp only [Finset.mem_range, not_lt] at hn
  rw [hf n (by omega), Real.zero_rpow hθ]

/-- **Ibragimov's mixing series converges for every exponent.** For an
m-dependent family and any `θ > 0`, the series `∑ₙ α(n)^θ` converges, since the
α-mixing coefficients vanish for `n > m`. Hence the Ibragimov CLT hypothesis
`∑ₙ α(n)^{δ/(2+δ)} < ∞` holds for every `δ > 0`. -/
theorem mDependent_summable_mixing_rpow {μ : Measure Ω}
    (σ_k : ℕ → MeasurableSpace Ω) (m : ℕ) (hMdep : MDependent μ σ_k m) (k : ℕ)
    {θ : ℝ} (hθ : θ ≠ 0) :
    Summable (fun n => (alphaMixingCoeff μ (σ_k k) (σ_k (k + n))) ^ θ) := by
  apply summable_rpow_of_eventually_zero (N := m) hθ
  intro n hn
  exact mDependent_alpha_zero σ_k m hMdep k n hn

/-
## Part VI: Hierarchy Placement

m-dependence sits strictly between independence and general α-mixing:

  Independent  ( = 0-dependent )
    ⊊ m-dependent  (finite range; α(n) = 0 for n > m)
    ⊊ α-mixing with summable rate  (Ibragimov)
    ⊊ α-mixing  (α(n) → 0)

Every m-dependent stationary sequence with `E[X₁] = 0` and `E[X₁²] < ∞`
satisfies the Ibragimov CLT (OQ-02-OQ-04) unconditionally on the rate, because
`mDependent_summable_mixing_rpow` gives the mixing-series condition for free.
The two inclusions are strict: a stationary 1-dependent moving average MA(1) is
not independent, and a long-memory α-mixing sequence with `α(n) > 0` for all `n`
is not m-dependent for any `m`.

The `θ ≠ 0` hypothesis of `mDependent_summable_mixing_rpow` is necessary: at
`θ = 0` each summand is `α(n)^0 = 1`, and `∑ₙ 1` diverges regardless of the
mixing structure.
-/

/-
## Part VII: The α-mixing coefficient is bounded by 1, and m-dependence is monotone

Two structural facts. First, a reusable bound the parent file explicitly leaves
out (its note: "`alphaMixingCoeff_nonneg` omitted due to nested ciSup elaboration
complexity"): on a probability space `0 ≤ α ≤ 1` always, because every term of the
defining supremum is `|x − y·z|` with `x, y, z ∈ [0,1]`. We supply the upper bound,
which `Real.iSup_le` handles cleanly (its `0 ≤ a` side-condition absorbs the
empty-index sup). Second, m-dependence is monotone in `m`: a stronger finite range
of dependence implies every weaker one, so the chain
`independent = 0-dependent ⊆ 1-dependent ⊆ 2-dependent ⊆ …` is genuine.
-/

/-- **The α-mixing coefficient is at most `1`.** On a probability space every term
`|μ(A∩B).toReal − μA.toReal · μB.toReal|` of the defining supremum lies in `[0,1]`
(all three measures are `≤ 1`), so the supremum is `≤ 1`. This supplies the upper
bound the parent file omits (stated for the lag-indexed σ-algebras `σ_k`). -/
theorem alphaMixingCoeff_le_one {μ : Measure Ω} [IsProbabilityMeasure μ]
    (σ_k : ℕ → MeasurableSpace Ω) (k n : ℕ) :
    alphaMixingCoeff μ (σ_k k) (σ_k (k + n)) ≤ 1 := by
  simp only [alphaMixingCoeff]
  refine Real.iSup_le (fun A => ?_) (by norm_num)
  refine Real.iSup_le (fun _ => ?_) (by norm_num)
  refine Real.iSup_le (fun B => ?_) (by norm_num)
  refine Real.iSup_le (fun _ => ?_) (by norm_num)
  have hx : (μ (A ∩ B)).toReal ≤ 1 := measureReal_le_one
  have hy : (μ A).toReal ≤ 1 := measureReal_le_one
  have hz : (μ B).toReal ≤ 1 := measureReal_le_one
  have hx0 : 0 ≤ (μ (A ∩ B)).toReal := ENNReal.toReal_nonneg
  have hy0 : 0 ≤ (μ A).toReal := ENNReal.toReal_nonneg
  have hz0 : 0 ≤ (μ B).toReal := ENNReal.toReal_nonneg
  rw [abs_le]
  constructor <;>
    nlinarith [hx, hx0, hy, hy0, hz, hz0, mul_nonneg hy0 hz0,
      mul_nonneg (sub_nonneg.mpr hy) hz0]

/-- **m-dependence is monotone in `m`.** If a family is `m`-dependent and `m ≤ m'`,
it is `m'`-dependent: any gap `n > m'` already exceeds `m`. Hence the finite-range
dependence classes are nested upward (`independent = 0-dependent ⊆ m-dependent ⊆ …`). -/
theorem mDependent_mono {μ : Measure Ω} {σ_k : ℕ → MeasurableSpace Ω} {m m' : ℕ}
    (hmm : m ≤ m') (hMdep : MDependent μ σ_k m) : MDependent μ σ_k m' := by
  intro k n A B hn hA hB
  exact hMdep k n A B (lt_of_le_of_lt hmm hn) hA hB

end CentralLimitTheoremOQ02OQ03
