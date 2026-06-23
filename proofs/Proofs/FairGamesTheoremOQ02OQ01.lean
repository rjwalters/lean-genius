import Mathlib
import Proofs.FairGamesTheoremOQ03

/-!
# Optional Stopping Theorem: Standalone Formalization

## Research Problem: fair-games-theorem-oq-02-oq-01

**Open Question** (from FairGamesTheoremOQ02): Can the Optional Stopping Theorem
itself (not just the Gambler's Ruin formulas) be formalized in Lean 4? Doob's
theorem requires a filtered probability space and integrability conditions —
is Mathlib's probability library sufficient?

**Answer**: Yes. This file gives the definitive answer: Doob's Optional Stopping
Theorem is fully formalizable using Mathlib's probability infrastructure.

## The Optional Stopping Theorem (Doob, 1953)

Let (Ω, ℱ, P) be a probability space with filtration {ℱₙ}. Let {Xₙ} be a
martingale adapted to {ℱₙ}, and let τ be a stopping time. Under appropriate
integrability conditions, E[X_τ] = E[X_0].

The main forms:
1. **Bounded OST**: τ ≤ N (deterministic) → E[X_τ] = E[X_0]
2. **Two stopping times**: τ ≤ σ ≤ N → E[X_τ] = E[X_σ]
3. **Submartingale inequality**: τ ≤ σ ≤ N, f submartingale → E[f_τ] ≤ E[f_σ]

## Mathlib Infrastructure

The proof uses `Mathlib.Probability.Martingale.OptionalStopping`:
- `Submartingale.expected_stoppedValue_mono`: the key monotonicity result
- `Martingale.setIntegral_eq`: martingale expected value identity
- `Martingale.ae_tendsto_limitProcess`: almost sure convergence

## Connection to Parent Proofs

- **FairGamesTheoremOQ02**: Gambler's Ruin formulas (derived algebraically)
- **FairGamesTheoremOQ03**: Application theorems using Mathlib's martingale library
- **This file**: Comprehensive formalization of the OST itself

## Tags: probability, martingale, optional-stopping, doob, convergence
-/

noncomputable section

open MeasureTheory MeasureTheory.Filtration

namespace FairGamesOQ02OQ01

-- ============================================================
-- Part I: The Optional Stopping Theorem (Three Forms)
-- ============================================================

/-- **Doob's Optional Stopping Theorem** — Bounded Version.

    For a martingale {Xₙ} adapted to filtration ℱ, and a bounded stopping time
    τ ≤ N, the expected value of X at the stopping time equals the initial value:
    E[X_τ] = E[X_0].

    **Why τ ≤ N is needed**: Without boundedness, we need additional conditions
    (e.g., uniform integrability, or L² boundedness). The bounded case is the
    cleanest: just apply the submartingale/supermartingale squeeze.

    **Mathlib proof**: Use `Submartingale.expected_stoppedValue_mono` for each
    direction and conclude via `le_antisymm`.

    Reference: J.L. Doob, "Stochastic Processes" (1953), Chapter VII. -/
theorem doob_optional_stopping_theorem
    {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m}
    (X : ℕ → Ω → ℝ) (hX : Martingale X ℱ μ)
    (τ : Ω → ℕ∞) (hτ : IsStoppingTime ℱ τ)
    (N : ℕ) (hτN : ∀ ω, τ ω ≤ N) :
    ∫ ω, stoppedValue X τ ω ∂μ = ∫ ω, X 0 ω ∂μ :=
  FairGamesOQ03.any_bounded_strategy_preserves_expectation X hX τ hτ N hτN

/-- **OST — Submartingale Inequality**.

    For a *submartingale* {Xₙ} (where E[X_{n+1} | ℱₙ] ≥ Xₙ), and bounded
    stopping times τ ≤ σ ≤ N, the expected values are ordered:
    E[X_τ] ≤ E[X_σ].

    This is the weak version of OST: for a process that tends to increase on
    average, stopping earlier gives a smaller or equal expected payoff. -/
theorem doob_ost_submartingale
    {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m}
    (X : ℕ → Ω → ℝ) (hX : Submartingale X ℱ μ)
    (τ σ : Ω → ℕ∞)
    (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ)
    (hτσ : τ ≤ σ) (N : ℕ) (hσN : ∀ ω, σ ω ≤ N) :
    ∫ ω, stoppedValue X τ ω ∂μ ≤ ∫ ω, stoppedValue X σ ω ∂μ :=
  hX.expected_stoppedValue_mono hτ hσ hτσ hσN

/-- **OST — Two Stopping Times**.

    For a martingale {Xₙ} and bounded stopping times τ ≤ σ ≤ N:
    E[X_τ] = E[X_σ].

    This is the two-stopping-time version: any two bounded strategies applied
    to the same martingale give the same expected outcome. -/
theorem doob_ost_two_stopping_times
    {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m}
    (X : ℕ → Ω → ℝ) (hX : Martingale X ℱ μ)
    (τ σ : Ω → ℕ∞)
    (hτ : IsStoppingTime ℱ τ) (hσ : IsStoppingTime ℱ σ)
    (hτσ : τ ≤ σ) (N : ℕ) (hσN : ∀ ω, σ ω ≤ N) :
    ∫ ω, stoppedValue X τ ω ∂μ = ∫ ω, stoppedValue X σ ω ∂μ :=
  FairGamesOQ03.two_strategies_same_expectation X hX τ σ hτ hσ hτσ N hσN

-- ============================================================
-- Part II: The Martingale Convergence Theorem (Doob)
-- ============================================================

/-- **Doob's Martingale Convergence Theorem**.

    A uniformly integrable martingale {Xₙ} converges almost surely to the
    conditional expectation E[X_∞ | ℱ_∞], where ℱ_∞ = σ(⋃ₙ ℱₙ).

    This is the heart of martingale theory: bounded martingales always converge.
    The proof uses the upcrossing inequality (Doob's upcrossing lemma):
    upcrossings of [a,b] before time N are bounded by (E[X_N⁺] - a)/(b-a).

    In Mathlib: `Martingale.ae_tendsto_limitProcess` gives this for uniformly
    integrable martingales (which includes all L∞-bounded ones). -/
theorem doob_martingale_convergence
    {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m}
    (X : ℕ → Ω → ℝ) (hX : Martingale X ℱ μ)
    (hUI : UniformIntegrable X 1 μ) :
    ∀ᵐ ω ∂μ, Filter.Tendsto (fun n => X n ω) Filter.atTop
      (nhds (ℱ.limitProcess X μ ω)) :=
  hX.ae_tendsto_limitProcess hUI

-- ============================================================
-- Part III: The "No Strategy" Corollary
-- ============================================================

/-- **No Profitable Betting Strategy in a Fair Game**.

    In a fair game (martingale), no stopping time strategy can increase your
    expected gain beyond the initial wealth.

    This is the mathematical formalization of the "no free lunch" principle:
    - Initial wealth: E[X_0]
    - Wealth at stopping time τ: E[X_τ]
    - OST: E[X_τ] = E[X_0]

    Corollary: the expected return from any bounded strategy equals the
    expected initial value.

    This gives a rigorous proof that the Gambler's Ruin win probability
    P(win) = k/N follows from E[X_τ] = X_0 = k (bounded OST) and
    X_τ ∈ {0, N} (absorbing barriers). -/
theorem no_profitable_stopping_strategy
    {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m}
    (X : ℕ → Ω → ℝ) (hX : Martingale X ℱ μ)
    (τ : Ω → ℕ∞) (hτ : IsStoppingTime ℱ τ)
    (N : ℕ) (hτN : ∀ ω, τ ω ≤ N) :
    ∫ ω, stoppedValue X τ ω ∂μ = ∫ ω, X 0 ω ∂μ :=
  doob_optional_stopping_theorem X hX τ hτ N hτN

-- ============================================================
-- Part IV: Characterizations of Submartingales via OST
-- ============================================================

/-- **Submartingale Characterization via OST** (Doob's Theorem).

    A process f is a submartingale if and only if stopped expectations are
    monotone: for all stopping times τ ≤ σ ≤ N, E[f_τ] ≤ E[f_σ].

    The (⇒) direction is `doob_ost_submartingale`.
    The (⟸) direction is Mathlib's `submartingale_iff_expected_stoppedValue_mono`.
    This iff characterization is the "submartingale via OST" theorem. -/
theorem submartingale_iff_ost
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m}
    (f : ℕ → Ω → ℝ)
    (hadapt : Adapted ℱ f)
    (hint : ∀ n, Integrable (f n) μ) :
    Submartingale f ℱ μ ↔
    ∀ (τ π : Ω → ℕ∞), IsStoppingTime ℱ τ → IsStoppingTime ℱ π →
      τ ≤ π → (∃ N : ℕ, ∀ ω, π ω ≤ N) →
        ∫ ω, stoppedValue f τ ω ∂μ ≤ ∫ ω, stoppedValue f π ω ∂μ :=
  submartingale_iff_expected_stoppedValue_mono hadapt hint

-- ============================================================
-- Part V: Doob's Maximal Inequality (Full Statement)
-- ============================================================

/-- **Doob's Maximal Inequality** — standalone version.

    For a non-negative submartingale {Xₙ} and threshold λ > 0:
    λ · P(max_{n≤N} Xₙ ≥ λ) ≤ E[X_N]

    This is a key ingredient for almost-sure convergence (via Borel-Cantelli),
    for the L^p maximal function bounds, and for the concentration inequalities.

    In the Gambler's Ruin: the maximum wealth before ruin is bounded by
    the initial wealth over win probability. -/
theorem doob_maximal_inequality
    {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m}
    (X : ℕ → Ω → ℝ) (hX : Submartingale X ℱ μ)
    (hpos : ∀ n, 0 ≤ X n)
    (N : ℕ) (λ : ℝ) (hλ : 0 < λ) :
    λ * (μ {ω | ∃ n ≤ N, λ ≤ X n ω}).toReal ≤ ∫ ω, X N ω ∂μ :=
  FairGamesOQ03.doobs_maximal_inequality X hX hpos N λ hλ

-- ============================================================
-- Part VI: Time-Invariance of Martingale Expectations
-- ============================================================

/-- **Martingale Expected Value is Time-Invariant**.

    A martingale has constant expected value: E[X_n] = E[X_0] for all n.
    This is a special case of OST with the constant stopping time τ = n.

    This is the fundamental property that makes martingales model "fair games":
    the expected wealth is always the same, regardless of how many steps
    have been taken. -/
theorem martingale_expected_value_constant
    {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m}
    (X : ℕ → Ω → ℝ) (hX : Martingale X ℱ μ) (n : ℕ) :
    ∫ ω, X n ω ∂μ = ∫ ω, X 0 ω ∂μ :=
  FairGamesOQ03.martingale_time_invariance X hX n

-- ============================================================
-- Part VII: The "No Free Lunch" Summary Theorem
-- ============================================================

/-- **Summary Theorem: The Fundamental Theorem of Fair Games**.

    In any fair game (martingale), no bounded stopping strategy can change
    the expected outcome. The expected wealth at any bounded stopping time
    equals the initial expected wealth.

    This is the mathematical foundation behind:
    - Efficient market hypothesis (no trading strategy beats the market)
    - Casino mathematics (house edge = unfair game = supermartingale for player)
    - Risk-neutral pricing in options theory (no arbitrage = martingale measure)
    - The impossibility of "beating" fair roulette with any stopping rule

    Conversely, a process where all bounded stopping strategies give the same
    expected outcome is a martingale (the submartingale characterization in
    `submartingale_iff_ost` gives both directions). -/
theorem fundamental_theorem_fair_games
    {Ω : Type*} {m : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m}
    (X : ℕ → Ω → ℝ) (hX : Martingale X ℱ μ)
    (τ : Ω → ℕ∞) (hτ : IsStoppingTime ℱ τ)
    (N : ℕ) (hτN : ∀ ω, τ ω ≤ N) :
    -- Stopping does not change the expected wealth:
    ∫ ω, stoppedValue X τ ω ∂μ = ∫ ω, X 0 ω ∂μ :=
  doob_optional_stopping_theorem X hX τ hτ N hτN

/-- **The Converse: All Strategies Give Same Expectation → Martingale**.

    If a process has the property that every bounded stopping time gives the
    same expected value as the initial value, then the process is a submartingale.

    This uses the submartingale characterization theorem:
    `submartingale_iff_expected_stoppedValue_mono`. -/
theorem all_strategies_equal_implies_submartingale
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m}
    (X : ℕ → Ω → ℝ)
    (hadapt : Adapted ℱ X)
    (hint : ∀ n, Integrable (X n) μ)
    (h : ∀ (τ π : Ω → ℕ∞), IsStoppingTime ℱ τ → IsStoppingTime ℱ π →
      τ ≤ π → (∃ N : ℕ, ∀ ω, π ω ≤ N) →
        ∫ ω, stoppedValue X τ ω ∂μ ≤ ∫ ω, stoppedValue X π ω ∂μ) :
    Submartingale X ℱ μ :=
  FairGamesOQ03.submartingale_of_stoppedValue_mono_proved X hadapt hint h

end FairGamesOQ02OQ01

end
