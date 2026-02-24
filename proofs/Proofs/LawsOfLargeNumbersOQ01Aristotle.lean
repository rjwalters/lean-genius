/-
  Aristotle targets for Laws of Large Numbers OQ-01
  Supporting lemmas for the slln_necessity proof (Borel-Cantelli approach).
  See LawsOfLargeNumbersOQ01.lean for the main formalization.

  The Missing Piece: slln_necessity

  LawsOfLargeNumbersOQ01.lean has `slln_necessity` as an axiom:
    If SLLN holds (sample mean → c a.s.), then E[|X₀|] < ∞.

  Proof Blueprint (for future formalization)

  By contradiction: assume SLLN holds but E[|X₀|] = ∞. Then:
  1. Xₙ/n → 0 a.s. (from SLLN, by Cesàro)
  2. Σ P(‖X₀‖ > n) = ∞ (layer cake: E[‖X‖] = ∞ ↔ Σ P(‖X‖ > n) = ∞)
  3. Σ P(‖Xₙ‖ > n) = ∞ (from 2, by identical distribution)
  4. P(‖Xₙ‖ > n i.o.) = 1 (BC2: ProbabilityTheory.measure_limsup_eq_one)
  5. But from (1): P(‖Xₙ‖ > n i.o.) = 0 — contradiction!

  Key Mathlib tools available:
  - ProbabilityTheory.measure_limsup_eq_one (BC2, from Mathlib.Probability.BorelCantelli)
  - ProbabilityTheory.tsum_prob_mem_Ioi_lt_top (L¹ → Σ P(X > n) < ∞)

  Criteria for inclusion:
  - NOT the main open conjecture
  - No axioms (use theorem ... := by sorry instead)
  - No definition sorries
-/
import Mathlib

open MeasureTheory ProbabilityTheory Filter ENNReal

namespace LawsOfLargeNumbersOQ01

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/- Routine Lemma 1: Measurability of tail events.
   The events {ω | n < ‖Xₙ(ω)‖} are measurable (needed for applying BC2). -/

/-- The tail event {ω | n < ‖X n ω‖} is measurable for each n. -/
theorem measurableSet_tail_event
    (X : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i))
    (n : ℕ) :
    MeasurableSet {ω : Ω | (↑n : ℝ) < ‖X n ω‖} :=
  measurableSet_lt measurable_const (hmeas n).norm

/- Routine Lemma 2: IdentDistrib preserves tail probabilities.
   If X₀ and Xₙ have identical distributions, then P(‖Xₙ‖ > t) = P(‖X₀‖ > t). -/

omit [IsProbabilityMeasure μ] in
/-- Identical distributions preserve tail probabilities. -/
theorem identDistrib_meas_norm_gt
    (X Y : Ω → ℝ)
    (hXY : ProbabilityTheory.IdentDistrib X Y μ μ)
    (t : ℝ) :
    μ {ω : Ω | t < ‖X ω‖} = μ {ω : Ω | t < ‖Y ω‖} :=
  hXY.measure_mem_eq (measurableSet_lt measurable_const measurable_norm)

/- Routine Lemma 3: i.i.d. tail sum equals X₀ tail sum.
   Σₙ P(‖Xₙ‖ > n) = Σₙ P(‖X₀‖ > n) when X₀, X₁, ... are identically distributed. -/

omit [IsProbabilityMeasure μ] in
/-- For an i.i.d. sequence, the tail sum Σ P(‖Xₙ‖ > n) equals Σ P(‖X₀‖ > n). -/
theorem tsum_prob_norm_gt_iid_eq
    (X : ℕ → Ω → ℝ)
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ) :
    (∑' n : ℕ, μ {ω : Ω | (↑n : ℝ) < ‖X n ω‖}) =
    (∑' n : ℕ, μ {ω : Ω | (↑n : ℝ) < ‖X 0 ω‖}) := by
  congr 1
  ext n
  exact identDistrib_meas_norm_gt (X n) (X 0) (hident n) n

/- Routine Lemma 4: Integrability implies finite tail sum.
   If E[‖X‖] < ∞, then Σₙ P(‖X‖ > n) < ∞.
   Uses ProbabilityTheory.tsum_prob_mem_Ioi_lt_top (requires MeasureSpace). -/

/-- Integrability implies finite tail sum: E[‖X‖] < ∞ → Σ P(‖X‖ > n) < ∞. -/
theorem tsum_prob_norm_gt_lt_top_of_integrable
    (X : Ω → ℝ)
    (hmeas : Measurable X)
    (hint : Integrable X μ) :
    (∑' n : ℕ, μ {ω : Ω | ‖X ω‖ ∈ Set.Ioi (↑n : ℝ)}) < ⊤ := by
  sorry

/- Routine Lemma 5: Layer cake converse.
   If Σ P(‖X‖ > n) < ∞, then X is integrable.
   This follows from E[‖X‖] ≤ 1 + Σ P(‖X‖ > n). -/

/-- If the tail sum Σ P(‖X‖ > n) is finite, then X is integrable.

    Proof sketch: E[‖X‖] ≤ 1 + Σ P(‖X‖ > n) by layer cake formula. -/
theorem integrable_of_tsum_prob_norm_gt_lt_top
    (X : Ω → ℝ)
    (hmeas : Measurable X)
    (htsum : (∑' n : ℕ, μ {ω : Ω | ‖X ω‖ ∈ Set.Ioi (↑n : ℝ)}) < ∞) :
    Integrable X μ := by
  sorry

/- Routine Lemma 6: Non-integrable → tail sum is infinite.
   Contrapositive of Lemma 5. -/

/-- If X is not integrable, then the tail sum Σ P(‖X‖ > n) = ∞. -/
theorem tsum_prob_norm_gt_eq_top_of_not_integrable
    (X : Ω → ℝ)
    (hmeas : Measurable X)
    (hint : ¬ Integrable X μ) :
    (∑' n : ℕ, μ {ω : Ω | ‖X ω‖ ∈ Set.Ioi (↑n : ℝ)}) = ⊤ := by
  sorry

/- Main Target: slln_necessity (the key open gap).
   Converts the axiom to a sorry theorem for potential future proof. -/

/-- slln_necessity — converse of Kolmogorov's SLLN.

    If the sample mean of i.i.d. random variables converges a.s. to some limit,
    then the random variables must have finite first moment.

    Status: Completes Kolmogorov's characterization: SLLN ⟺ E[‖X₀‖] < ∞

    Proof gaps:
    1. Cesàro argument: SLLN → Xₙ/n → 0 a.s.
    2. Layer cake converse: ¬ Integrable → Σ P(‖X‖ > n) = ∞
    3. Full mutual independence of {‖Xₙ‖ > n} for BC2 -/
theorem slln_necessity_statement
    (X : ℕ → Ω → ℝ)
    (hmeas : ∀ i, Measurable (X i))
    (hindep : Pairwise fun i j => ProbabilityTheory.IndepFun (X i) (X j) μ)
    (hident : ∀ i, ProbabilityTheory.IdentDistrib (X i) (X 0) μ μ)
    (hslln : ∃ (c : ℝ), ∀ᵐ ω ∂μ,
      Filter.Tendsto (fun n : ℕ => (↑n : ℝ)⁻¹ • ∑ i ∈ Finset.range n, X i ω)
      Filter.atTop (nhds c)) :
    MeasureTheory.Integrable (X 0) μ := by
  sorry

end LawsOfLargeNumbersOQ01
