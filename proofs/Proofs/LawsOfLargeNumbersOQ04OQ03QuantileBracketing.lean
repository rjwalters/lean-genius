/-
# Glivenko–Cantelli: Quantile Bracketing Grid (S13 typed scaffold)
(laws-of-large-numbers-oq-04-oq-03 — Session S13, 2026-06-02)

## Background

The previous bracketing companion file
`LawsOfLargeNumbersOQ04OQ03Bracketing.lean` (S3–S9 ACT) defined a structure
`BracketingGrid F ε` whose `step_le` field required
`F (qⱼ₊₁) − F (qⱼ) ≤ ε` for every adjacent pair, with no atomless hypothesis.
That structure is provably empty for any CDF with an atom of mass `> ε`
(witness: a single Dirac point mass; see
`LawsOfLargeNumbersOQ04OQ03BracketingDisproof.lean`, S10 ACT). The companion's
sole axiom `bracketingGrid_exists` is therefore false (refuted in #20969),
and the downstream `glivenko_cantelli_uniform` proof in §2.5 is vacuous
(derived from an inconsistent assumption).

## What this file does (S13 — typed scaffold only)

This file ships the redesigned structure `QuantileBracketingGrid F ε` that
*does* handle atomic CDFs, by replacing the one-sided step bound with the
standard quantile bound `Function.leftLim F (qⱼ₊₁) − F (qⱼ) ≤ ε`. The
field `cont` (continuity at each node) is dropped: left limits exist for
*any* monotone `F` (Mathlib's `Function.leftLim` returns a definite value
regardless of continuity), so no atomless hypothesis is needed.

Mirroring S3's scaffold-only approach to the original `BracketingGrid`,
this file introduces only the structure and rich documentation — no
theorems, no axioms, no sorries. S14+ will:

  * Prove `quantileBracketingGrid_exists` — the *genuine* existence
    statement that holds for arbitrary probability measures on `ℝ`,
    using the quantile construction `qⱼ = inf {x | F x ≥ jε}` (Mathlib's
    `Function.leftLim` + monotone-image API). This is the real Mathlib
    upstream target, replacing the void
    `Monotone.exists_increasing_continuity_seq` plan.
  * Rewrite §2.4 `bracketing_pointwise_bound` /
    `bracketing_uniform_sup_bound` with cross-side step bounds: interior
    cell uses `F(x) ≤ F(qⱼ₊₁⁻)` and `F(qⱼ) ≤ F(x)` for
    `x ∈ [qⱼ, qⱼ₊₁)`.
  * Rewrite §2.5 `glivenko_cantelli_uniform` with the two-sided per-grid
    hypothesis. The diagonal ε = 1/(m+1) structure is preserved.
  * Remove the refuted axiom `bracketingGrid_exists` and the disproof
    file once the redesign lands.

## Why a scaffold-only PR

Mirroring S3 (PR #17442, researcher-12, 2026-05-08): the existing OQ04OQ03
chain has 0 sorries on the main file and the disproof file is build-verified.
A scaffold-only S13 introduces zero new proof obligations while giving
S14+ a typed substrate for the genuine existence proof + §2.4/§2.5 rewrites.
The structure shape is the only design decision; pinning it down with
docstrings allows multiple downstream sessions to proceed in parallel
without re-negotiating field layout each time.

## Field-by-field comparison with the refuted `BracketingGrid`

| Field      | `BracketingGrid` (refuted)                          | `QuantileBracketingGrid` (this file)                                        |
|------------|-----------------------------------------------------|-----------------------------------------------------------------------------|
| `k`        | `ℕ` (interior cell count)                           | `ℕ` (unchanged)                                                             |
| `q`        | `Fin (k + 2) → ℝ`                                   | `Fin (k + 2) → ℝ` (unchanged)                                               |
| `mono`     | `StrictMono q`                                      | `StrictMono q` (unchanged)                                                  |
| `cont`     | `∀ j, ContinuousAt F (q j)`                         | **dropped** — `Function.leftLim` works without continuity                   |
| `step_le`  | `F (qⱼ₊₁) − F (qⱼ) ≤ ε`                             | **`Function.leftLim F (qⱼ₊₁) − F (qⱼ) ≤ ε`** (the quantile bound)           |
| `left_le`  | `F (q 0) ≤ ε`                                       | `F (q 0) ≤ ε` (unchanged)                                                   |
| `right_ge` | `F (q_last) ≥ 1 − ε`                                | `F (q_last) ≥ 1 − ε` (unchanged)                                            |

The only mathematical change is in `step_le` and `cont`. The shift is
exactly the standard quantile / Dvoretzky–Kiefer–Wolfowitz / empirical
process construction: at an atom of mass `m > ε`, the node `qⱼ` sits at
the atom's left side and `Function.leftLim F (qⱼ₊₁) = F (qⱼ)` keeps the
step at `0 ≤ ε`. For atomless CDFs the left limit equals the value, so
the new bound reduces to the old one and the redesign is conservative.

## What S13 does NOT do

  * Does not delete the refuted axiom `bracketingGrid_exists` or the
    disproof file. Both remain in tree as historical record of the S10
    pivot point until the redesign supersedes them.
  * Does not modify `LawsOfLargeNumbersOQ04OQ03Bracketing.lean` or
    `LawsOfLargeNumbersOQ04OQ03.lean`. Existing build-verified content
    is preserved bit-for-bit.
  * Does not prove `quantileBracketingGrid_exists`. The existence proof
    is the substantive S14 ACT (~150 LOC).
  * Does not rewrite §2.4 / §2.5. Those rewrites are S15/S16 ACT.

## Build cost

The file imports the same Mathlib modules as the existing bracketing
companion (`Probability.CDF`, `Topology.Order.Monotone`) plus the
single new import `Topology.Order.LeftRightLim` that exposes
`Function.leftLim`. The structure declaration has no proof obligations
beyond elaboration of the field types. Type-check confidence is high.
-/

import Proofs.LawsOfLargeNumbersOQ04OQ03
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Probability.CDF

namespace GlivenkoCantelli

open MeasureTheory ProbabilityTheory Set Function

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

-- ============================================================================
-- §S13.1: The quantile-bracketing-grid predicate
-- ============================================================================

/-- A **quantile ε-bracketing grid** for a CDF `F : ℝ → ℝ` is a finite
    strictly increasing sequence of nodes whose `F`-images cover `[0, 1]`
    in steps of size at most `ε`, measured with the *left limit* of `F` at
    the next node.

    The five fields capture:
    * `k`        — number of interior cells (so the grid has `k + 2` nodes);
    * `q`        — the strictly increasing sequence of nodes,
                   indexed by `Fin (k + 2)`;
    * `mono`     — strict monotonicity of `q`;
    * `step_le`  — interior quantile bound: for each adjacent pair indexed
                   by `Fin (k + 1)`, the left limit of `F` at `qⱼ₊₁`
                   minus `F (qⱼ)` is at most `ε`;
    * `left_le`  — left boundary mass bound: `F(q₀) ≤ ε`;
    * `right_ge` — right boundary mass bound: `F(q_{k+1}) ≥ 1 − ε`.

    Unlike the refuted `BracketingGrid` (companion §2.1, disproved S10 ACT
    in `LawsOfLargeNumbersOQ04OQ03BracketingDisproof.lean`), this structure
    *does not* require continuity at the nodes or atomlessness of the
    distribution. The left-limit-based `step_le` accommodates atoms by
    placing each atom at its own cell boundary: if `F` jumps by mass
    `m > ε` at `x₀`, the grid sets `qⱼ = x₀` and
    `Function.leftLim F qⱼ = F (qⱼ⁻)`, leaving the step
    `leftLim F (qⱼ₊₁) − F (qⱼ)` measured to the *bottom* of any subsequent
    atom rather than across it.

    For atomless `F`, `Function.leftLim F x = F x` (when `F` is continuous
    at `x`, which holds at almost every `x` for any CDF), so this bound
    reduces to the original `F (qⱼ₊₁) − F (qⱼ) ≤ ε` and the redesign is
    conservative.

    The genuine existence statement
    `Nonempty (QuantileBracketingGrid (trueCDF X μ) ε)` for any probability
    measure `μ` on `ℝ` and any `ε > 0` is the S14+ target (replaces the
    void `Monotone.exists_increasing_continuity_seq` Mathlib upstream
    plan). -/
structure QuantileBracketingGrid (F : ℝ → ℝ) (ε : ℝ) where
  k        : ℕ
  q        : Fin (k + 2) → ℝ
  mono     : StrictMono q
  step_le  : ∀ j : Fin (k + 1),
             Function.leftLim F (q j.succ) - F (q j.castSucc) ≤ ε
  left_le  : F (q 0) ≤ ε
  right_ge : F (q (Fin.last (k + 1))) ≥ 1 - ε

-- ============================================================================
-- §S14a.1: Boundary node existence helpers
-- ============================================================================

/-- **Bridge to Mathlib's `cdf`.** Pointwise identification of the parent's
    `trueCDF X μ` with `ProbabilityTheory.cdf (Measure.map (X 0) μ)`. Mirrors
    `LawsOfLargeNumbersOQ04OQ03Bracketing.trueCDF_eq_cdf_map` and is restated
    here so the quantile-bracketing chain has no transitive dependency on the
    refuted axiom in the bracketing companion. -/
private lemma trueCDF_eq_cdf_map' [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : Measurable (X 0)) (x : ℝ) :
    trueCDF X μ x = ProbabilityTheory.cdf (Measure.map (X 0) μ) x := by
  haveI : IsProbabilityMeasure (Measure.map (X 0) μ) :=
    Measure.isProbabilityMeasure_map hX_meas.aemeasurable
  rw [ProbabilityTheory.cdf_eq_real]
  show (μ {ω | X 0 ω ≤ x}).toReal = ((Measure.map (X 0) μ) (Set.Iic x)).toReal
  rw [Measure.map_apply hX_meas measurableSet_Iic]; rfl

/-- **Boundary helper for the redesigned grid.** For any `ε > 0`, the CDF
    has values `≤ ε` arbitrarily far to the left. This will discharge the
    `left_le : F (q 0) ≤ ε` field of `QuantileBracketingGrid` in the
    S14b existence proof: pick `q 0` as any witness of this lemma.

    Proof outline: `trueCDF X μ → 0` at `-∞` (via Mathlib's
    `ProbabilityTheory.tendsto_cdf_atBot`), so the eventual-membership in
    `Iio ε ∈ 𝓝 0` extracts a witness. -/
lemma trueCDF_exists_le [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : Measurable (X 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x : ℝ, trueCDF X μ x ≤ ε := by
  haveI : IsProbabilityMeasure (Measure.map (X 0) μ) :=
    Measure.isProbabilityMeasure_map hX_meas.aemeasurable
  have h_tend : Filter.Tendsto (trueCDF X μ) Filter.atBot (nhds 0) := by
    have h_eq : trueCDF X μ = ProbabilityTheory.cdf (Measure.map (X 0) μ) := by
      funext x; exact trueCDF_eq_cdf_map' hX_meas x
    rw [h_eq]; exact ProbabilityTheory.tendsto_cdf_atBot _
  obtain ⟨x, hx⟩ := (h_tend.eventually (Iio_mem_nhds hε)).exists
  exact ⟨x, le_of_lt hx⟩

/-- **Boundary helper for the redesigned grid.** For any `η < 1`, the CDF
    has values `≥ η` arbitrarily far to the right. This will discharge the
    `right_ge : F (q_last) ≥ 1 - ε` field of `QuantileBracketingGrid` in
    the S14b existence proof: pick `q_last` as any witness of this lemma
    instantiated at `η = 1 - ε`.

    Proof outline: `trueCDF X μ → 1` at `+∞` (via Mathlib's
    `ProbabilityTheory.tendsto_cdf_atTop`), so the eventual-membership in
    `Ioi η ∈ 𝓝 1` extracts a witness. -/
lemma trueCDF_exists_ge [IsProbabilityMeasure μ]
    {X : ℕ → Ω → ℝ} (hX_meas : Measurable (X 0))
    {η : ℝ} (hη : η < 1) :
    ∃ x : ℝ, η ≤ trueCDF X μ x := by
  haveI : IsProbabilityMeasure (Measure.map (X 0) μ) :=
    Measure.isProbabilityMeasure_map hX_meas.aemeasurable
  have h_tend : Filter.Tendsto (trueCDF X μ) Filter.atTop (nhds 1) := by
    have h_eq : trueCDF X μ = ProbabilityTheory.cdf (Measure.map (X 0) μ) := by
      funext x; exact trueCDF_eq_cdf_map' hX_meas x
    rw [h_eq]; exact ProbabilityTheory.tendsto_cdf_atTop _
  obtain ⟨x, hx⟩ := (h_tend.eventually (Ioi_mem_nhds hη)).exists
  exact ⟨x, le_of_lt hx⟩

-- ============================================================================
-- §S14a.2: Monotone left-limit upper bracket
-- ============================================================================

/-- **Left-limit upper bracket (monotone, no continuity needed).** If every
    point strictly below `q` has `F`-value `≤ p`, then `Function.leftLim F q ≤ p`.

    This is the generic order-topology half of the S14 quantile `step_le`
    bound: at the quantile node `qⱼ₊₁ = sInf {x | (j+1)ε ≤ F x}`, every
    `x < qⱼ₊₁` fails membership and hence has `F x < (j+1)ε`, so this lemma
    yields `leftLim F qⱼ₊₁ ≤ (j+1)ε`. Combined with `jε ≤ F qⱼ` (the
    right-continuous half, CDF-specific) this gives
    `leftLim F qⱼ₊₁ − F qⱼ ≤ ε`.

    No continuity or right-continuity of `F` is required: the left limit of a
    monotone `F` is the limit along `𝓝[<] q`, and the hypothesis bounds `F`
    on that entire left neighbourhood. -/
lemma leftLim_le_of_forall_lt {F : ℝ → ℝ} (hF : Monotone F) {q p : ℝ}
    (h : ∀ x, x < q → F x ≤ p) : Function.leftLim F q ≤ p := by
  have hev : ∀ᶠ x in nhdsWithin q (Set.Iio q), F x ≤ p :=
    Filter.eventually_of_mem self_mem_nhdsWithin (fun x hx => h x hx)
  exact le_of_tendsto (hF.tendsto_leftLim q) hev

end GlivenkoCantelli
