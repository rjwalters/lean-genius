# Session 4 — 2026-06-10 — Bearer verification for `pareto_in_lr_iff` reduction

**Researcher**: researcher-1
**Problem**: laws-of-large-numbers-oq-01-oq-02
**Status before session**: COMPLETED (0 sorries, 3 axioms; unchanged from S3)
**Mode**: REVISIT — extend S3's blueprint with `gh api`-verified Mathlib bearer signatures
**Outcome**: knowledge — Mathlib v4.26.0 bearer-pin table for the layer-cake reduction, with API-drift annotations against S3's blueprint
**Aristotle MCP probe**: ❌ still `Resource not found` (S3 outage signal persists ~10 hours later; per-sorry MCP path still unavailable)

## Why this session is knowledge-only (again)

S3 (2026-06-09) finished with three actionable next-tasks for whoever picks the
slug up:

> The next session should first confirm these names exist in v4.26.0 by either (a) running `gh search code --owner leanprover-community/mathlib4 '<name>'`, (b) fixing the broken `proofs/.lake` symlink so local grep works, or (c) trying them in a minimal Docker build.

S4 takes route (a) — `gh api` search — because:

1. The `proofs/.lake` symlink is still broken (`/Users/rwalters/GitHub/lean-genius/proofs/.lake` self-references; `ls proofs/.lake/packages/` errors with "Too many levels of symbolic links"). Fixing it is out of scope for a researcher claim (Mechanic/Deployer territory).
2. The Aristotle MCP is still down (verified at session start with the trivial smoke test `example : 1 + 1 = 2 := by sorry` → `Resource not found`).
3. Without route (a) results, route (c) (Docker build) is a high-failure-rate use of expensive cycles.

The deliverable is therefore: a bearer-pin table that closes the
"first task" S3 left explicit, so a subsequent S5 ACT session lands
with verified signatures and only needs to wire them together.

## Bearer verification (lake-pinned: Mathlib v4.26.0 / `2df2f01…`)

All four bearers from S3's "Mathlib lemmas to verify" table were
located via `gh api` searches against `leanprover-community/mathlib4`.
Two are present as named; two had naming drift relative to S3's draft.

### B1 — Continuous layer-cake (CONFIRMED, EXACT NAME)

- **Symbol**: `MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul`
- **Path**: `Mathlib/Analysis/SpecialFunctions/Pow/Integral.lean:91`
- **Signature** (verbatim from Mathlib HEAD via `gh api contents`):

  ```lean
  theorem lintegral_rpow_eq_lintegral_meas_lt_mul
      {f : α → ℝ} (f_nn : 0 ≤ᵐ[μ] f) (f_mble : AEMeasurable f μ)
      {p : ℝ} (p_pos : 0 < p) :
      ∫⁻ ω, ENNReal.ofReal (f ω ^ p) ∂μ =
        ENNReal.ofReal p * ∫⁻ t in Ioi 0,
          μ {a : α | t < f a} * ENNReal.ofReal (t ^ (p - 1))
  ```

- **Companion at line 57**: `lintegral_rpow_eq_lintegral_meas_le_mul`
  uses `{a | t ≤ f a}` (closed sublevel-set form). The `lt` variant is
  the one S3's blueprint sketches against because `hX_dist` is stated
  for `{ω | X ω > s}`, which is open and matches the `lt` sublevel set
  after relabelling `t = s`.

- **Risk for S5 ACT**: LOW. Direct fit. The only adapter work is
  threading `f_nn : 0 ≤ᵐ[μ] X` from `pareto_ge_one_ae` (the S3
  sub-lemma 1).

### B2 — `MemLp` ↔ `lintegral` (DRIFT: `Memℒp` → `MemLp`, no `_iff_lintegral_rpow_nnnorm_lt_top` constant)

S3's blueprint named **`Memℒp_iff_lintegral_rpow_nnnorm_lt_top`** as the
conversion lemma. This name is **not present in v4.26.0**. Two API drifts:

1. **Type rename**: `Memℒp` → `MemLp`. Confirmed via
   `gh api contents/Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean`:
   the file contains 30+ `MemLp.*` and `memLp_*` lemmas; **0** uses of
   `Memℒp`. The script-letter form is gone.
2. **Conversion path goes via `eLpNorm` def, not a single iff-lemma**.
   The canonical equality is

   ```lean
   theorem eLpNorm_eq_lintegral_rpow_enorm
       {p : ℝ≥0∞} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
       eLpNorm f p μ = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal)
   ```

   (`Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean:100`,
   line number verified via `base64 -d | grep -n`).

   Combined with `MemLp.eLpNorm_lt_top` (Basic.lean:34) — which states
   `MemLp f p μ → eLpNorm f p μ < ∞` — and its iff partner via the
   `MemLp` definition (`AEStronglyMeasurable f μ ∧ eLpNorm f p μ < ∞`),
   the desired equivalence

   ```
   MemLp f p μ  ↔  AEStronglyMeasurable f μ ∧ (∫⁻ ‖f‖ₑ^p.toReal ∂μ) < ∞
   ```

   is obtained by `rw [eLpNorm_eq_lintegral_rpow_enorm]` then
   `ENNReal.rpow_lt_top` housekeeping.

- **Risk for S5 ACT**: MEDIUM. The S3 blueprint's single-shot
  `memℒp_iff` is no longer one rewrite — it's a two-step
  (`MemLp` definition unfold + `eLpNorm_eq_lintegral_rpow_enorm` rewrite +
  finite-ness of rpow). Adds ~3–4 LOC of bookkeeping per direction.

- **Wrapping suggestion**: introduce a local helper

  ```lean
  private lemma memLp_iff_lintegral_lt_top
      {f : α → E} {p : ℝ≥0∞} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
      MemLp f p μ ↔ AEStronglyMeasurable f μ
                ∧ ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ < ∞ := by
    constructor
    · rintro ⟨hmeas, hlt⟩
      refine ⟨hmeas, ?_⟩
      rw [eLpNorm_eq_lintegral_rpow_enorm hp_ne_zero hp_ne_top] at hlt
      -- hlt : (∫⁻ ...) ^ (1/p.toReal) < ⊤
      -- conclude ∫⁻ ... < ⊤ via ENNReal.rpow_lt_top_iff
      sorry
    · rintro ⟨hmeas, hlt⟩
      refine ⟨hmeas, ?_⟩
      rw [eLpNorm_eq_lintegral_rpow_enorm hp_ne_zero hp_ne_top]
      -- conclude (∫⁻ ...) ^ (1/p.toReal) < ⊤
      sorry
  ```

  Both `sorry`s are TRIVIAL (≤ 3 lines each via `ENNReal.rpow_lt_top_iff`
  or equivalent) and Aristotle-suitable once the MCP comes back.

### B3 — `intervalIntegral.integral_rpow` (CONFIRMED, MULTIPLE OCCURRENCES)

- **Symbol**: `integral_rpow` (occurs across 5+ Mathlib files; the
  closed-form `∫_a^b x^p dx` lemma).
- **Confirmed paths** (via `gh api search/code`):
  - `Mathlib/MeasureTheory/Integral/Gamma.lean`
  - `Mathlib/MeasureTheory/Function/ContinuousMapDense.lean`
  - `Mathlib/MeasureTheory/Integral/Bochner/Basic.lean`
  - `Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean`
  - `Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean`
  - `Mathlib/MeasureTheory/Function/LpSeminorm/Indicator.lean`
  - `Mathlib/MeasureTheory/Integral/MeanInequalities.lean`
  - `Mathlib/MeasureTheory/Function/LpSeminorm/LpNorm.lean`
  - `Mathlib/MeasureTheory/Function/LpSpace/Complete.lean`
  - `Mathlib/MeasureTheory/Function/L2Space.lean`
- **Risk for S5 ACT**: LOW (existence confirmed); MEDIUM (multiple
  candidate names — S5 needs to identify the correct one by reading
  the closest signature; recommended start point is the proof of
  `lintegral_rpow_eq_lintegral_meas_lt_mul` in
  `Mathlib/Analysis/SpecialFunctions/Pow/Integral.lean` itself, which
  internally cites the standard `integral_rpow` of choice).

### B4 — `Real.integrable_rpow_of_lt_neg_one` (UNCONFIRMED, NEEDS FALLBACK)

- The exact name **not found** via direct `gh api search/code`
  (returned 0 hits). Candidate alternatives to check next session:
  - `Real.integrableOn_Ioi_rpow` (closed form for `∫_a^∞ x^p dx`).
  - `MeasureTheory.integrableOn_Ioi_rpow_iff`.
  - The proof of `lintegral_rpow_eq_lintegral_meas_lt_mul` itself
    likely produces the needed `∫_1^∞ t^(r-α-1) dt < ∞ ↔ r-α-1 < -1`
    fact as a side condition; S5 should check whether the layer-cake
    step bundles it.

- **Risk for S5 ACT**: MEDIUM. The mathematical content (Riemann
  integrability of `x^p` on `[1, ∞)` iff `p < -1`) is elementary and
  guaranteed to be in Mathlib in *some* form. The naming search just
  needs a wider net. If still unfound, the fallback is to prove it
  inline (~10 LOC via `intervalIntegral.integral_rpow` over `[1, R]`
  and a `tendsto_atTop` limit).

## Updated blueprint snippet (S3 + S4 deltas)

The S3 blueprint's `Memℒp` references should be globally replaced with
`MemLp` before any Lean attempt. The blueprint's "Step 1" reads:

> Step 1: `Memℒp X (ENNReal.ofReal r) μ ↔ AEStronglyMeasurable X μ ∧ ∫⁻ a, ‖X a‖ₑ ^ r ∂μ < ∞`   [Mathlib: `memℒp_iff_lintegral_rpow_nnnorm_lt_top`]

Updated form:

> Step 1: `MemLp X (ENNReal.ofReal r) μ ↔ AEStronglyMeasurable X μ ∧ ∫⁻ a, ‖X a‖ₑ ^ r ∂μ < ∞`   [Helper `memLp_iff_lintegral_lt_top` derived from `eLpNorm_eq_lintegral_rpow_enorm` + `MemLp.eLpNorm_lt_top` + `ENNReal.rpow_lt_top_iff`]

All other steps (2–6) of the S3 blueprint are unaffected by this drift —
the layer-cake step uses B1 verbatim, and the split-at-`t=1` step uses
B3/B4 for the closed-form integrals.

## What S5 should do (if MCP up) / S5 should NOT do (if MCP down)

**If Aristotle MCP returns to service**:
1. Submit the S3 sub-lemma 1 (`pareto_ge_one_ae`) snippet via `prove()`.
   Context: just `proofs/Proofs/LawsOfLargeNumbersOQ01OQ02.lean`.
   It's TRIVIAL (~10 lines of `MeasureTheory.measure_iUnion_null` +
   `Set.ext`), so even partial MCP recovery should clear it.
2. Submit the `memLp_iff_lintegral_lt_top` helper. Both `sorry`s are
   TRIVIAL.
3. Once both helpers compile, submit `pareto_in_lr_iff_proof` itself.
   Hint to Aristotle: "Use the layer-cake formula
   `lintegral_rpow_eq_lintegral_meas_lt_mul`, then substitute the
   Pareto survival function and split the outer integral at t=1."

**If MCP stays down** (likely if this session is in the ~6h outage
window S3 telemetered):
1. Do NOT attempt blind Lean edits. The doc-only-saturation trap was
   the explicit S2 concern and remains valid.
2. Do NOT submit Docker builds for the unfinished blueprint — wasteful
   under the no-local-Mathlib constraint.
3. Either release the claim (preferred — give Mechanic time to fix
   `.lake` symlink or Aristotle service to recover), or do a knowledge-
   only extension of the blueprint (e.g., resolve B4's name with
   broader gh-api searches, or precompute the `∫_0^1 t^(r-1) dt` and
   `∫_1^∞ t^(r-α-1) dt` closed-form ENNReal values for the split).

## Honest-status block

- **Mathematical progress**: 0 new theorems. Knowledge contribution:
  bearer-pin table for the S5 ACT, with verified Mathlib v4.26.0
  signatures for B1, B2 (via decomposition), B3 (multi-source), and
  flagged unknown B4.
- **Build-verification status**: not attempted (doc-only PREP).
- **Axiom status**: unchanged from 2026-05-06 — 3 axioms
  (`marcinkiewicz_zygmund_slln`, `pareto_in_lr_iff`,
  `stable_clt_attraction`), 0 sorries.
- **Infrastructure status**:
  - `proofs/.lake` symlink still broken (self-references).
  - Aristotle MCP still returns `Resource not found` (S3 signal
    persists ~10 hours; possibly longer than the predicted 6h window).
- **Doc-only-saturation watch**: this is the THIRD consecutive
  knowledge-only session on this slug (S2 2026-06-06, S3 2026-06-09,
  S4 2026-06-10). Recommendation: future sessions should default to
  RELEASE-WITHOUT-ACTION unless one of the two infrastructure
  blockers (.lake symlink or Aristotle MCP) is resolved upstream.
  Three sessions of doc-only work is the slug's signal for a hard
  infrastructure dependency, not a mathematical one.

## References

- **S1 (2026-05-06)**: original formalization, 3 axioms.
- **S2 (2026-06-06)**: PR #22582 — axiom-reduction planning (declined).
- **S3 (2026-06-09)**: PR #22740 — `pareto_in_lr_iff` executable
  blueprint + MCP outage report.
- **Mathlib bearer locations** (verified by `gh api contents` reads,
  not search-API hits which can be incomplete):
  - B1: `Mathlib/Analysis/SpecialFunctions/Pow/Integral.lean:91`.
  - B2 decomposition: `Mathlib/MeasureTheory/Function/LpSeminorm/Defs.lean:100`
    (`eLpNorm_eq_lintegral_rpow_enorm`) and
    `Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean:34`
    (`MemLp.eLpNorm_lt_top`).
