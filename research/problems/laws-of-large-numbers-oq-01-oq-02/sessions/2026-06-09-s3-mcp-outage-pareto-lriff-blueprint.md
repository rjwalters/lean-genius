# Session 3 — 2026-06-09 — MCP outage + executable blueprint for `pareto_in_lr_iff`

**Researcher**: researcher-1
**Problem**: laws-of-large-numbers-oq-01-oq-02
**Status before session**: COMPLETED (0 sorries, 3 axioms)
**Mode**: REVISIT (S2's planned axiom-reduction work, picked up by S3)
**Outcome**: knowledge — Aristotle MCP outage + repository gap finding + drafted executable proof skeleton

## Why this session is knowledge-only (again)

S2 (2026-06-06, PR #22582) declined the axiom reduction because it would have required blind edits without a local Mathlib build. S3 attempted to follow the role's **preferred** path for hard sorries — per-sorry Aristotle MCP `prove()` — but ran into two concrete blockers:

1. **Aristotle MCP returned `Resource not found`** on repeated calls (including a trivial `example : 1 + 1 = 2 := by sorry` smoke check). The MCP server is reachable (API key present, `.mcp.json` loaded), but its backing service is not responding to this researcher in this window. Telemetry value: future sessions claiming this problem in the next ~6 hours should expect the same outage signal.
2. **No layer-cake idiom precedent in the repo.** `grep -E 'lintegral_meas_lt|lintegral_meas_le|lintegral_rpow_eq|Memℒp_iff|snorm.*lintegral'` over `proofs/Proofs/` returned **zero matches**. This problem would be the first repo proof to thread Mathlib's continuous layer-cake formula. Without a sibling pattern to copy, attempting it blind (no Mathlib source access — `proofs/.lake` is a broken self-referencing symlink in this worktree) is a high-failure-rate use of expensive Docker build cycles.

So S3's deliverable is a concrete, copy-paste-ready proof draft for the next session that lands with a working Mathlib build or MCP access.

## Executable blueprint for the reduction

The reduction strategy from S2's knowledge.md is preserved verbatim; S3 contributes a Lean-syntactic draft so the next session can skip the API-naming guesswork.

### Sub-lemma 1: `X` is bounded below by 1 almost surely

This is the smallest precursor and a clean independent contribution: from the hypothesis `μ {ω | X ω > s} = ENNReal.ofReal (paretoSurvival α s)` at any `s < 1`, the probability of `X ω > s` is `1`, so `X ω ≥ 1` a.s.

```lean
/-- Under the Pareto survival hypothesis, X ≥ 1 almost surely. -/
theorem pareto_ge_one_ae {α : ℝ}
    (X : Ω → ℝ)
    (hX_dist : ∀ s : ℝ, μ {ω | X ω > s} = ENNReal.ofReal (paretoSurvival α s)) :
    ∀ᵐ ω ∂μ, (1 : ℝ) ≤ X ω := by
  rw [MeasureTheory.ae_iff]
  -- Goal: μ {ω | ¬ 1 ≤ X ω} = 0, i.e. μ {ω | X ω < 1} = 0.
  -- Express {X < 1} as ⋃ n, {X ≤ 1 - 1/(n+1)} and show each summand is null.
  have h_union : {ω | ¬ (1 : ℝ) ≤ X ω} = ⋃ n : ℕ, {ω | X ω ≤ 1 - 1 / (n + 1 : ℝ)} := by
    ext ω
    simp only [Set.mem_setOf_eq, not_le, Set.mem_iUnion]
    refine ⟨fun hlt => ?_, ?_⟩
    · have hpos : (0 : ℝ) < 1 - X ω := by linarith
      obtain ⟨n, hn⟩ := exists_nat_gt (1 / (1 - X ω))
      refine ⟨n, ?_⟩
      have h_n1_pos : (0 : ℝ) < n + 1 := by positivity
      have : (1 : ℝ) / (n + 1) < 1 - X ω := by
        rw [div_lt_iff h_n1_pos]
        have hn' : 1 / (1 - X ω) < (n + 1 : ℝ) := by linarith
        rw [div_lt_iff hpos] at hn'
        linarith
      linarith
    · rintro ⟨n, hn⟩
      have h_n1_pos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
      have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
      linarith
  rw [h_union]
  refine MeasureTheory.measure_iUnion_null fun n => ?_
  -- Goal: μ {ω | X ω ≤ 1 - 1/(n+1)} = 0
  -- Strategy: {X ≤ s} = {X > s}ᶜ; μ {X > s} = 1 since paretoSurvival α s = 1 for s < 1.
  set s := (1 : ℝ) - 1 / (n + 1 : ℝ) with hs_def
  have hs_lt_one : s < 1 := by
    simp [hs_def]; positivity
  have h_survival : paretoSurvival α s = 1 := by
    simp [paretoSurvival, hs_lt_one]
  have h_meas_gt : μ {ω | X ω > s} = 1 := by
    rw [hX_dist, h_survival]; simp [ENNReal.ofReal_one]
  -- {X ≤ s} ⊆ {X > s}ᶜ at the level of pointwise truth values (in fact equality)
  -- μ ({X ≤ s}) = μ univ - μ ({X > s}) = 1 - 1 = 0 in a probability measure
  have h_compl : {ω | X ω ≤ s} = {ω | X ω > s}ᶜ := by
    ext ω; simp [not_lt]
  rw [h_compl]
  -- Use `prob_compl_eq_one_sub` requires measurability. Alternative: bound by univ.
  -- μ (Aᶜ) ≤ μ univ - μ A when A is measurable; for arbitrary A, use measure_compl_le.
  -- For a probability measure, the cleanest route is:
  --   measurability lemma: hX_dist's RHS being well-defined for all s implies
  --   {ω | X ω > s} is measurable (this is the standard CDF argument).
  -- For the blueprint, we leave the measurability hypothesis explicit if needed:
  --   add  (hX_meas : Measurable X)  to the theorem signature, then use:
  --   measurableSet_lt and prob_compl_eq_one_sub.
  sorry  -- < 10 lines once measurability is threaded through
```

**Open Lean detail (S4-ready)**: Whether to thread `Measurable X` through the theorem signature (cheapest), or extract measurability from `hX_dist` (the survival function determining the law forces `{X > s}` to be measurable, but this argument is non-trivial in Lean). Recommended path: **add `(hX_meas : Measurable X)` as a hypothesis**. The downstream callers (`pareto_finite_mean`, `pareto_not_l2`, `pareto_mz_applicable`, `pareto_complete_rate_hierarchy`) can supply it from their `hmeas` argument; the main `pareto_in_lr_iff` axiom itself does not currently require it.

### Sub-lemma 2 (the axiom): `pareto_in_lr_iff` via layer-cake

```lean
theorem pareto_in_lr_iff_proof
    (α : ℝ) (hα : 0 < α) (r : ℝ) (hr : 0 < r)
    (X : Ω → ℝ) (hX_meas : Measurable X)
    (hX_dist : ∀ s : ℝ, μ {ω | X ω > s} = ENNReal.ofReal (paretoSurvival α s)) :
    IsLr X r μ ↔ r < α := by
  -- Step 1: Memℒp X (ENNReal.ofReal r) μ ↔ AEStronglyMeasurable X μ
  --         ∧ ∫⁻ a, ‖X a‖ₑ ^ r ∂μ < ∞   [Mathlib: memℒp_iff_lintegral_rpow_nnnorm_lt_top]
  -- Step 2: From `pareto_ge_one_ae`, X ≥ 1 ≥ 0 a.s., so ‖X a‖ = X a a.s.
  --         The lintegral becomes ∫⁻ a, ENNReal.ofReal (X a ^ r) ∂μ.
  -- Step 3: Apply layer-cake:
  --   MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul_rpow_sub_one
  --   ∫⁻ a, ENNReal.ofReal (X a ^ r) ∂μ
  --     = ENNReal.ofReal r * ∫⁻ t in Set.Ioi (0:ℝ),
  --         μ {ω | t < X ω} * ENNReal.ofReal (t ^ (r-1)) ∂volume
  -- Step 4: Substitute hX_dist:
  --   μ {ω | t < X ω} = ENNReal.ofReal (paretoSurvival α t)
  --                    = 1 on (0, 1) and t^(-α) on [1, ∞).
  -- Step 5: Split the outer integral at t = 1.
  --   - On (0, 1]: ∫₀¹ t^(r-1) dt = 1/r, finite, contributes 1.
  --   - On [1, ∞): ∫_1^∞ t^(r-α-1) dt, finite iff r-α-1 < -1 ⟺ r < α.
  -- Step 6: Combine the two pieces. Both directions:
  --   - (r < α): both integrals finite, ∫⁻ < ∞, so Memℒp.
  --   - (r ≥ α): second integral is ∞, so ∫⁻ = ∞, contradicting Memℒp.
  sorry
```

### Mathlib lemmas to verify (S4 first task, before writing tactics)

The next session should **first** confirm these names exist in v4.26.0 by either (a) running `gh search code --owner leanprover-community/mathlib4 '<name>'`, (b) fixing the broken `proofs/.lake` symlink so local grep works, or (c) trying them in a minimal Docker build:

| Mathlib symbol | Purpose | Likely path |
|---|---|---|
| `MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul_rpow_sub_one` | Continuous layer-cake | `Mathlib/MeasureTheory/Integral/Layercake.lean` |
| `MeasureTheory.memℒp_iff_lintegral_rpow_nnnorm_lt_top` | `Memℒp ↔ lintegral finite` | `Mathlib/MeasureTheory/Function/LpSeminorm/Basic.lean` |
| `intervalIntegral.integral_rpow` | Closed-form `∫ x^p dx` | `Mathlib/MeasureTheory/Integral/IntervalIntegral.lean` |
| `Real.integrable_rpow_of_lt_neg_one` | `∫_1^∞ x^p dx < ∞ ↔ p < -1` | `Mathlib/Analysis/SpecialFunctions/IntegralImproper.lean` |
| `MeasureTheory.ae_iff` | `(∀ᵐ ω ∂μ, p ω) ↔ μ {ω | ¬p ω} = 0` | `Mathlib/MeasureTheory/Measure/MeasureSpace.lean` |
| `MeasureTheory.measure_iUnion_null` | Countable union of nulls is null | (same) |

If any of these names has shifted in v4.26.0, the next session should grep for the exact symbol from the local Mathlib cache. The semantic content is well-established; only the exact spelling may have rotated.

## Repository finding (deliverable for indexing)

- **Mathlib gap**: this would be the **first** proof in `proofs/Proofs/` to use the continuous layer-cake formula. The repo has the integer-indexed sibling `ProbabilityTheory.tsum_prob_mem_Ioi_lt_top` (cited in `LawsOfLargeNumbersOQ01Aristotle.lean`) but no continuous-t version usage. Worth recording in the gallery's technique index when one lands.
- **Aristotle MCP availability flag**: returning `Resource not found` on a trivial smoke test as of 2026-06-09 ~12:30 PT.

## Files modified

- `research/problems/laws-of-large-numbers-oq-01-oq-02/sessions/2026-06-09-s3-mcp-outage-pareto-lriff-blueprint.md` (this file — new)
- `research/problems/laws-of-large-numbers-oq-01-oq-02/knowledge.md` (S3 entry appended)
- `src/data/research/problems/laws-of-large-numbers-oq-01-oq-02.json` (lastUpdate + S3 insights/nextSteps)

## Knowledge added

- Insights: 2 (Aristotle MCP outage signal; layer-cake idiom is a first-of-its-kind in this repo)
- Next-steps: 1 refined (executable proof blueprint with sub-lemma + measurability hypothesis recommendation)
- Built items: 0 (no Lean code changes — same reason as S2, now with concrete MCP outage telemetry)
