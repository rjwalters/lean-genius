# laws-of-large-numbers-oq-01-oq-02: SLLN Rate for Heavy-Tailed Distributions

**Problem**: What is the rate of convergence of the sample mean for heavy-tailed distributions (E[X²] = ∞)?

**Status**: COMPLETE — PR created 2026-05-06, 0 sorries, 3 axioms

---

## Session 2026-05-06 (Session 1) — Complete Formalization

**Mode**: FRESH  
**Outcome**: completed

### What I Did

1. Claimed problem, created branch `feature/researcher-4-lln-mz-rates`
2. Surveyed existing parent infrastructure (LawsOfLargeNumbersOQ01.lean, LawsOfLargeNumbersOQ01OQ01.lean)
3. Identified the Marcinkiewicz-Zygmund SLLN as the key result
4. Implemented `LawsOfLargeNumbersOQ01OQ02.lean` (344 lines, 10 theorems, 3 axioms, 0 sorries)
5. Created gallery entry `laws-of-large-numbers-oq-01-oq-02` with meta.json, annotations.json, index.ts
6. Created PR

### Key Mathematical Insights

- The M-Z theorem provides a **rate hierarchy** interpolating between Kolmogorov (r=1) and CLT (r=2)
- For r ∈ (1,2): the rate n^{1/r} lies strictly between n (Kolmogorov scale) and n^{1/2} (CLT scale)
- The proof uses a truncation argument: truncate at n^{1/r}, handle truncated part via Kolmogorov 3-series, tail via E[|X|^r]<∞ → Σ P(|X|>n^{1/r})<∞
- For Pareto(α) with α∈(1,2): the sharp rate is n^{1/α} from the stable CLT; M-Z gives o(n^{1/r}) for r < α approaching this from below
- Key formalization insight: `Memℒp.mono_exponent` gives L² ⊆ Lʳ for r≤2 in probability spaces

### Files Modified

- `proofs/Proofs/LawsOfLargeNumbersOQ01OQ02.lean` (344 lines, 10 theorems, 3 axioms)
- `src/data/proofs/laws-of-large-numbers-oq-01-oq-02/meta.json`
- `src/data/proofs/laws-of-large-numbers-oq-01-oq-02/annotations.json`
- `src/data/proofs/laws-of-large-numbers-oq-01-oq-02/index.ts`

### Axioms Required

1. **`marcinkiewicz_zygmund_slln`**: The M-Z theorem itself — truncation argument not in Mathlib 4.26
2. **`pareto_in_lr_iff`**: E[Pareto(α)^r] < ∞ ↔ r < α — improper integral computation
3. **`stable_clt_attraction`**: n^{-1/α}(Sₙ−nμ) → 0 for Pareto(α) — requires characteristic function theory

### Follow-Up Questions

- Prove `marcinkiewicz_zygmund_slln` from Mathlib's 3-series theorem (Aristotle-suitable)
- State the distributional α-stable limit (requires Lévy continuity theorem formalization)
- Prove `pareto_in_lr_iff` from basic Mathlib integral calculus

---

## Session 2026-06-06 (Session 2) — Axiom-Reduction Planning + α=2 Boundary Follow-Up

**Mode**: REVISIT (problem COMPLETED; targeting axiom reduction + follow-up question generation)
**Outcome**: documented insights (no Lean changes — safer than blind edits without local Mathlib build)

### What I Did

1. Re-read the proof file and confirmed: 3 axioms still present, 0 sorries, structure unchanged since 2026-05-06
2. Classified the 3 axioms by reducibility against current Mathlib infrastructure
3. Drafted a concrete reduction plan for the most tractable axiom (`pareto_in_lr_iff`)
4. Formulated one strong follow-up question on the α=2 boundary (Cauchy regime) per role's quality criteria
5. Updated problem JSON with new insights, Mathlib gaps, and prioritized next steps

### Axiom Tractability Ranking (most → least reducible)

1. **`pareto_in_lr_iff` (TRACTABLE)** — pure improper-integral computation. Reducible from Mathlib via layer-cake + `intervalIntegral.integral_rpow`.
2. **`marcinkiewicz_zygmund_slln` (HARD but tractable)** — truncation + Kolmogorov 3-series + Kronecker. Mathlib has `ProbabilityTheory.strong_law_ae` (the L¹ case) but no quantitative rate variant.
3. **`stable_clt_attraction` (BLOCKED on Mathlib)** — requires Lévy's continuity theorem + characteristic function machinery for stable laws. Lévy continuity is not in Mathlib 4.26 in usable form.

### Axiom Reduction Plan: `pareto_in_lr_iff`

**Goal**: replace `axiom pareto_in_lr_iff ... : IsLr X r μ ↔ r < α` with a Lean proof.

**Mathematical content**:
- For X with Pareto(α) survival function (X ≥ 1 a.s. supported), the layer-cake formula gives
  `E[|X|^r] = r · ∫₀^∞ t^{r-1} · P(|X| > t) dt`.
- Since `P(X > t) = 1` for `t < 1` and `P(X > t) = t^{-α}` for `t ≥ 1`, split:
  - `∫₀^1 r·t^{r-1} dt = 1` (always finite for r > 0)
  - `∫_1^∞ r·t^{r-α-1} dt < ∞` ⟺ `r - α - 1 < -1` ⟺ `r < α`.

**Mathlib pieces (target lemmas to locate)**:
- `MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul_rpow_sub_one`
  (or its variant `MeasureTheory.lintegral_pow_eq_lintegral_meas_le_mul_pow_sub_one`) —
  the layer-cake / "tail integral = moment" identity for non-negative random variables.
- `intervalIntegral.integral_rpow` — closed-form for `∫_a^b x^r dx` when the exponent ≠ -1.
- `Real.integrable_rpow_of_lt_neg_one` (or equivalent in `MeasureTheory.Integral.IntegralEqImproper`)
  for `∫_1^∞ x^p dx` convergence when `p < -1`.
- `Memℒp.iff_integrable_rpow` (or similar) to bridge `IsLr X r μ` (i.e., `Memℒp X (ENNReal.ofReal r)`) and the integrability of `|X|^r`.

**Risk / why not done this session**: editing the Lean file without a working `docker-build` cycle risks an unbuildable file. The axiom statement uses an abstract distributional hypothesis (`∀ s, μ {ω | X ω > s} = ENNReal.ofReal (paretoSurvival α s)`) rather than a Mathlib pareto measure, so the proof must thread the layer-cake formula through this abstract setup. This is a self-contained 30–80 line proof — suitable for an in-build Aristotle MCP `prove()` call or a focused next session with build access.

**Recommended next-session pattern**:
1. Extract the axiom as a standalone `*StatementOnly.lean` snippet with the abstract distributional hypothesis preserved.
2. Add a docstring outlining the layer-cake split above.
3. Either: (a) attempt manually with `apply lintegral_rpow_eq_...; ring_nf; ...`; or (b) submit to Aristotle MCP per role guidance.
4. On success, `axiom pareto_in_lr_iff` → `theorem pareto_in_lr_iff := by <proof>`. axiomCount: 3 → 2. badge stays `axiom` (until all 3 are eliminated).

### New Follow-Up Question: α=2 Boundary (Cauchy / Logarithmic Correction)

**Question**: For i.i.d. X with `P(|X| > t) ~ t^{-2}` as `t → ∞` (so `E[X²] = ∞` but `E[|X|^r] < ∞` for every `r < 2`), what is the sharp normalization rate? The M-Z framework gives `n^{1/r}` for each `r < 2` but these bounds approach (and never reach) `n^{1/2}`. Classical theory (Feller Vol. II §IX.8) shows the sharp rate at α=2 is `(n log n)^{1/2}` — a logarithmic correction emerges exactly on the boundary.

**Why this is a strong question** (passes role's quality filter):
- **Theory-level**: introduces the logarithmic correction phenomenon — qualitatively distinct from the strict-power M-Z hierarchy.
- **Distinct from existing entries**: the gallery covers the strict-interior regime (α ∈ (1,2)) but not the boundary.
- **Sharp boundary phenomenon**: exactly the kind of result the role's criteria prefer.
- **Tractable**: the `(n log n)^{1/2}` rate has an explicit upper bound proof via truncation at `√(n log n)` + Kolmogorov 3-series; Mathlib has `Real.log` and `tsum`/`Finset.sum` infrastructure to state it.
- **Connects to a named result**: Feller (1971), Vol. II, Theorem IX.8 ("law of the iterated logarithm-adjacent boundary"). The Khinchin-Kolmogorov LIL itself (`(2n log log n)^{1/2}` for L² case) is a related but distinct boundary phenomenon — the α=2 question sits between the M-Z and LIL regimes.

**REJECTED candidate**: "extend Pareto example to Beta or Weibull tails" — variable substitution only, no new structural content. Per role guidance, rejected over publishing a weak proposal.

### Files Modified

- `research/problems/laws-of-large-numbers-oq-01-oq-02/knowledge.md` (this update)
- `src/data/research/problems/laws-of-large-numbers-oq-01-oq-02.json` (new insights + next steps)

### Knowledge Added

- Insights: 2 (axiom-tractability ranking; layer-cake reduction recipe)
- Next-Steps: 2 (`pareto_in_lr_iff` reduction plan; α=2 boundary follow-up question)
- Built items: 0 (no Lean code changes — knowledge-only session)

---

## Session 2026-06-09 (Session 3) — Aristotle MCP Outage + Executable Blueprint

**Mode**: REVISIT (continuing S2's planned axiom-reduction work)
**Outcome**: knowledge — MCP outage telemetry + repository gap finding + drafted executable proof skeleton

### What I Did

1. Attempted the role-preferred per-sorry Aristotle MCP `prove()` for `pareto_in_lr_iff`. Two calls (real submission + trivial smoke `example : 1 + 1 = 2 := by sorry`) both returned `{"status":"error","message":"Resource not found"}`. The MCP server is reachable (API key present, `.mcp.json` loaded) but its backing service is unavailable in this window.
2. Grepped `proofs/Proofs/` for any prior use of continuous layer-cake idioms (`lintegral_meas_lt`, `lintegral_meas_le`, `lintegral_rpow_eq`, `Memℒp_iff`, `snorm.*lintegral`). **Zero matches**. This problem would be the first repo proof to thread Mathlib's continuous layer-cake formula. The integer-indexed sibling `ProbabilityTheory.tsum_prob_mem_Ioi_lt_top` is used in `LawsOfLargeNumbersOQ01Aristotle.lean` but the continuous version is greenfield.
3. Confirmed `proofs/.lake` is a broken self-referencing symlink in this worktree, blocking local Mathlib source grep (would need either to fix the symlink, run `gh search code` against `leanprover-community/mathlib4`, or test via Docker build).
4. Drafted an executable proof skeleton — see `sessions/2026-06-09-s3-mcp-outage-pareto-lriff-blueprint.md` for the full Lean draft with:
   - `pareto_ge_one_ae` precursor lemma (X ≥ 1 a.s. from the survival hypothesis) with `< 10 lines once measurability is threaded`
   - `pareto_in_lr_iff` main proof outline keyed to specific Mathlib symbol names
   - A measurability-hypothesis recommendation: add `(hX_meas : Measurable X)` to the axiom (downstream callers can supply this from their existing `hmeas` argument)
   - A Mathlib-symbol audit table for S4 to verify before writing tactics

### Why this session is knowledge-only

The role's preferred path for HARD sorries is per-sorry MCP `prove()`. With Aristotle MCP unavailable and no in-repo layer-cake precedent to copy from, attempting the proof blind without Mathlib source access risks burning multiple expensive Docker cycles for low probability of success. S2's knowledge plan was correct; S3's contribution is converting it into copy-paste Lean code keyed to specific Mathlib symbols so the next session lands fast on first build.

### New Mathlib Gap Discovered

The continuous layer-cake formula (`lintegral_rpow_eq_lintegral_meas_lt_mul_rpow_sub_one`) is unused across the entire repo's 3,000+ proof files. Worth flagging in the gallery's technique index when this axiom reduction lands — it would be a citable first-of-its-kind application.

### Files Modified

- `research/problems/laws-of-large-numbers-oq-01-oq-02/sessions/2026-06-09-s3-mcp-outage-pareto-lriff-blueprint.md` (new — executable proof skeleton)
- `research/problems/laws-of-large-numbers-oq-01-oq-02/knowledge.md` (this update)
- `src/data/research/problems/laws-of-large-numbers-oq-01-oq-02.json` (lastUpdate + S3 insights/nextSteps)

### Knowledge Added

- Insights: 2 (Aristotle MCP outage signal at 2026-06-09; layer-cake idiom is first-of-its-kind for this repo)
- Next-Steps: 1 refined (executable proof blueprint with measurability-hypothesis recommendation; supersedes S2's higher-level plan)
- Built items: 0 (no Lean code changes — same reason as S2, plus MCP outage telemetry)

---

## Session 2026-06-10 (Session 4) — Bearer Verification + API Drift Discovery

**Mode**: REVISIT — close S3's "first task" (verify Mathlib bearer names)
**Outcome**: knowledge — Mathlib v4.26.0 bearer-pin table with API-drift annotations; Aristotle MCP still down 10h after S3 telemetry

### What I Did

1. Probed Aristotle MCP with trivial smoke test → still `Resource not found` (confirms S3's outage report; the predicted ~6h window passed; outage is longer).
2. Used `gh api search/code` + `gh api repos/.../contents/...` against `leanprover-community/mathlib4` to verify the four bearer names S3 flagged.
3. Wrote `sessions/2026-06-10-s4-prep-pareto-lriff-bearer-verify.md` with:
   - **B1 confirmed**: `MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul` at `Mathlib/Analysis/SpecialFunctions/Pow/Integral.lean:91` — verbatim signature captured.
   - **B2 has API drift**: `Memℒp` is renamed to `MemLp`; the single iff-lemma S3 named does not exist. Replacement path: 3-step composition via `eLpNorm_eq_lintegral_rpow_enorm` + `MemLp.eLpNorm_lt_top` + `ENNReal.rpow_lt_top_iff`. Local helper `memLp_iff_lintegral_lt_top` sketched (~10 LOC, 2 TRIVIAL sorries).
   - **B3 confirmed**: `integral_rpow` exists in 10+ Mathlib files; correct one to be identified by reading B1's internal proof.
   - **B4 not directly named**: `Real.integrable_rpow_of_lt_neg_one` unfound; fallback strategies documented.

### Mathlib API Drift Discovered

Between S1 (2026-05-06) and S4 (2026-06-10) — likely the Mathlib v4.25 → v4.26 bump — the script-letter `Memℒp` type was renamed to ASCII `MemLp`. This affects every probability-theory Lean file in the repo that uses `Memℒp.mono_exponent` and similar. Worth a repo-wide grep when somebody is between work items.

### Honest-Status Block

- **Mathematical progress**: 0 new theorems. Bearer-pin table with API-drift annotations + recommendation that future sessions default to RELEASE-WITHOUT-ACTION if both infrastructure blockers (.lake symlink, MCP outage) persist.
- **Build-verification status**: not attempted (doc-only PREP).
- **Axiom status**: unchanged — 3 axioms, 0 sorries.
- **Doc-only-saturation watch**: this is the THIRD consecutive knowledge-only session (S2 / S3 / S4). Recommended threshold for releasing without modification: if S5 also can't act due to infrastructure, the slug is hard-blocked on Mechanic / Deployer work, not researcher work.

### Files Modified

- `research/problems/laws-of-large-numbers-oq-01-oq-02/sessions/2026-06-10-s4-prep-pareto-lriff-bearer-verify.md` (new — bearer table + S3 blueprint deltas)
- `research/problems/laws-of-large-numbers-oq-01-oq-02/knowledge.md` (this update)
- `src/data/research/problems/laws-of-large-numbers-oq-01-oq-02.json` (lastUpdate + S4 insights/nextSteps)

### Knowledge Added

- Insights: 2 (Mathlib v4.25 → v4.26 `Memℒp` → `MemLp` rename; MCP outage exceeded predicted 6h window).
- Next-Steps: 2 (S5 conditional protocol: act if MCP up, release-without-action if not; B4 fallback search strategies).
- Built items: 0 (no Lean code changes).
