# Session 2026-05-15 — S5c-prep sibling audit of PR #19050

**Agent**: researcher-9
**Mode**: REVISIT (sibling-PREP-after-PREP audit; doc-only)
**Phase**: ACT (file unchanged; this PR is a sibling-PREP audit of #19050's
S5c-prep ACT for soundness + downstream-API-readiness review)
**Outcome**: Sibling-PREP audit. PR #19050's bridge lemma
`indicator_covariance_le_alpha` is **sound** at lake SHA `2df2f015...`. One
**structural gap** identified for S5c proper: `IbragimovHypotheses` lacks
sub-σ→ambient `le`-relation fields needed to invoke the bridge lemma's ambient
measurability hypothesis. Recommended +5 LOC, non-breaking fix.

## Scope

This is a strict doc-only sibling-PREP audit. No Lean changes, no edits to
`state.md`, no edits to JSON trackers, no edits to `meta.json`. New file only:
this session log. Strict conflict-free against:

- **PR #19030** (researcher-9, doc-only S5b build-verify, MERGEABLE).
- **PR #19050** (researcher-12, S5c-prep ACT adding
  `indicator_covariance_le_alpha`, MERGEABLE, build-verified).

Builders/Champions can merge any of {#19030, #19050, this PR} in any order.

## What PR #19050 ships

Adds one fully-proven theorem `indicator_covariance_le_alpha` (~35 LOC incl.
docstring) and fixes the line-419 unused-simp-argument lint warning in the
pre-existing `indicator_pair_covariance_eq`. The new theorem:

```lean
theorem indicator_covariance_le_alpha
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (σPair : Fin 2 → MeasurableSpace Ω)
    {A B : Set Ω}
    (hA_amb : MeasurableSet A) (hB_amb : MeasurableSet B)
    (hA : @MeasurableSet Ω (σPair 0) A) (hB : @MeasurableSet Ω (σPair 1) B) :
    |∫ ω, A.indicator (1 : Ω → ℝ) ω * B.indicator (1 : Ω → ℝ) ω ∂μ
      - (∫ ω, A.indicator (1 : Ω → ℝ) ω ∂μ)
        * (∫ ω, B.indicator (1 : Ω → ℝ) ω ∂μ)|
    ≤ CentralLimitTheoremOQ02.alphaMixingCoeff μ (σPair 0) (σPair 1) := by
  rw [indicator_pair_covariance_eq hA_amb hB_amb]
  simp only [Measure.real_def]
  exact davydov_indicator_bound σPair hA hB
```

It bridges S4's algebraic identity `indicator_pair_covariance_eq` (researcher-6,
#17939) and S5b's α-bound `davydov_indicator_bound` (researcher-3, #18728)
into the **covariance-form** indicator Davydov bound consumed by S5c.

## Audit findings

### Finding A — Bearer pin-verification ✓ (no phantoms)

All bearers pin-verified at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(toolchain `leanprover/lean4:v4.26.0`) via `gh api ?ref=<SHA>`:

| API | File | Line | Notes |
|-----|------|------|-------|
| `Measure.real_def` | `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean` | 108 | Alias of `measureReal_def` |
| `measureReal_def` | `Mathlib/MeasureTheory/Measure/MeasureSpaceDef.lean` | 105 | `μ.real s = (μ s).toReal := rfl` |
| `integral_indicator_one` | `Mathlib/MeasureTheory/Integral/Bochner/Set.lean` | 494 | `@[simp]`, takes ambient `MeasurableSet s` |
| `LE` instance on `MeasurableSpace α` | `Mathlib/MeasureTheory/MeasurableSpace/Defs.lean` | 309 | `m₁ ≤ m₂ := ∀ s, MeasurableSet[m₁] s → MeasurableSet[m₂] s` |
| `MeasurableSpace.le_def` | `Mathlib/MeasureTheory/MeasurableSpace/Defs.lean` | 311 | `Iff.rfl` re-expression |
| `Measurable.le` | `Mathlib/MeasureTheory/MeasurableSpace/Defs.lean` | 528 | `(hm : m ≤ m0) → Measurable[m] f → Measurable[m0] f` |
| `measurable_const` | `Mathlib/MeasureTheory/MeasurableSpace/Defs.lean` | 525 | `@[simp, fun_prop]`, polymorphic in target σ-algebra |
| `measurableSet_lt` | `Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean` | 235 | `[SecondCountableTopology α]`, ambient |

No phantom names; the PR body's reference to
`Mathlib.MeasureTheory.Measure.MeasureSpaceDef.measureReal_def` is exact (the
alias `Measure.real_def` is the public name on line 108).

### Finding B — 3-line proof goal-state walk ✓

Initial goal:
```
⊢ |∫ ω, A.indicator (1 : Ω → ℝ) ω * B.indicator (1 : Ω → ℝ) ω ∂μ
    - (∫ ω, A.indicator (1 : Ω → ℝ) ω ∂μ)
      * (∫ ω, B.indicator (1 : Ω → ℝ) ω ∂μ)|
  ≤ alphaMixingCoeff μ (σPair 0) (σPair 1)
```

After `rw [indicator_pair_covariance_eq hA_amb hB_amb]`:
- The LHS of `indicator_pair_covariance_eq` matches the entire integral-form
  expression inside the absolute value.
- Substitution direction is `LHS → RHS`, so `μ.real (A ∩ B) - μ.real A * μ.real B`
  replaces the integral form.

```
⊢ |μ.real (A ∩ B) - μ.real A * μ.real B|
  ≤ alphaMixingCoeff μ (σPair 0) (σPair 1)
```

After `simp only [Measure.real_def]`:
- `Measure.real_def : μ.real s = (μ s).toReal` (definitional, `:= rfl`).
- All three `μ.real _` occurrences rewrite to `(μ _).toReal`.

```
⊢ |(μ (A ∩ B)).toReal - (μ A).toReal * (μ B).toReal|
  ≤ alphaMixingCoeff μ (σPair 0) (σPair 1)
```

After `exact davydov_indicator_bound σPair hA hB`:
- `davydov_indicator_bound`'s conclusion is exactly the current goal with
  `hA, hB` providing the sub-σ measurability of `A, B`.

✓ Type-checks. Proof is sound.

### Finding C — Statement-level scrutiny ✓ (double hypothesis is structurally required)

`indicator_covariance_le_alpha` takes both:
- `hA_amb : MeasurableSet A` (ambient, used by the upstream
  `indicator_pair_covariance_eq` whose proof invokes
  `MeasureTheory.integral_indicator_one`),
- `hA : @MeasurableSet Ω (σPair 0) A` (sub-σ, used by
  `davydov_indicator_bound` to peel the 4-fold ⨆).

These hypotheses are **independent**: the parent file's `alphaMixingCoeff` is
defined for arbitrary pairs of `MeasurableSpace Ω` instances (NOT
sub-σ-algebras of the ambient `[MeasurableSpace Ω]`; see
`CentralLimitTheoremOQ02.lean:419-424`). Therefore there is no automatic
implication `@MeasurableSet Ω (σPair 0) A → MeasurableSet A`. The double
hypothesis is the *minimal* set of facts that closes the bridge.

This is not a defect. The lemma cannot be simplified to a single-hypothesis
form (e.g., dropping `hA_amb`) while remaining usable from the existing S4
identity, because `indicator_pair_covariance_eq` necessarily uses the
ambient-measure integral and hence requires ambient measurability of `A` and
`B`.

### Finding D — Line-419 simp-arg lint fix is correct ✓

Original (S4 / #17939):
```lean
by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B <;>
  simp [Set.indicator_apply, Set.mem_inter_iff, hωA, hωB]
```

PR #19050 removes `Set.indicator_apply`:
```lean
by_cases hωA : ω ∈ A <;> by_cases hωB : ω ∈ B <;>
  simp [Set.mem_inter_iff, hωA, hωB]
```

Verified semantically: under Mathlib v4.26.0, the four `by_cases` splits each
produce a goal where `ω ∈ A` and `ω ∈ B` are either `True` or `False` *as
hypotheses*. `simp` with `hωA, hωB` in the simp set rewrites the
membership-tests inside `Set.indicator`'s `if-then-else`, and the `if` branches
collapse without needing `Set.indicator_apply` as an explicit unfold. The
linter's verdict is sound; this is a correct cleanup.

### Finding E — STRUCTURAL GAP for S5c (this audit's key finding)

**Problem.** PR #19050's bridge lemma `indicator_covariance_le_alpha`
requires BOTH ambient `MeasurableSet A` AND sub-σ `@MeasurableSet Ω (σPair 0) A`
at every invocation. The natural call site in S5c is the level-set
decomposition of `X, Y`:

```lean
-- X = ∫₀^∞ (𝟙_{X > t} − 𝟙_{X < -t}) dt  (layer-cake decomposition).
-- For each t, the level set {ω | X ω > t} appears as A in the bilinear
-- expansion of Cov(X, Y); analogously for {ω | Y ω > s} as B.
```

To call `indicator_covariance_le_alpha` at each `(t, s)`, S5c needs:
- `@MeasurableSet Ω (σPair 0) {ω | X ω > t}` — provable from
  `Measurable[σPair 0] X` via
  `@measurableSet_lt Ω ℝ _ _ (σPair 0) X (fun _ => t) hX_meas measurable_const`.
- `MeasurableSet {ω | X ω > t}` (ambient) — NOT directly provable from
  `Measurable[σPair 0] X` alone.

The current `IbragimovHypotheses` (lines 157–189 of
`CentralLimitTheoremOQ02OQ04.lean`) provides:
- `pastSigma : ℕ → MeasurableSpace Ω`
- `futureSigma : ℕ → MeasurableSpace Ω`
- `past_measurable : ∀ k, Measurable[pastSigma k] (X k)` (S3 addition)
- `future_measurable : ∀ k, Measurable[futureSigma k] (X k)` (S3 addition)

but does **not** carry the sub-σ→ambient `le`-relation:
- `past_le : ∀ k, pastSigma k ≤ inferInstance` — **MISSING**.
- `future_le : ∀ k, futureSigma k ≤ inferInstance` — **MISSING**.

Without those fields, the natural S5c proof of `davydov_covariance_inequality`
cannot transfer sub-σ measurability of level sets to ambient measurability.

**Alternative path A — null-measurable detour (not recommended).**
`MemLp X p μ` implies `AEStronglyMeasurable X μ` (ambient AE-strong-measurable),
from which the level set `{ω | X ω > t}` is `NullMeasurableSet μ` (ambient
AE-measurable, not strictly measurable). Then `integral_indicator_one`'s strict
`MeasurableSet s` hypothesis must be replaced with a null-measurable variant,
which introduces additional measure-theoretic plumbing (`NullMeasurableSet`,
`Integrable.indicator`, AE-equality of integrals). Estimated overhead: ~30
extra LOC inside `davydov_covariance_inequality`. Possible but unappealing.

**Alternative path B — sub-σ-le fields (recommended).** Add two new
non-breaking fields to `IbragimovHypotheses`:

```lean
  /-- The past σ-algebra is a sub-σ-algebra of the ambient measurable structure. -/
  past_le : ∀ k, pastSigma k ≤ inferInstance
  /-- The future σ-algebra is a sub-σ-algebra of the ambient measurable structure. -/
  future_le : ∀ k, futureSigma k ≤ inferInstance
```

Then in the S5c proof:
```lean
-- Sub-σ measurability of level set {X > t} from H.past_measurable + measurable_const + measurableSet_lt:
have h_sub : @MeasurableSet Ω (H.pastSigma 0) {ω | X ω > t} :=
  @measurableSet_lt Ω ℝ _ _ (H.pastSigma 0) X (fun _ => t)
    (H.past_measurable 0) measurable_const
-- Ambient measurability follows from H.past_le applied to h_sub:
have h_amb : MeasurableSet {ω | X ω > t} := H.past_le 0 _ h_sub
```

Cost: **+2 lines in the structure definition + 0 lines per call site** (the
`@[fun_prop]` tactic should auto-discharge the level-set construction once
`H.past_measurable` and `H.past_le` are in scope, but it can also be done
manually as above).

**Parent file extension.** The parent file's `AlphaMixingSequence`
(`CentralLimitTheoremOQ02.lean:427-442`) has the same gap. If S5c extends
`IbragimovHypotheses` with `past_le`/`future_le`, a parallel extension of
`AlphaMixingSequence` upstream-portable cleanup target.

**LOC impact.** S5c projected ~100 LOC (per state.md/Next iteration / PR
#19050 body). With the `past_le`/`future_le` extension, revised budget is
~100-130 LOC, of which:
- +2 LOC in `IbragimovHypotheses` (new fields).
- +0-5 LOC in `davydov_covariance_inequality` (threading `H.past_le`/`H.future_le`
  to the new bridge lemma).
- Body of S5c proof: unchanged ~95 LOC.

### Finding F — Negative result: no α-mixing primitive in Mathlib ✓ (re-pinned)

Re-pinned at lake SHA `2df2f015...` via
`gh api search/code?q=alphaMixingCoeff+OR+StronglyMixing+OR+MixingCoefficient+repo:leanprover-community/mathlib4`:
no hits. The parent file's `alphaMixingCoeff` remains the only source for
α-mixing infrastructure. This is unchanged from session 1 (S1 OBSERVE,
researcher-12, 2026-05-11) and confirms there's no upstream API change that
might displace the OQ-02-OQ-04 in-file approach.

## Race / non-overlap check

`gh pr list -R rjwalters/lean-genius --search "central-limit-theorem-oq-02-oq-04 in:title" --state open`
returns 7 open PRs as of 2026-05-15 ~08:30Z:

- **#17810** (researcher-8, conflict-frozen against post-S3 main) —
  pre-S3 stationarity/moment-bound bridge lemmas; superseded by merged S3
  content. No overlap.
- **#17826** (conflict-frozen against post-S3 main) — duplicate S3 ACT.
  No overlap.
- **#17943, #17947** (S4 prep/partial, build pending) — pre-S4-merge content;
  superseded by merged S4 (#17974) and downstream S5/S5a/S5b. No overlap.
- **#18439** (auditor drift) — superseded by merged #18440. No overlap.
- **#19030** (researcher-9, doc-only S5b build-verify, MERGEABLE) —
  retires "(build pending)" qualifier; touches `state.md`,
  `currentState.*` / `knowledge.progressSummary` JSON, and one session log.
  **No overlap with this PR** (this PR's sole new file is
  `sessions/2026-05-15-s5c-prep-sibling-audit.md`).
- **#19050** (researcher-12, S5c-prep ACT, MERGEABLE, build-verified) —
  adds proven `indicator_covariance_le_alpha`, fixes line-419 lint, updates
  JSON trackers. **No overlap with this PR** (this PR audits #19050 but
  modifies no file #19050 touches).

This PR adds a single new file under `research/problems/.../sessions/`. Strict
conflict-free against all 7 open PRs and against any subsequent S5c ACT PR.

## Sibling-worktree race check (memory's "parallel ACT race" pattern)

Per memory `feedback_researcher_parallel_worktree_act_race_check_sibling_worktrees`:

- `ps -ef | grep -E "docker-build|lean-build"` ⇒ no active Docker builds.
- `docker ps` ⇒ no running containers.
- `ls .loom/worktrees/researcher-*/proofs/Proofs/CentralLimitTheoremOQ02OQ04.lean`
  shows 5 worktrees with file size 34488 bytes, all checked out at S5b state
  (post-#18728-merge). researcher-12's mtime is the latest (2026-05-14 08:02)
  but is on branch `research/erdos-101-oq-01-s7-prep-sibling-audit-of-s6-bridge-1778832777`
  (different slug); no active edits on `CentralLimitTheoremOQ02OQ04.lean`.

No race risk for this doc-only PREP.

## Goal-state walk: how S5c proper invokes the bridge after the +5 LOC fix

To make the audit actionable, here is the goal-state at the S5c call site of
`indicator_covariance_le_alpha` after the recommended `past_le`/`future_le`
extension (Path B above):

```lean
-- Inside the proof of davydov_covariance_inequality, after level-set
-- decomposition and bilinear expansion, the inner-loop goal at (t, s) is:
-- ⊢ |∫ ω, ({X > t}).indicator 1 ω * ({Y > s}).indicator 1 ω ∂μ - ...| ≤ α₀ (or similar bound)

-- (1) Sub-σ measurability of level sets.
have hAt_sub : @MeasurableSet Ω (σPair 0) {ω | X ω > t} :=
  @measurableSet_lt Ω ℝ _ _ (σPair 0) X (fun _ => t)
    _hX_meas (@measurable_const ℝ Ω _ (σPair 0) t)
have hBs_sub : @MeasurableSet Ω (σPair 1) {ω | Y ω > s} :=
  @measurableSet_lt Ω ℝ _ _ (σPair 1) Y (fun _ => s)
    _hY_meas (@measurable_const ℝ Ω _ (σPair 1) s)

-- (2) Ambient measurability via the new past_le / future_le fields.
have hAt_amb : MeasurableSet {ω | X ω > t} := hpast_le _ hAt_sub
have hBs_amb : MeasurableSet {ω | Y ω > s} := hfut_le _ hBs_sub

-- (3) Invoke the bridge lemma.
exact indicator_covariance_le_alpha σPair hAt_amb hBs_amb hAt_sub hBs_sub
```

Notes:
- The `@measurable_const ℝ Ω _ (σPair 0) t` form is needed to specify which
  measurable space we want constants to be measurable w.r.t.; the polymorphic
  `measurable_const` lemma supports this.
- After step (2), we obtain ambient `MeasurableSet` (not just
  `NullMeasurableSet`), which is what `integral_indicator_one` (and hence
  `indicator_pair_covariance_eq` and the bridge lemma) demands.
- `Measurable.le` (line 528 of `Defs.lean`) can also be used to derive
  `Measurable X` (ambient) from `Measurable[σPair 0] X` and `H.past_le 0`,
  which is a useful side effect of the new fields.

## Counts (this PR)

- Lean lines changed: **0** (no Lean file touched).
- `state.md` lines changed: **0**.
- JSON-tracker lines changed: **0**.
- `meta.json` lines changed: **0**.
- New files: **1** (this session log, doc-only).
- Sorries delta: 0.
- Axioms delta: 0.
- Build status: N/A (no Lean change).

## Recommendations for next session(s)

### Immediate (S5c-prep refinement, optional)

If the deployer stall holds and #19050 doesn't merge promptly, the
`past_le`/`future_le` extension could be bundled into a **separate** doc-only
PREP-2 PR (just the structure-field documentation, no Lean changes) so the
S5c builder has a complete blueprint at hand. Estimated +0 LOC Lean,
~30-50 LOC markdown.

### Next iteration (S5c ACT proper)

After #19050 merges, the S5c builder should:

1. Extend `IbragimovHypotheses` with `past_le`, `future_le` fields (+2 LOC).
2. Optionally extend parent's `AlphaMixingSequence` similarly (upstream-portable).
3. Write the L^p Davydov proof using the level-set decomposition + bilinear
   expansion + `indicator_covariance_le_alpha` (now available from #19050).
4. Apply Hölder amplification with conjugate exponents `(p, p/(p-1))` to
   recover the `12 · α^{(p-2)/p} · ‖X‖_p · ‖Y‖_p` bound.
5. Apply Markov tail bound on `|X| > N`, `|Y| > M` to handle the truncation
   remainder.

Estimated S5c LOC: 100-130 (revised from #19050's ~100 projection to account
for the `past_le`/`future_le` extension and any null-measurable threading).
Reference: Doukhan 1994 §1.2.2, Bradley 2007 Vol I Thm 3.7.

### Parallel path (S6 ACT, unblocked)

S6 joint tuple stationarity (~100 LOC) is independent of S5c and the
`past_le`/`future_le` extension. Refines `Stationary μ X` (marginal-slice
identical distribution) to `JointStationary` over finite tuples, prerequisite
for Bernstein blocks. No dependency on PR #19050 or this audit. Could ship
in parallel with S5c.

## Trap notes (memory composability)

This audit composes the following memory entries:

- `feedback_researcher_sibling_prep_audits_peer_prep_workaround_finds_sharper_cancellation_path`
  (sibling-PREP audits peer's workaround) — closest precedent; this audit
  similarly examines a peer PREP's bearer chain at lake SHA, but instead of
  finding a sharper cancellation it finds a **structural gap** in the
  hypothesis bundle (different failure mode, same audit shape).
- `feedback_researcher_audit_geometric_vs_arithmetic_decomposition_disconnect`
  (audit closure plan for type-system gap) — this audit's Finding E is a
  type-system gap: sub-σ measurability vs. ambient measurability of the same
  underlying set. The fix is structural (add `≤` relation field), parallel
  to the recommended "add geometric reduction lemma" fix in that memory.
- `feedback_researcher_preflight_pin_verifies_peer_prep_skeleton`
  (pre-flight pin-verifies peer's skeleton at SHA) — applied here for all 8
  bearer-table entries; all pin-verified, no phantoms.
- `feedback_researcher_sweep_audit_pin_verify_multi_prep_chain`
  (sweep-audit pin-verify across multi-PREP chain) — applied here for the
  S4 (#17939) + S5 (#18227) + S5b (#18728) + S5c-prep (#19050) chain that
  contributes to the current S5c-prep state.

No new trap discovered. The "double-hypothesis structurally required" pattern
(Finding C) is an interesting *non-defect* finding — worth noting that not
all "looks simplifiable" hypotheses can be eliminated; the parent's choice of
arbitrary `Fin 2 → MeasurableSpace Ω` (rather than `[Sub σ-Algebra Ω]`) makes
this unavoidable at the bridge layer.

## Summary

- ✅ PR #19050's `indicator_covariance_le_alpha` is sound; 3-line proof
  type-checks at lake SHA.
- ✅ All 8 Mathlib bearers pin-verified at SHA `2df2f015...`. No phantoms.
- ✅ Line-419 simp-arg lint fix is correct.
- ⚠ **Structural gap** for S5c: `IbragimovHypotheses` needs `past_le`,
  `future_le` fields (+2 LOC) to bridge sub-σ to ambient measurability.
- ✅ Parent file `AlphaMixingSequence` has the same gap; same +2 LOC fix.
- ✅ No α-mixing primitive has appeared in Mathlib; the in-file approach
  remains the only path.
- ✅ Strict conflict-free against all 7 open PRs on the slug. No race risk
  (no active Docker builds; no sibling worktree edits to the .lean file).
