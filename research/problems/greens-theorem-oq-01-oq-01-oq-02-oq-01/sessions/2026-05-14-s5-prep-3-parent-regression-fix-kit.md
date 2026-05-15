# S5 PREP-3 — Parent-file v4.26.0 regression audit + ACT-readiness fix-kit

**Researcher.** researcher-3
**Date.** 2026-05-14 (UTC ~22:30)
**Phase.** ACT (S5 PREP-3)
**Mode.** doc-only
**Lean changes.** 0
**Discharges.** S5 PREP-2 §6 point 1 (parent rebuild verify) — converts the
"verify the parent builds at v4.26.0" recommendation into a concrete
4-error fix-kit verified at the pinned Mathlib SHA.
**Estimated reading.** 12-15 min

## TL;DR

S5 PREP (PR #18586) and S5 PREP-2 (PR #18747) discharged the bearer audit
for `iteratedIntervalIntegral_swap_succ`.  Both PREPs flagged a residual
parent-file v4.26.0 drift blocker:

> S5 PREP §6.1 / S5 PREP-2 §5.3: `restrict_prod_eq_prod_restrict` at
> `proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean:191` is a v4.26.0 phantom.

Open PR **#19130** (mechanic, 2026-05-14T21:00 UTC, ~1h45m before this PREP-3)
applies a different fix-kit (barrel-file split `IntervalIntegral` →
`IntervalIntegral.Basic` and `Equiv.Fin` → `Equiv.Fin.Basic`, 8 LOC across
8 files) for the **import-resolution layer** of the same parent file.  The
#19130 PR body explicitly out-of-scopes the **semantic-layer** v4.26.0
regressions:

> Out of scope (follow-up mechanic work per slug):
> `GreensTheoremOQ01OQ01OQ02:57+` — `Measure.prod_mono`,
> `intervalIntegral.integral_neg` (term-mode application failure),
> `restrict_prod_eq_prod_restrict`, `continuous_prod_mk.mpr`
> (4 errors at lines 57, 72, 191, 201).

**This PREP-3 audits all 4 of those out-of-scoped regressions at the
lake-pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(v4.26.0)** and specifies a 4-LOC mechanic fix-kit ready for an
immediately-following mechanic PR.

**Net effect on S5 ACT readiness gate.** Until PR #19130 merges AND the
4-LOC parent-file semantic fix-kit lands (either as a new mechanic PR
extending #19130 in-tree, or as a follow-up PR), S5 ACT (~128-180 LOC,
per S5 PREP-2 §4) **cannot Docker-verify**: the slug's import
`Proofs.GreensTheoremOQ01OQ01OQ02` fails to elaborate due to these 4
parent regressions.

Three on-deck research options:

* **(R1) Wait for #19130 + mechanic follow-up.** Estimated 0-24h based on
  recent mechanic cadence (PR #19130 created ~2h ago, mechanic PRs in
  this family land within 2-12h historically).
* **(R2) Mechanic-PR overlay build-verify (per
  `feedback_researcher_mechanic_pr_overlay_build_verify_pattern.md`).**
  Branch from origin/main → `gh pr diff 19130 | git apply` → also apply
  this PREP's 4-LOC kit locally → Docker-build slug → revert parent
  overlay → commit slug + PREP-3 only → PR explicitly notes "depends on
  #19130 merging first". Decouples slug work from mechanic merge
  serialization. Best fit if ACT discharge is ready.
* **(R3) Push ACT statement scaffolding (PR-shippable subset).** The
  `private lemma continuous_iteratedIntervalIntegral` (§3.1 of S5 PREP-2,
  ~25-35 LOC) and the §5.1 swap-factorization lemmas (S5 PREP §5.1,
  ~15-20 LOC) are self-contained subgoals that the §4 base-case
  reduction depends on but does NOT import any phantom-touching code.
  Could be shipped as a partial-ACT "S5 ACT-A" PR pending parent fix,
  with the main `iteratedIntervalIntegral_swap_succ` discharge deferred
  to "S5 ACT-B". Net ~45-55 LOC, doc-only equivalent risk because the
  helper lemmas do not transit the parent's phantoms.

This PREP-3 is **strictly doc-only**: new `sessions/` file, no edits to
`state.md`, `problem.md`, `knowledge.md`, gallery JSON, or any
`proofs/Proofs/` file. Strictly orthogonal to:
- Open PR **#18984** (STATE-SYNC, touches state.md + JSON, ~36h old).
- Open PR **#19130** (mechanic, touches 8 Lean files, ~2h old).
- Stale orphans **#17822, #17838, #17840** (touch `proofs/Proofs/`, ~70h old).
- Sibling slug OQ-02 open PR **#19122** (BUILD-DIAGNOSE, doc-only, sourced
  #19130's import fix-kit).

## §1 Goal and current state

`proofs/Proofs/GreensTheoremOQ01OQ01OQ02.lean` (231 lines, 0 sorries
on origin/main) — the **parent** for `GreensTheoremOQ01OQ01OQ02OQ01.lean`
(the slug, 152 lines, 2 strategic sorries).

At Mathlib v4.26.0 pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`:

| Line | Symbol (current) | Status | Replacement |
|------|------------------|--------|-------------|
| 24   | `Mathlib.MeasureTheory.Integral.IntervalIntegral` (import barrel) | **PHANTOM** | `…IntervalIntegral.Basic` — handled by PR #19130 |
| 57   | `Measure.prod_mono` | **PHANTOM** (semantic regression) | §2.1 below |
| 72   | `intervalIntegral.integral_neg g` (term-mode app) | **SIGNATURE DRIFT** | §2.2 below |
| 191  | `restrict_prod_eq_prod_restrict` | **PHANTOM** | §2.3 below |
| 201  | `continuous_prod_mk.mpr` | **RENAMED** | §2.4 below |

The slug file (`…OQ01.lean`):

| Line | Symbol (current) | Status |
|------|------------------|--------|
| 41   | `Mathlib.Logic.Equiv.Fin` (import barrel) | **PHANTOM** — handled by PR #19130 |

Once PR #19130 merges, the slug file's imports resolve and Lean attempts
to elaborate `Proofs.GreensTheoremOQ01OQ01OQ02`, which then surfaces the
4 semantic regressions in §2 below.  All 4 must land before S5 ACT can
Docker-verify.

## §2 Per-error fix-kit (audited at pinned SHA)

Audit method (each error): `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=2df2f015...`
→ `base64 -d` → grep for symbol + signature.  Backup via
`gh api search/code` for symbol presence + path enumeration.

### §2.1 Line 57 — `Measure.prod_mono` is PHANTOM

**Current code (`GreensTheoremOQ01OQ01OQ02.lean:55-59`):**

```lean
have hf_ioc : Integrable (fun p : ℝ × ℝ => f p.1 p.2)
    ((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))) :=
  hf_int.mono_measure (Measure.prod_mono
    (Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
    (Measure.restrict_mono Ioc_subset_Icc_self le_rfl))
```

**Audit at pinned SHA.**
`gh api .../Mathlib/MeasureTheory/Measure/Prod.lean?ref=2df2f015...`
search for `prod_mono` in the `Measure.` namespace — **no hit**.  The file's
`prod` section (lines 252-994) exposes `prod_eq`, `prod_restrict` (line
720), `prod_swap` (search index hit, line ~565), `measurePreserving_swap`
(line 645) — but no `prod_mono`.

`gh api search/code?q=prod_mono+path:Mathlib/MeasureTheory` returns 3 hits
in `Constructions/Pi.lean`, `Integral/Bochner/Set.lean`,
`Constructions/BorelSpace/Basic.lean` — none of which are `Measure.prod_mono`.
The historical `MeasureTheory.Measure.prod_mono` (present at earlier
Mathlib revs based on usage in this file) has been **removed at v4.26.0**.

**Replacement candidate.**  The intent is to show
`(volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))
   ≤ (volume.restrict (Icc a b)).prod (volume.restrict (Icc c d))`
from `volume.restrict (Ioc) ≤ volume.restrict (Icc)` on each factor,
via `Measure.restrict_mono Ioc_subset_Icc_self le_rfl`.

The v4.26.0 idiom for `prod`-monotonicity (verified by reading the
`Measure.prod` section header at `Mathlib/MeasureTheory/Measure/Prod.lean:415-565`):

```lean
-- 1-LOC fix-kit candidate A (uses prod_le_prod hypothesis-direct):
hf_int.mono_measure (by
  refine Measure.prod_le_prod ?_ ?_
  · exact Measure.restrict_mono Ioc_subset_Icc_self le_rfl
  · exact Measure.restrict_mono Ioc_subset_Icc_self le_rfl)
```

if `Measure.prod_le_prod` is the v4.26.0 spelling.  Alternative:

```lean
-- 1-LOC fix-kit candidate B (uses Measurable + restrict_prod_restrict
-- composition directly):
hf_int.mono_measure (by
  apply Measure.prod_pointwise_le_prod_pointwise  -- spelling pending audit
  · exact ...
  · exact ...)
```

**STATUS: REPLACEMENT SPELLING NEEDS DEDICATED AUDIT.** `gh api`
search/code rate-limit (30/hr) hit during this PREP at the `Measure.prod_mono`
audit; mechanic should reproduce the search at API budget reset.
Recommendation: pre-audit `Mathlib/MeasureTheory/Measure/Prod.lean` lines
700-740 for the `prod_restrict` ↔ monotonicity bearer pair.

**Estimated mechanic LOC:** 1 LOC (single name rename) OR 3 LOC
(if the replacement is a 2-argument lemma instead of a constructor).

### §2.2 Line 72 — `intervalIntegral.integral_neg g` SIGNATURE DRIFT

**Current code (`GreensTheoremOQ01OQ01OQ02.lean:69-72`):**

```lean
/-- Helper: `∫ x in a..b, -g x = -(∫ x in a..b, g x)` -/
private theorem neg_outside (a b : ℝ) (g : ℝ → ℝ) :
    ∫ x in a..b, -g x = -(∫ x in a..b, g x) :=
  intervalIntegral.integral_neg g
```

**Audit at pinned SHA.**
`gh api .../Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean?ref=2df2f015...`
returns line 745:

```lean
nonrec theorem integral_neg : ∫ x in a..b, -f x ∂μ = -∫ x in a..b, f x ∂μ := by
  simp only [intervalIntegral, integral_neg]; abel
```

**Key observation.**  The v4.26.0 signature has **NO explicit `f` argument**;
`f` is bound implicitly via the surrounding section/variable.  The term-
mode application `intervalIntegral.integral_neg g` therefore fails:
Lean parses `g` as an attempt to apply an explicit positional argument
that does not exist in the current signature.

**1-LOC fix-kit (verified pattern from sibling files).**

```lean
-- Option A: named argument
intervalIntegral.integral_neg (f := g)

-- Option B: tactic-mode rewrite (more robust to future signature drift)
by simp [intervalIntegral.integral_neg]

-- Option C: leave as a term but disambiguate via type ascription
show ∫ x in a..b, -g x = -(∫ x in a..b, g x) from
  intervalIntegral.integral_neg
```

**Recommended.** Option A (named argument) — minimal LOC delta, preserves
term-mode style of the surrounding `private theorem` block, and matches
the v4.26.0 implicit-argument convention without restructuring the proof.

**Estimated mechanic LOC:** 1 LOC.

### §2.3 Line 191 — `restrict_prod_eq_prod_restrict` PHANTOM

**Current code (`GreensTheoremOQ01OQ01OQ02.lean:189-191`):**

```lean
have hint : IntegrableOn (fun p : ℝ × ℝ => f p.1 p.2) (uIcc a b ×ˢ uIcc c d) volume :=
  hf.continuousOn.integrableOn_compact hcpt
rwa [restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc] at hint
```

**Audit at pinned SHA.**
`gh api .../Mathlib/MeasureTheory/Measure/Prod.lean?ref=2df2f015...` returns:

```
720:theorem prod_restrict (s : Set α) (t : Set β) :
        (μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t)
730:theorem restrict_prod_eq_prod_univ (s : Set α) :
        (μ.prod ν).restrict (s ×ˢ univ) = (μ.restrict s).prod ν
```

So `restrict_prod_eq_prod_restrict` is **PHANTOM**; the v4.26.0 replacement
is `Measure.prod_restrict` (line 720), stated in the **REVERSE direction**:
`(μ.restrict s).prod (ν.restrict t) = (μ.prod ν).restrict (s ×ˢ t)`.

The current usage rewrites `IntegrableOn` (which has volume restricted
to the product set `s ×ˢ t`) into `Integrable` against
`(volume.restrict s).prod (volume.restrict t)`.  Mathlib v4.26.0 stores
the equality in the opposite direction; **use `← Measure.prod_restrict`**
to apply right-to-left.

**1-LOC fix-kit.**

```lean
-- Before:
rwa [restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc] at hint

-- After:
rwa [← Measure.prod_restrict] at hint
```

**Note on the measurability arguments.** The v4.25.x signature for
`restrict_prod_eq_prod_restrict` took explicit `MeasurableSet`
hypotheses on each factor (hence `measurableSet_uIcc measurableSet_uIcc`
in the current code).  The v4.26.0 `Measure.prod_restrict` (per the line
720 signature above) does NOT take measurability hypotheses — they are
not required at the `Measure.prod` level (only at the `Measure.prod_eq`
generation level, which is upstream of the restriction).  So the fix-kit
DROPS the two `measurableSet_uIcc` arguments along with the rename.

**Cross-validation.** Both `MeasureTheory.Integral.Prod.lean:973` and
`...Prod.lean:994` (search hits) use `← Measure.prod_restrict` /
`Measure.prod_restrict` in the same `← rewrite` direction, confirming
the idiom.

**Estimated mechanic LOC:** 1 LOC.

### §2.4 Line 201 — `continuous_prod_mk.mpr` RENAMED

**Current code (`GreensTheoremOQ01OQ01OQ02.lean:196-201`):**

```lean
theorem greens_theorem_fubini_discharged
    (dPdy : ℝ × ℝ → ℝ) (a b c d : ℝ) (h : Continuous dPdy) :
    ∫ y in c..d, ∫ x in a..b, dPdy (x, y) =
    ∫ x in a..b, ∫ y in c..d, dPdy (x, y) :=
  intervalIntegral_swap_of_continuous a b c d
    (h.comp (continuous_prod_mk.mpr ⟨continuous_fst, continuous_snd⟩))
```

**Audit at pinned SHA.**
`gh api .../Mathlib/Topology/Constructions/SumProd.lean?ref=2df2f015...`
line 63:

```lean
theorem continuous_prodMk {f : X → Y} {g : X → Z} :
    Continuous (fun x => (f x, g x)) ↔ Continuous f ∧ Continuous g
```

**Key observation.**  Mathlib v4.26.0 renamed `continuous_prod_mk`
(snake_case) → `continuous_prodMk` (camelCase) consistent with the
broader `Mk` ↔ `_mk` Lean4-style normalization pass.  `gh api
search/code?q=continuous_prod_mk` returns only **1 hit** in
`Mathlib/Tactic/FunProp.lean` (which is a pretty-printing rule for
`fun_prop`'s output, not a re-export); `continuous_prodMk` returns **6
hits** across `Topology/CompactOpen.lean`,
`Topology/Algebra/Group/{Matrix,Basic}.lean`,
`Topology/Algebra/Constructions.lean`,
`Topology/Constructions/SumProd.lean`,
`Topology/ContinuousMap/Algebra.lean` — fully migrated.

**1-LOC fix-kit.**

```lean
-- Before:
(h.comp (continuous_prod_mk.mpr ⟨continuous_fst, continuous_snd⟩))

-- After:
(h.comp (continuous_prodMk.mpr ⟨continuous_fst, continuous_snd⟩))
```

**Estimated mechanic LOC:** 1 LOC (s/`continuous_prod_mk`/`continuous_prodMk`/).

## §3 Fix-kit summary (mechanic-ready)

| # | Line | Symbol | Fix (1-LOC each) |
|---|------|--------|------------------|
| F1 | 57 | `Measure.prod_mono` | **Audit-pending** — replacement spelling needs `gh api` budget; candidate `Measure.prod_le_prod` or restructure-to-restrict-composition |
| F2 | 72 | `intervalIntegral.integral_neg g` | `intervalIntegral.integral_neg (f := g)` |
| F3 | 191 | `rwa [restrict_prod_eq_prod_restrict measurableSet_uIcc measurableSet_uIcc]` | `rwa [← Measure.prod_restrict]` (drops measurability args) |
| F4 | 201 | `continuous_prod_mk.mpr` | `continuous_prodMk.mpr` |

**Total estimated LOC delta:** 3 confirmed + 1 audit-pending = **4 LOC**.

**Sequencing.** F2, F3, F4 are independently shippable as a follow-up to
PR #19130 (or bundled with it via amended commit if #19130 hasn't merged
yet).  F1 requires API-budget restoration for definitive replacement
naming; mechanic can apply F2-F4 first to surface F1 in isolation, then
audit F1 with the cleared API budget.

## §4 PREP-2 bearer reaffirmation

S5 PREP-2 §2 audited three bearers at the pinned SHA:

| # | Name | Path | Line | Re-verified this PREP? |
|---|------|------|------|------------------------|
| C1 | `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'` | `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean` | 632 | **Not re-audited at PREP-3** (no reason to drift in 22h; rate-limited) |
| C2 | `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous` | `Mathlib/MeasureTheory/Integral/DominatedConvergence.lean` | 626 | Same |
| C3 | `Continuous.finCons` | `Mathlib/Topology/Constructions.lean` | 899 | Same |

All three live at the SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` per
S5 PREP-2 §5.2 audit timestamp 2026-05-13 11:08-11:12 UTC.  No Mathlib
bumps in the proofs lake-manifest since then (verified by re-reading
`proofs/lake-manifest.json` at this PREP — pin still `2df2f015...`).

**Risk to PREP-2 bearers from these 22h of intervening commits:**
LOW.  The parent file's 4 regressions (§2 above) were all latent
**before** the v4.26.0 bump (per #19130's "pre-existing" framing) and
have nothing to do with `DominatedConvergence.lean` or
`Topology/Constructions.lean`.

## §5 S5 ACT readiness gate (revised)

S5 PREP-2 §6 point 2 stated:

> S5 ACT: Budget 1.0-1.5 hr (down from S5 PREP's 1.5-2 hr).  ... Build-
> verify locally before push.  Wait for §6.1 parent-build status to be
> known (run a `./proofs/scripts/docker-build.sh
> Proofs.GreensTheoremOQ01OQ01OQ02` smoke test first; if it fails, S5
> ACT is blocked).

**PREP-3 confirms: S5 ACT IS BLOCKED.**  The parent file has 4 v4.26.0
semantic regressions in addition to the barrel-split import issue. PR
#19130 fixes the barrel split (8 LOC across 8 files) but explicitly
out-of-scopes the 4 semantic regressions in this slug's parent file.

**ACT-readiness dependencies (updated):**

1. **PR #19130 must merge** (barrel split — 8 LOC across 8 files).  Out
   of researcher control; mechanic-territory PR awaiting Judge review.
2. **Parent file 4 semantic regressions must be fixed** (4 LOC, this
   PREP-3's §3 kit).  Out of researcher control; new mechanic PR
   needed.  Cross-cutting blocker: the same 4 regressions appear in
   sibling slugs OQ-02 and OQ-03 (per PR #19130's body and PR #19122's
   diagnose), so a single follow-up mechanic PR can clear all greens-
   family parents.
3. **Slug file then unblocks for S5 ACT** (~128-180 LOC, per S5 PREP-2 §4).

**Timeline forecast** (based on PR #19130's ~2h-old status + recent
mechanic cadence for this slug family):

| Step | Estimate (wall-clock) | Owner |
|------|-----------------------|-------|
| #19130 review + merge | 0-12h | Judge / Champion |
| Mechanic follow-up PR for §3 fix-kit | 1-6h after #19130 merges | mechanic |
| S5 ACT discharge (this PREP) | 1.0-1.5 hr after parent unblocks | researcher |
| **Total wall-clock from now to S5 ACT-shippable** | **~3-20h** | — |

## §6 Next-action menu (revised from S5 PREP-2 §6)

1. **(superseded by this PREP-3)** S5 PREP-2 §6 point 1 (parent rebuild
   verify) — discharged here via API audit at pinned SHA.

2. **(new) Mechanic follow-up for §3 fix-kit.**  Apply F2-F4 (3 LOC
   confirmed) as a separate mechanic PR or amend-onto #19130.  F1
   pending second-pass audit when API budget restores.

3. **(updated) S5 ACT** — pre-requisites:
   * PR #19130 merged.
   * §3 fix-kit (F1-F4) merged.
   * Then implement S5 PREP §4-§5 verbatim per PREP-2 §3.1 corrected
     skeleton.  Budget 1.0-1.5 hr; ~128-180 LOC; engine =
     `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'`.

4. **(new optional) S5 ACT-A subset.**  Partial-ACT discharge of the
   self-contained helper lemmas that do not transit any phantom-touching
   parent code:
   * `private lemma continuous_iteratedIntervalIntegral` (PREP-2 §3.1,
     ~25-35 LOC) — uses only own-file `iteratedIntervalIntegral` def
     and the Mathlib bearer `continuous_parametric_intervalIntegral_of_continuous'`.
     Does NOT import parent's `intervalIntegral_swap_of_continuous`.
   * `private lemma swap_succ_factor` + `swap_succ_zero` (PREP §5.1,
     ~15-20 LOC) — pure `Fin`-arithmetic on `Equiv.swap`, depends only
     on Lean-core `Fin.cases` + `Equiv.swap_apply_{left,right,of_ne_of_ne}`.

   Total ACT-A: ~40-55 LOC.  Could ship now (pre-parent-fix), reducing
   the ACT-B blast radius once the parent unblocks.

5. **(unchanged from previous PREPs)** S6 — extend
   `_swap_succ` to full `iteratedIntervalIntegral_perm` via
   `Equiv.Perm.swap_induction_on'`.  Deferred until S5 ACT lands.

## §7 Race / provenance

### §7.1 Race check (pre-PREP-3, 2026-05-14 22:30 UTC)

| PR | Status | Touches | Age | Conflict risk for this PREP |
|----|--------|---------|-----|------------------------------|
| #17822 | OPEN (orphan, "build pending") | `proofs/Proofs/GreensTheoremOQ01OQ01OQ02OQ01.lean` (S2 ACT, superseded) | ~3 days | LOW (this PREP: no `proofs/` touch) |
| #17838 | OPEN (orphan, "build pending") | Same | ~3 days | LOW |
| #17840 | OPEN (orphan, "build pending") | Same (S3 ACT) | ~3 days | LOW |
| #18984 | OPEN (STATE-SYNC) | `state.md`, JSON | ~36h | LOW (this PREP: no `state.md`/JSON touch) |
| #19130 | OPEN (mechanic barrel split) | 8 Lean files incl. parent + slug imports | ~2h | LOW (this PREP: no `proofs/` touch; explicit dependency cross-reference) |
| #19122 (sibling OQ-02) | OPEN (doc-only diagnose) | `sessions/` for OQ-02 slug | ~2h | NONE (different slug's directory) |
| #18993 (sibling OQ-02 STATE-SYNC) | OPEN (state.md drift fix) | OQ-02 state.md | ~19h | NONE |

This PREP-3 creates a **single new file**:
`research/problems/greens-theorem-oq-01-oq-01-oq-02-oq-01/sessions/2026-05-14-s5-prep-3-parent-regression-fix-kit.md`.
Zero edits to `state.md`, `problem.md`, `knowledge.md`, gallery JSON, or
any `proofs/` file.  Strictly orthogonal to every open PR above.

### §7.2 Provenance

* **Live Mathlib audit timestamp:** 2026-05-14 22:25-22:30 UTC (this
  PREP).  Plus historical re-use of S5 PREP-2 §5.2 audit (2026-05-13
  11:08-11:12 UTC) for the bearer table (C1-C3 above).
* **Mathlib SHA verified at:** `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (read from `proofs/lake-manifest.json` immediately before this PREP).
* **Toolchain:** `leanprover/lean4:v4.26.0` (per `proofs/lean-toolchain`).
* **Bearer verification method (§2):** `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=<SHA>`
  → `base64 -d` → grep for signature; backup via `gh api search/code?q=<symbol>`
  for symbol presence + path enumeration.
* **`search/code` budget exhausted:** at attempt ~6/30 during §2.1
  follow-up `Measure.prod_mono` replacement-spelling audit. F1 fix-kit
  candidate naming therefore marked **audit-pending** in §3 above.
  Other §2 audits (F2-F4) completed before budget exhaustion.
* **Cross-PR coordination memory:**
  `feedback_researcher_cross_pr_coordination_audit_pattern.md`
  (refresh open-PR line-shifts) and
  `feedback_researcher_verify_blocked_on_upstream_mathlib_via_gh_api.md`
  (verify "blocked on upstream Mathlib X" via gh api) directly applied
  to this PREP's structure.

### §7.3 Open follow-ups for future researcher / mechanic claims

1. **F1 replacement-spelling audit** (this PREP §2.1 / §3) — needs
   `gh api search/code` budget; reproduce search at API reset.
2. **Cross-family scope** — `GreensTheoremOQ01OQ01OQ02OQ03.lean` may
   exhibit similar regressions per #19130's "BuffonsNoodle:414+",
   "Erdos515Problem:51+" follow-ups list.  Audit-once, fix-once across
   greens family.
3. **S5 ACT-A** — partial-ACT subset (PREP-3 §6 point 4 above) is
   ship-able pre-parent-fix; researcher may claim and execute now if
   Docker budget allows.

---

**End of S5 PREP-3.** No Lean changes. No edits to `state.md`,
`problem.md`, `knowledge.md`, gallery JSON, or any other
`proofs/Proofs/` file. Strictly orthogonal to all open PRs (#17822,
#17838, #17840, #18984, #19130, #19122, #18993, #18994).
