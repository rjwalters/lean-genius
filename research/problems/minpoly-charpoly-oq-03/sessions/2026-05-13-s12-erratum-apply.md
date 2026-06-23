# S12 ERRATUM-APPLY — propagate S11 PREP §8 corrections (doc-only)

**Date**: 2026-05-13
**Agent**: researcher-9
**Mode**: ERRATUM-APPLY (doc-only audit-trail propagation)
**Slug**: `minpoly-charpoly-oq-03`
**Parent PREP**: PR #18668 (S11, researcher-11, merged 07:58 UTC)
**Phase**: post-S10 OQ-03-OQ-01 critical-path closure + pre-OQ-03-OQ-02-ACT
preparation; sub-OQ OQ-03-OQ-02 remains the sole substantive Mathlib
gap.

## 1. Headline finding (no new mathematics)

The S11 PREP audit identified four documents in this slug carrying a
**load-bearing wrong claim** about the Mathlib API surface:

> Apply `Module.equiv_directSum_of_isTorsion` to obtain the
> invariant-factor decomposition with **divisibility chain
> `p₁ ∣ p₂ ∣ ⋯ ∣ pₖ`**.

The Mathlib lemma at `Mathlib/Algebra/Module/PID.lean:233` (v4.26.0,
pinned at `2df2f0150c27`) instead yields the **primary cyclic
decomposition** `⨁ᵢ R ⧸ R ∙ pᵢ^{eᵢ}` with `Irreducible (pᵢ)`. Each
summand is a prime power; the summands have no a-priori divisibility
relation. The bridge from primary form to invariant-factor form is a
~290-LOC bookkeeping pass over `Multiset`/`Finset`/`List`, **not
provided by Mathlib v4.26.0**.

S11 PREP flagged the corrections but explicitly did NOT apply them
(§8 second paragraph: "This PR does NOT apply the corrections — it
merely flags them so the next implementer can fold them in without
re-discovering the issue."). This S12 session is that follow-up
application.

## 2. Why apply now, separately from the regrouping ACT

S11 PREP's cheat-sheet (§10 step 5) recommends bundling the erratum
corrections with the eventual regrouping ACT PR:

> Apply the §8 erratum corrections to the source-file docstring,
> state.md, and `src/data/research/problems/minpoly-charpoly-oq-03.json`
> in the same PR. Bundling them with the regrouping ACT keeps the
> audit trail aligned.

We **deviate from this recommendation** here, for three reasons:

1. **Wrong claims are currently live on `main`.** Until the regrouping
   ACT lands, any agent claiming this slug (or any of its sub-slugs)
   reads `knowledge.insights[0]` declaring "no genuine Mathlib gap"
   and may attempt OQ-03-OQ-02 SCAFFOLD on the wrong premise (~300
   LOC misallocated before discovering the gap mid-flight). The cost
   of leaving the erratum live grows with each new agent rotation.

2. **The regrouping ACT is high-risk and not blocking the
   correction.** Per slug memory (`feedback_researcher_lake_symlink_loop_and_wipe`),
   `proofs/.lake` symlink loops + daemon mid-build wipes have already
   bitten this codebase, and the ~340 LOC regrouping ACT
   would land as build-pending (~45 min Docker cold). The erratum
   corrections are zero-LOC of Lean and zero risk to the existing
   sorry-free helpers in `MinpolyCharpolyOQ03.lean`.

3. **Standalone erratum-apply PR is cleaner to review.** A reviewer
   can audit the four corrected texts side-by-side with the S11 PREP
   §8 proposed text without parsing 340 LOC of regrouping
   bookkeeping. The regrouping ACT can then ship without the doc
   churn entangled in its diff.

## 3. Files this PR touches

* `proofs/Proofs/MinpolyCharpolyOQ03.lean` (parent Lean file)
  **docstring only** — lines ~36-100. No Lean tactic, theorem, def,
  axiom, or `import` is touched; the `1 by sorry` count is
  unchanged at 1 (the unchanged S1 placeholder on
  `rational_canonical_form_exists`).
* `research/problems/minpoly-charpoly-oq-03/state.md` — phase line,
  "Active Approach" section, "Next Action" section, "Attempt Counts"
  section, and a new S11 + S12 session-log bullet pair.
* `src/data/research/problems/minpoly-charpoly-oq-03.json` —
  `knowledge.progressSummary`, `knowledge.insights[0]`,
  `knowledge.mathlibGaps`, `knowledge.nextSteps`,
  `currentState.focus`, `currentState.iteration`,
  `currentState.attemptCounts`, `currentState.nextAction`,
  `lastUpdate`.
* `research/problems/minpoly-charpoly-oq-03/sessions/2026-05-13-s12-erratum-apply.md`
  (this file, new).

## 4. Files this PR does NOT touch

* `proofs/Proofs/MinpolyCharpolyOQ03.lean` definitions, theorems,
  proofs — only the docstring.
* `proofs/Proofs/MinpolyCharpolyOQ03OQ01.lean` (child Lean file) —
  the OQ-03-OQ-02 ACT's territory.
* No new file `proofs/Proofs/MinpolyCharpolyOQ03OQ02.lean` — the
  Route B regrouping algorithm is S13+ ACT material.
* `src/data/proofs/minpoly-charpoly-oq-03/*` — gallery surface
  unchanged. (The gallery does not currently re-state the
  primary-vs-invariant distinction in user-facing prose.)
* meta.json drift — irrelevant; no Lean code changes.
* `problem.md` — does not re-state the strategy at the level of
  detail affected by the erratum.

## 5. Race-context (why doc-only is safe now)

`gh pr list --search "minpoly-charpoly-oq-03 in:title" --state open`
at session start (11:07 UTC, 2026-05-13) returns **0 open PRs**.

Most recent merges on the `minpoly-charpoly-oq-03` parent + its
sub-slugs:

| PR | Time (UTC) | Title (abbrev) |
|----|-----------|----------------|
| #18668 | 07:58 | S11 PREP — OQ-03-OQ-02 elementary-divisors erratum + Route B (doc-only) |
| #18592 | 05:15 | audit drift-sync after S10 (2→1 sorries) |
| #18583 | 05:00 | S10 ACT — discharge xModule_isTorsion |
| #18520 | 03:16 | S9 PREP — xModule_isTorsion cheatsheet |
| #18516 | 03:14 | audit drift-sync after S8 (3→2 sorries) |

The last merge is **>3h old**, well past the ~2-min race window
documented in memory `feedback_mechanic_race_quadruple_slot_collision`.

This S12 PR diff is on a different filename plane from any of the
above PRs (parent docstring + state.md + knowledge JSON; nobody's
sorry counts move). No race expected.

## 6. Erratum corrections applied — diff summary

### 6.1 `proofs/Proofs/MinpolyCharpolyOQ03.lean`

Two block changes:

* **Strategy section "2. Structure theorem for finitely generated
  modules over a PID (Mathlib)"** (lines ~36-65). Replaced the
  wrong "splits as `K^n ≅ ⊕ F[X]/(pᵢ)` with divisibility chain
  `p₁ ∣ ⋯ ∣ pₖ`" with the correct "splits as primary cyclic
  decomposition `⊕ F[X]/(pᵢ^{eᵢ})` with `pᵢ` irreducible; a
  ~290-LOC regrouping bookkeeping pass (sub-OQ OQ-03-OQ-02, S11
  PREP §6) converts to invariant-factor form `⊕ F[X]/(dⱼ)` with
  divisibility chain `d₁ ∣ ⋯ ∣ dₖ`." Added a forward-reference to
  the S11 PREP session-note for the audit details.

* **Bullet 3 "Cyclic summand ↔ companion block"** (~lines 66-71).
  Renamed `pᵢ` → `dⱼ` to match the corrected post-regrouping
  invariant-factor notation; the cyclic-summand bookkeeping is
  unchanged.

* **Closing sentence "No genuine Mathlib gap or axiomatic
  assumption is required"** (~lines 73-74) replaced with a
  paragraph stating "Exactly one genuine Mathlib gap: the
  elementary-divisors → invariant-factors regrouping algorithm
  (~290 LOC)" + a footnote on the alternative `Submodule.smithNormalForm`
  Route A and its own divisibility-chain gap.

* **Sub-OQ table row for OQ-03-OQ-02** (~lines 83-95). Description
  changed from "Apply `Module.equiv_directSum_of_isTorsion` to get
  the invariant-factor decomposition with divisibility chain" to
  "Apply `Module.equiv_directSum_of_isTorsion` (primary form) then
  regroup elementary divisors into invariant factors. The
  regrouping is the substantive Mathlib gap (~290 LOC bookkeeping
  + ~50 LOC API plumbing ≈ 340 LOC; see S11 PREP §6 for full
  skeleton)." Budget cell updated from `~300` to `~340`. Total
  roadmap closing sentence updated from "≈ 900 lines" to "≈ 940
  lines" with the same SNF-route-comparison footnote.

### 6.2 `research/problems/minpoly-charpoly-oq-03/state.md`

* Phase line updated to reflect post-S10 critical-path closure +
  S11 PREP audit propagation + S12 ERRATUM-APPLY iteration.
* "Active Approach" section: bullet 2 in the three-ingredient plan
  expanded to include the regrouping requirement; sub-OQ list
  bullet for OQ-03-OQ-02 updated with the ~340 LOC budget and a
  forward-reference to S11 PREP §6.
* "Next Action" section: enumeration revised to exactly four
  options (was previously enumerated for post-S5 next step, now
  re-anchored for post-S10 + post-S11-PREP next step). New strong
  recommendation: option 1 (regrouping ACT) → option 3
  (statement-only upgrade) → option 2 (`lastFactor = minpoly`
  proof).
* "Attempt Counts" updated 5 → 12 (total + currentApproach).
* "Session Log" extended with S11 PREP and S12 ERRATUM-APPLY
  entries (~30 LOC each).

### 6.3 `src/data/research/problems/minpoly-charpoly-oq-03.json`

* `knowledge.progressSummary` rewritten to summarise this S12
  ERRATUM-APPLY pass + the substantive S11 PREP correction.
* `knowledge.insights[0]` corrected from "No genuine Mathlib gap"
  to "One substantive Mathlib gap (regrouping algorithm,
  ~290 LOC, upstreamable)" + the revised roadmap budget.
* `knowledge.mathlibGaps` array expanded from 2 entries to 3:
  the original `Module.equiv_directSum_of_isTorsion` confirmation
  entry, a new explicit "elementary-divisors → invariant-factors
  regrouping" gap entry citing S11 PREP §5/§6, and a new
  `Submodule.smithNormalForm divisibility chain` entry covering
  the alternative-route gap.
* `knowledge.nextSteps` rewritten as a 6-entry list ordered by
  the recommended sequence (regrouping ACT first; statement-only
  upgrade; `lastFactor = minpoly` proof; signature re-audit;
  upstream contribution opportunity; build-verification note).
* `currentState.{phase,since,iteration,focus,attemptCounts.total,attemptCounts.currentApproach,nextAction}`
  all updated.
* `lastUpdate` bumped to `2026-05-13T11:00:00Z`.

## 7. What is NOT in this PR

* **No new Lean code.** The 1 sorry in `MinpolyCharpolyOQ03.lean`
  remains exactly where it was; the 1 sorry in
  `MinpolyCharpolyOQ03OQ01.lean` (post-S10) remains exactly where
  it was.
* **No new theorems, definitions, or axioms.** Theorem/def/axiom
  counts unchanged on all files.
* **No build verification needed.** Docstrings and JSON do not
  require Docker compilation. The status quo for the file's
  build-pending state from S4/S5 is unaffected.
* **No mechanic-style drift-sync.** meta.json is not touched (no
  Lean code changes; no `lineCount`/`sorryCount`/`theoremCount`
  drift).
* **No regrouping algorithm implementation.** That remains the
  next ACT iteration's deliverable, per the revised "Next Action"
  enumeration option 1.
* **No strong-form statement upgrade.** Per the revised "Next
  Action" enumeration, the `c.lastFactor = M.minpoly` upgrade
  belongs to option 3, ideally after option 1's regrouping work
  produces an actual chain to consume.

## 8. Verification — every corrected text matches S11 PREP §8

For audit:

| S11 PREP §8 sub-section | Target file | Match status |
|--|--|--|
| §8.1 source-file docstring lines ~36-50 | `proofs/Proofs/MinpolyCharpolyOQ03.lean` strategy bullet 2 | Applied: paragraph rewritten + S11 PREP forward-reference added |
| §8.2 state.md "Active Approach" bullet 2 | `state.md` lines 91-99 | Applied: expanded to mention regrouping requirement explicitly |
| §8.3 knowledge.insights[0] | `*.json` line ~63 | Applied: verbatim text from §8.3 with minor reflow |
| §8.4 knowledge.mathlibGaps | `*.json` lines ~74-77 | Applied: 2 entries → 3 entries (added regrouping + SNF-chain gaps; confirmed equiv_directSum signature entry retained but reworded) |
| §8.5 currentState.nextAction option 3 | `*.json` `currentState.nextAction` | Applied: enumeration restructured to 4 post-S10/post-S11 options; old option 3 replaced by new option 1 (OQ-03-OQ-02 ACT Route B) with the ~340-LOC budget. |

## 9. Honesty assessment

**What this PR delivers:**

- Four wrong claims about Mathlib API surface and gap structure are
  no longer live on `main`.
- The next agent claiming this slug will read the corrected
  `knowledge.insights[0]`, `knowledge.mathlibGaps`, and
  `currentState.nextAction` and route to the genuine substantive
  work (OQ-03-OQ-02 ACT Route B regrouping) without re-deriving
  the audit-correction.
- The S11 PREP session-note (PR #18668) is now cross-referenced
  from the parent Lean file's docstring; readers landing on the
  Lean file will find the audit details.

**What this PR does NOT deliver:**

- No new mathematics. The headline correction comes from S11 PREP
  PR #18668, which performed the actual Mathlib API audit.
- No new proofs or sorry discharges.
- No regrouping algorithm. The substantive Mathlib gap remains a
  gap until OQ-03-OQ-02 ACT lands.
- No `c.lastFactor = M.minpoly` follow-up. That is an independent
  ~15-30 LOC ACT for a later session.

**Significance assessment.** Low-to-medium impact. The S12 ERRATUM-
APPLY is **strictly audit-trail propagation** — its mathematical
content is zero, and its operational value is bounded by the
probability that a future agent reads the corrected text instead
of independently re-discovering the gap. Given the slug's recent
session cadence (~one PR every 1-3 hours over the past 24 hours,
across S1-S11) and the proximity of the next OQ-03-OQ-02 ACT
attempt, the operational value is meaningful but not large. The
PR is honest about its scope: it does not claim novelty, only
audit-trail hygiene.

**No fabricated value.** Every claim in §6 corresponds to a text
edit that can be diff-inspected; every claim in §8 corresponds to
a §8.x sub-section of the S11 PREP session-note (`research/problems/
minpoly-charpoly-oq-03/sessions/2026-05-13-s11-prep-oq03-oq02-elementary-divisors-erratum.md`).
The Mathlib v4.26.0 API references re-cited here (`Mathlib/Algebra/
Module/PID.lean:233`, `Mathlib/LinearAlgebra/FreeModule/PID.lean:541`,
`Mathlib/Algebra/Polynomial/Module/AEval.lean:124`) were verified
in S11 PREP via `gh api repos/leanprover-community/mathlib4/contents/
<path>?ref=v4.26.0` — this PR does not independently re-verify them
because they are quoted from a recently-merged session-note rather
than first-derived.
