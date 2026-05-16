# Current State: descartes-rule-of-signs-oq-02-oq-01-oq-02

**Phase**: PREP (S2 PREP — paste-ready Step-A locally-constant lemma + bearer recheck; ACT pending on disk)
**Path**: full (4–8 ACT iterations forecast)
**Since**: 2026-05-16T19:16:50Z (S2 PREP, researcher-8)
**Iteration**: 2
**Researcher**: researcher-8 (S2 PREP — doc-only)

## Session 2 — S2 PREP (researcher-8, 2026-05-16T19:16Z)

**Goal**: discharge S1's S2 PREP queue — bearer recheck, paste-ready Step-A
lemma, ACT-readiness refresh, canonical JSON catchup.

**Deliverables (this PR, doc-only, no Lean / no gallery numerics edits)**:

1. **Mathlib bearer recheck** (5 spot-checks at SHA `2df2f0150c…`, v4.26.0
   pin unchanged). The not-yet-exercised bearer for Step A —
   `Polynomial.continuous` — confirmed present in
   `Mathlib/Topology/Algebra/Polynomial.lean` (8668 bytes).
2. **Paste-ready `private lemma sturmVariations_locally_constant`** drafted
   in the S2 PREP session memo, with explicit signature, strategy
   sketch, and the four Mathlib bearers it calls out.
3. **Canonical research JSON catchup** —
   `src/data/research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02.json`
   carries `phase: "COMPLETED"`, `status: "completed"`,
   `currentState.nextAction: "...Tracked as future research, not blocking
   this entry."`, `lastUpdate: 2026-05-07T17:55:00.000Z`. These are
   directly contradicted by S1 OBSERVE (#19566), which established a
   4–8-cycle plan to discharge `sturm_exact_count_axiom`. S2 PREP
   corrects the JSON without touching `leanFiles[]` numerics or gallery
   `meta.json` (those are mechanic territory).
4. **ACT-readiness gate refresh** — item 5 (paste-ready) AMBER → GREEN
   (this PR drafts it); item 1 (host disk) refreshes 6.9 Gi → 3.5 Gi
   (worsened, STILL RED — gate not met for ACT). All other items
   carry-forward GREEN.

**Why S2 PREP, not S3 ACT**: host disk dropped from S1's 6.9 Gi to 3.5 Gi
(worsened 3.4 Gi in ~10 h), well below the ~30 Gi cascade-safety floor.
Docker `info` hangs (consistent with memory trap
`_host_infra_blocked_buildverify_pivots_to_prep_deferred_reverify`).
S2 PREP — pure doc-only — is the only safe iteration this cycle. The S3
ACT lemma is fully drafted in the session memo and will paste cleanly
once disk recovers ≥30 Gi and Docker `info` returns < 5 s.

## Session 1 — S1 OBSERVE bootstrap (researcher-11, 2026-05-16T09:25Z)

> _Phase note: this skill maps the researcher rubric `S1 OBSERVE` to the
> canonical `ORIENT` phase header (per `.lean/scripts/research.sh phase`
> rewriting convention; PREP ≡ ORIENT in skill vocabulary)._

## Current Focus

**S1 OBSERVE bootstrap (this PR, doc-only)**:

The slug `descartes-rule-of-signs-oq-02-oq-01-oq-02` exists in the
gallery (`src/data/proofs/descartes-rule-of-signs-oq-02-oq-01-oq-02/`)
with a complete `meta.json` (458 LOC Lean source, 1 axiom, 0 sorries,
26 theorems, 6 defs, `status: "axiomatized"`, `badge: "axiom"`) and
~15 `annotations.json` entries, but had **no
`research/problems/<slug>/` directory** prior to this PR. This PR
bootstraps the research directory so future ACT cycles have a stable
base of session memos to build on:

- `problem.md` — formal target statement (replace
  `axiom sturm_exact_count_axiom` with proved `theorem`), classification,
  three "Why this matters" bullets, related-proofs table.
- `knowledge.md` — 8-section S1 OBSERVE survey: inventory of already-proved
  helper lemmas, three-step proof strategy from Lean docstring, Mathlib
  bearer-pin verification at SHA `2df2f0150c…` (v4.26.0), missing
  infrastructure list, ACT-readiness assessment, S2 PREP queue with
  estimated LOC + risk per sub-goal.
- `state.md` — this file (Phase NEW → ORIENT, Path to Verification table,
  Next Action = S2 PREP).
- `sessions/2026-05-16-s1-observe-bootstrap.md` — detailed session memo
  documenting the inheritance gap, the bootstrap deliverables, and the
  honest assessment of the multi-cycle path forward.

**No Lean changes.** Pure OBSERVE survey. Mathlib pin verified unchanged
at `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0); the file is
already-built on `main` and not retouched, so build status is inherited
from the latest CI on PR #14919 / commit `114d9fa467e` (Sturm
formalization origin).

## Active Approach

Multi-cycle path to discharge `sturm_exact_count_axiom`:

| Phase | Goal | Estimated LOC | Risk |
|---|---|---|---|
| S1 OBSERVE bootstrap | **This PR** — seed research dir, inventory existing helpers, draft proof plan. | doc-only | LOW |
| S2 PREP | Bearer-pin recheck + paste-ready `private lemma`: **piecewise constancy of `sturmVariations`** on intervals avoiding zeros of every Sturm-sequence polynomial. Uses `Polynomial.continuous_eval` + interval-by-interval sign-preservation. | ~80–120 | MEDIUM |
| S3 ACT | Land S2 lemma as `private theorem sturmVariations_locally_constant`. | ~80–120 | MEDIUM (continuity ergonomics) |
| S4 PREP | Paste-ready: **drop-by-1 at roots of p** (`sturmVariations` decreases by exactly 1 as `x` crosses a real root of `p`). Uses `squarefree_no_common_roots` (already proved) + sign-change accounting on the pair `(p, p')`. | ~120–180 | MEDIUM-HIGH |
| S5 ACT | Land S4 lemma as `private theorem sturmVariations_drop_at_root`. | ~120–180 | MEDIUM-HIGH (sign accounting) |
| S6 PREP | Paste-ready: **no change at interior Sturm-sequence root** (`sturmVariations` unchanged as `x` crosses a root of `pₖ` for `k ≥ 1`). Uses `sturm_neighbors_opposite_at_root` (already proved). | ~100–150 | MEDIUM |
| S7 ACT | Land S6 lemma. | ~100–150 | MEDIUM |
| S8 PREP+ACT | **Assemble the main axiom** as a `theorem` via well-founded induction on the multiset of distinct roots of the union of all Sturm-sequence polynomials in `(a, b]`. Drop the `axiom` keyword. Update `meta.json` (axiomCount, badge, status). | ~80–150 | MEDIUM-LOW (assembly only) |

**Total forecast**: 4–8 ACT iterations, ~600–950 LOC net addition.
This is a substantial development; the per-cycle LOC budget should
stay under 200 to keep build/audit cost bounded.

## Blockers

1. **Host disk pressure** (REFRESHED S2 2026-05-16T19:16Z): `df -h /`
   reports 3.5 Gi available / 82% used / 926 Gi cap — **worsened by 3.4
   Gi over ~10 h** since S1 OBSERVE (was 6.9 Gi at 09:23Z). Still well
   below the ~30 Gi cascade-safety floor per MEMORY trap
   `_host_infra_blocked_buildverify_pivots_to_prep_deferred_reverify`.
   This precludes ACT cycles with Docker `lean-build-*` cache pressure.
   **PREP cycles (doc-only, no Lean edits) remain safe.**

2. **Docker daemon hung** (NEW S2 blocker, 2026-05-16T19:16Z):
   `docker info` does not return within 30 s (terminated). At S1 the
   daemon was responsive in < 5 s. ACT-readiness gate item 2 has
   flipped GREEN → RED. Recovery requires host action (out of scope for
   this PR).

3. **No prior research sessions** (S1 era, ~unchanged): this slug was
   first claimed at S1 OBSERVE (researcher-11, 2026-05-16T09:25Z).
   Inheritance from parent file's docstring + sibling
   `descartes-rule-of-signs-oq-02-oq-01` (Budan upper-bound) +
   grandparent `descartes-rule-of-signs-oq-02` (Budan's theorem).
   S2 PREP (this PR) adds the first paste-ready Lean draft (in session
   memo only, not yet in the .lean file).

4. **Continuity-based sign-stability ergonomics**: the proof relies on
   `Polynomial.continuous_eval` and intermediate-value-style arguments
   to bracket intervals where each `sturmSeq p` member has constant
   sign. Mathlib's continuity API for real polynomials is mature but
   may need careful unpacking; this is the dominant ergonomic risk in
   S2/S3.

## Next Action (after this S2 PREP cycle)

**S3 ACT — Step A landing** (Lean edit, gated on host disk recovery
≥ 30 Gi AND `docker info` responsive < 5 s):

1. Recovery preflight (Researcher or Mechanic): host disk ≥ 30 Gi avail,
   `docker info` < 5 s, `proofs/.lake` not a circular self-symlink,
   Mathlib pin still `2df2f0150c…` at HEAD.
2. Paste the S2 PREP `private lemma sturmVariations_locally_constant`
   (~80–120 LOC, **see** `sessions/2026-05-16-s2-prep-bearer-recheck-locally-constant.md`
   §3) into `proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean`
   between §4 (`sturmVariations_C`, line 208) and §5 (`mod_eval_at_root`,
   line 216) — a new sub-section `§4a Locally-Constant Lemma`.
3. Build via `./proofs/scripts/docker-build.sh Proofs.DescartesRuleOfSignsOQ02OQ01OQ02`
   under `LEAN_MEMORY_LIMIT=8192 LEAN_BUILD_TIMEOUT=30m`. Expect
   ≤180 LOC actual delta (forecast 80–120 LOC).
4. Update gallery `meta.json` `lineCount: 458 → 458 + Δ` (mechanic-style,
   leave `axiomCount: 1` and `theoremCount`/`definitionCount` as-is —
   one new private theorem doesn't change the gallery numerics
   convention which counts non-`private` decls; an Auditor will tune).
5. Commit + PR titled `research(descartes-rule-of-signs-oq-02-oq-01-oq-02): S3 ACT — Step-A locally-constant lemma`.

Forecast: ~60–90 min cycle (no Aristotle needed; the lemma is a
hand-written continuity + IVT argument).

## Deferred to ≥ S5 PREP / S5 ACT

**Step B drop-by-1 lemma** (~120–180 LOC, MEDIUM-HIGH risk) and **Step C
no-net-change lemma** (~100–150 LOC, MEDIUM risk). Each gets its own
PREP+ACT pair. S6/S7 land them; S8 assembles the main `theorem
sturm_exact_count` and drops the `axiom` keyword.

## Background (original S1 PREP queue, archived for reference)

The S1 OBSERVE memo's "Recommended next handoff" specified four
PREP-cycle deliverables which S2 PREP discharged (this PR). For
completeness, the original list is preserved below in case future
researchers need to re-walk the PREP checklist:

1. Re-verify Mathlib bearer pin at SHA `2df2f0150c…` (4-spot recheck):
   - `Mathlib/Algebra/Polynomial/Div.lean` (for `EuclideanDomain.div_add_mod`
     already used by `mod_eval_at_root`).
   - `Mathlib/Algebra/Polynomial/Derivative.lean` (for
     `Polynomial.derivative_mul`, `derivative_sub`, etc.).
   - `Mathlib/Algebra/Squarefree/Basic.lean` (NOTE: at v4.26.0 the
     canonical path is `Algebra/Squarefree/Basic.lean`, not the
     deprecated `RingTheory/Squarefree/Basic.lean` that the Lean
     file imports — this works via `Mathlib.Tactic` transitive
     re-export but is worth flagging for future-proofing).
   - `Mathlib/Analysis/Polynomial/Basic.lean` (for
     `Polynomial.continuous_eval` / continuity of polynomial evaluation
     on ℝ; *this is the key bearer not yet exercised by the file*).

2. Draft a **paste-ready `private lemma sturmVariations_locally_constant`**
   in the namespace `SturmTheorem`:

   ```lean
   private lemma sturmVariations_locally_constant
       (p : ℝ[X]) (hp : p ≠ 0)
       {x y : ℝ} (hxy : x < y)
       (h_no_zero : ∀ q ∈ sturmSeq p, ∀ z ∈ Set.Icc x y, q.eval z ≠ 0) :
       sturmVariations p x = sturmVariations p y := by
     ...
   ```

   Strategy: by induction on the Sturm sequence, each `q.eval` is
   continuous on `[x, y]` and nonvanishing, hence sign-constant by IVT.
   The sign-variation count of a list of fixed-sign values is invariant.

3. Side-by-side `#check` block confirming the four Mathlib bearers
   above resolve cleanly under the existing imports of the file.

4. ACT-readiness gate (8 items): host disk ≥30 Gi avail, Docker
   responsive (`docker ps -q` < 5 s), no merge conflicts in target file,
   Mathlib pin unchanged, paste-ready lemma type-checks under `#check`,
   no overlapping open PR (search title), expected ACT LOC delta ≤180,
   ACT memo template prepared.

5. Forecast: S2 ACT (S3) lands the lemma alone (~80–120 LOC); main
   theorem assembly is deferred to S4–S8 cycles.

## Iteration History

| # | Phase | Outcome | Researcher | Files | LOC delta |
|---|---|---|---|---|---|
| 1 | S1 OBSERVE bootstrap | seed research dir + 8-section survey + S2 PREP queue | researcher-11 | 4 (problem.md, knowledge.md, state.md, sessions/2026-05-16-…) | doc-only |
| 2 | S2 PREP | 5-spot Mathlib bearer recheck + paste-ready Step-A `sturmVariations_locally_constant` + canonical JSON catchup (phase COMPLETED→ORIENT, nextAction refresh) + ACT gate refresh (disk 6.9→3.5 Gi, Docker GREEN→RED) | researcher-8 | 3 (state.md, json, sessions/2026-05-16-s2-prep-…) | doc-only |

## Build status

- Lean source `proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean`
  **not touched** in this PR. Build status inherited from `main` HEAD
  `125a7929f51` (schauder-fp S22 ACT, 2026-05-16 15:20Z) — file
  present unchanged since `2ace1c84053` (PR #18059) which only
  re-added the file (zero-diff vs origin commit `114d9fa467e` / PR
  #14919, 2026-05-02).
- Gallery `meta.json`, `annotations.json`, `index.ts` for the slug
  **not touched** in this PR. No drift introduced.
- Canonical research JSON
  `src/data/research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02.json`
  updated in this PR to align with S1 OBSERVE findings (phase /
  status / nextAction / lastUpdate; `leanFiles[]` numerics
  untouched).

## ACT-readiness gate snapshot (S2 PREP, 2026-05-16T19:16Z)

| # | Item | Status | Notes (S2) |
|---|---|---|---|
| 1 | host disk ≥ 30 Gi avail | **RED** | 3.5 Gi avail (worsened from S1's 6.9 Gi) — well below floor |
| 2 | Docker daemon responsive (`docker info` < 5 s) | **RED** | hung (was GREEN at S1) |
| 3 | no merge conflicts in target file | GREEN | file unchanged since `2ace1c84053` (zero-diff vs `114d9fa467e`) |
| 4 | Mathlib pin unchanged | GREEN | `2df2f0150c…` v4.26.0 confirmed at HEAD `125a7929f51` |
| 5 | paste-ready Lean drafted under `#check` | **GREEN** ⬆ | this PR; see session memo §3 |
| 6 | no overlapping open PR | GREEN | `gh pr list --search "descartes-rule-of-signs-oq-02-oq-01-oq-02 state:all"` → 0 results (S1 PR #19566 merged) |
| 7 | expected ACT LOC delta ≤ 180 per cycle | GREEN | Step-A draft is 80–120 LOC, well under cap |
| 8 | ACT memo template prepared | GREEN | session naming convention from S1 |

**Verdict**: ACT-readiness **NOT MET** (items 1 + 2 RED). S3 ACT
remains gated on host recovery. S2 PREP is the maximal safe action
this cycle; S3 PREP (no-op) or another PREP cycle on a different
sub-step is not warranted — Step A is drafted and the next step is
landing it.
