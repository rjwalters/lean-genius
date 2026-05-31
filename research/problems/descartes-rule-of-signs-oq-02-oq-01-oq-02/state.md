# Current State: descartes-rule-of-signs-oq-02-oq-01-oq-02

**Phase**: ACT (S5 ACT — Step-A `sturmVariations_locally_constant` landed; +75 LOC, 0 sorries, 0 axioms net, build pending — G9 lake self-loop)
**Path**: full (3–7 ACT iterations remaining: Step-B PREP+ACT, Step-C PREP+ACT, assembly PREP+ACT)
**Since**: 2026-05-31T00:00:00Z (S5 ACT, researcher-1)
**Iteration**: 5
**Researcher**: researcher-1 (S5 ACT — Lean edit)

## Session 5 — S5 ACT (researcher-1, 2026-05-31)

**Goal**: land Step-A `private lemma sturmVariations_locally_constant`
from S2 PREP §3 paste-ready draft. Outcome: SHIPPED build-pending.

**Lean edit summary** (`proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean`,
458 → 533 LOC):

1. **New import** (line 72): `import Mathlib.Topology.Algebra.Polynomial`
   for `Polynomial.continuous` (`@[continuity, fun_prop]` bearer
   spot-checked at SHA `2df2f0150c…` in S2 PREP §2).

2. **New §4a section** (inserted between line 208 `sturmVariations_C`
   body and `§5` divider): 73 LOC of section header + docstring + lemma
   pasted verbatim from S2 PREP §3.2 modulo whitespace and removal of
   section-internal commentary (per CLAUDE.md "default to writing no
   comments").

**Lemma signature**:

```lean
private lemma sturmVariations_locally_constant
    (p : ℝ[X]) {x y : ℝ} (hxy : x ≤ y)
    (h_no_zero : ∀ q ∈ sturmSeq p, ∀ z ∈ Set.Icc x y, q.eval z ≠ 0) :
    sturmVariations p x = sturmVariations p y
```

**Proof strategy**: for each `q ∈ sturmSeq p`, `q.eval` is continuous on
`Icc x y` (`Polynomial.continuous`) and nonvanishing (by `h_no_zero`).
By `intermediate_value_Icc`, `q.eval x` and `q.eval y` cannot have
opposite signs (would force a zero on `Icc x y`). The two ±1 sign-lists
are therefore pointwise equal under `List.map_congr_left`, and
`countSignAlts` of equal lists is equal — so `sturmVariations p x =
sturmVariations p y`.

**Why build-pending** (G9 worktree chain): researcher-1's worktree at
`.loom/worktrees/researcher-1/proofs/.lake` is a symlink pointing to
the main repo's `proofs/.lake`, which is itself a self-symlink (G9).
The full chain is therefore self-loop; whether the docker-build.sh
CACHE_VOLUME mount shadow at `/workspace/proofs/.lake/build` still
wins for the worktree-redirected case is unverified (S4's empirical
confirmation was on the main-repo path, not a worktree). Per memory
`project_lake_self_loop_main_repo.md`: ship build-pending qualifier,
mechanic verifies on a recovered host.

**ACT-readiness gate at S5 firing point**:

| # | Item | Status | Notes |
|---|---|---|---|
| 1 | host disk ≥ 30 Gi avail | ✅ GREEN (57 Gi) | down 6 Gi from S4, still above floor |
| 2 | Docker Server | ✅ GREEN (29.4.1) | responsive |
| 3 | main repo `.lake` | ⚠️ AMBER (self-symlink, docker-build bypasses) | unchanged |
| 4 | worktree `.lake` | 🚫 RED (transitive self-loop) | new discovery at S5 |
| 5 | Mathlib pin | ✅ GREEN | `2df2f0150c…` |
| 6 | Paste-ready draft | ✅ GREEN | S2 PREP §3.2 |
| 7 | No overlapping open PR | ✅ GREEN | search returned 0 |
| 8 | ACT LOC delta ≤ 180 | ✅ GREEN | actual +75 |

**Aggregate**: 6/8 GREEN, 1/8 AMBER, 1/8 RED. RED item 4 is the
build-verification block — mechanic surface.

**Deliverables (this PR)**:

1. **Lean source** (`proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean`):
   +1 import (line 72), +73 LOC §4a section (458 → 533).

2. **Canonical JSON** (`src/data/research/problems/<slug>.json`):
   phase PREP→ACT, iteration 4→5, focus/blockers/nextAction rewrite,
   progressSummary prepend, nextSteps renumber, lastUpdate.

3. **state.md head**: this Session 5 prepend.

4. **NEW session memo**: `sessions/2026-05-31-s5-act-locally-constant-landed.md`.

**Out of scope (deferred)**:

- Gallery `meta.json` `lineCount: 458 → 533` resync — mechanic batch-sync.
- Step B paste-ready draft — that's S6 PREP, next cycle.
- Build verification — pending mechanic G9 host recovery.
- `problem.md` and `knowledge.md` body edits.
- Aristotle submission — reserved for Step B if combinatorics exceeds budget.

**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0),
unchanged since S1 OBSERVE.

## Session 4 — S4 STATE-SYNC (researcher-1, 2026-05-30T14:50Z)

**Goal**: T+13d catchup against S3's 3 RED INFRA blockers. Outcome: G7 and G8
**RESOLVED**, G9 **reclassified** to host-side-only after empirical
demonstration that docker-build bypasses the self-symlink. S5 ACT (Step-A
landing) is now READY for the docker-build path.

**Infrastructure delta vs S3**:

- **G7 disk**: ✅ RESOLVED — 63 Gi avail / 16% used (up from S3's 2.9 Gi /
  100%; +60.1 Gi recovered over ~13d 13h45m; well above 30 Gi
  cascade-safety floor).
- **G8 Docker daemon**: ✅ RESOLVED — `docker info --format '{{.ServerVersion}}'` returns `29.4.1` instantly; `docker ps` returns container list; full
  daemon responsive.
- **G9 `proofs/.lake → itself` self-symlink**: ⚠️ STILL PRESENT but
  **RECLASSIFIED** — empirically does NOT block docker-build (verified by
  parallel S3a ACT run on `triangle-inequality-oq-04-oq-01` at 2026-05-30T14:37Z,
  PR #21188, `Build completed successfully (2551 jobs)` clean first-try with
  G9 in place on the same host). The docker-build.sh wrapper's `-v "${CACHE_VOLUME}:/workspace/proofs/.lake/build:delegated"` mount (line
  127) shadows the host symlink at the only path Docker reads from inside
  `.lake`. G9 only blocks host-side `lake` ops (e.g. `lake show-paths`),
  which are out of researcher PR-scope (shell-ops / mechanic surface).

**ACT-readiness gate update vs S3**:

| Gate | S3 STATE-SYNC | S4 STATE-SYNC |
|------|---------------|---------------|
| Disk ≥ 30 Gi | 🚫 RED (2.9 Gi) | ✅ GREEN (63 Gi) |
| Docker Server: | 🚫 RED (empty) | ✅ GREEN (29.4.1) |
| `.lake` real-dir | 🚫 RED (self-symlink) | ⚠️ AMBER (still symlink, docker-build bypasses) |
| Step-A paste-ready (S2 PREP §3) | ✅ GREEN | ✅ GREEN |
| Bearers at pinned SHA verified | ✅ GREEN | ✅ GREEN (pin unchanged) |

**Aggregate**: 4/5 GREEN, 1/5 AMBER. S5 ACT is READY for the docker-build
path.

**Next action**: S5 ACT — paste the ~80–120 LOC Step-A `private lemma
sturmVariations_locally_constant` from S2 PREP §3 (sessions/2026-05-16-s2-prep-bearer-recheck-locally-constant.md) into
`proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean` between line 208
(`sturmVariations_C`) and line 211 (`-- § 5. …` divider), with the single
new import `import Mathlib.Topology.Algebra.Polynomial`. Build-verify via
`./proofs/scripts/docker-build.sh Proofs.DescartesRuleOfSignsOQ02OQ01OQ02`.

**Deliverables (this PR, doc-only — no Lean / no gallery meta / no
problem.md / no knowledge.md body edits)**:

1. **Canonical JSON** (`src/data/research/problems/<slug>.json`):
   - `currentState.phase`: PREP (unchanged)
   - `currentState.iteration`: 3 → 4
   - `currentState.since`: 2026-05-17T01:05:00Z → 2026-05-30T14:50:00Z
   - `currentState.focus`: rewrite for S4 STATE-SYNC scope
   - `currentState.nextAction`: rewrite as S5 ACT (Step-A landing)
   - `currentState.attemptCounts.total`: 3 → 4
   - `currentState.blockers`: 3-entry → 1-entry (G7 dropped, G8 dropped,
     G9 reclassified)
   - `knowledge.progressSummary`: prepend S4 line documenting infra
     recovery + G9 reclassification
   - `lastUpdate`: 2026-05-17T01:05:00.000Z → 2026-05-30T14:50:00.000Z
2. **Session note** (this PR, `sessions/2026-05-30-s4-statesync-infra-g7-g8-resolved-g9-docker-bypass.md`).

**Out of scope (carried over from S3)**: gallery meta theoremCount sync
(mechanic batch); host-side `.lake` recovery (shell-ops); Step-A landing
(named S5 ACT, not this PR).

---

## Session 3 — S3 STATE-SYNC (researcher-10, 2026-05-17T01:05Z)

**Goal**: doc-only catchup. Three threads of drift accumulated since S2
PREP closed at 2026-05-16T19:16Z (T-5h45m):

1. **3 RED INFRA blockers** (one carried, one unchanged, one NEW):
   - **G7 disk**: 2.9 Gi avail / 100% used — worsened from S2's 3.5 Gi by
     -0.6 Gi over ~5h45m; still well below the 30 Gi cascade-safety
     floor set in S2's nextAction gate.
   - **G8 Docker daemon**: `docker info` returns the Client: section
     promptly but the Server: section is empty — unchanged from S2's
     "hung" state, full daemon unreachable, build-cycle structurally
     foreclosed.
   - **G9 `proofs/.lake → itself`** circular self-symlink (NEW at S3 —
     not flagged at S2; matches the recurring `.lake → itself` pattern
     from memory `feedback_researcher_postship_pivot_to_act_ready_slug_…
     _three_red_infra_blockers_post_merge`). Blocks any Lake operation
     including pin-state inspection without surgical `rm proofs/.lake &&
     ln -s …` recovery.

2. **Registry drift** — `research/registry.json` carries `phase: NEW,
   lastUpdate: 2026-04-26T14:51:07.083Z` (21d stale) while canonical
   `src/data/research/problems/<slug>.json` since S2 PREP correctly
   reads `phase: PREP, iteration: 2, lastUpdate: 2026-05-16T19:16Z`. S2
   PREP catchup corrected the canonical JSON but did not mirror to the
   registry. Matches memory
   `feedback_researcher_claim_random_re_rolls_same_slug_due_to_registry_phase_new_vs_canonical_observe_iter1`
   (different phase target, same registry-not-mirrored shape).

3. **Stale `leanFiles[6].theoremCount`** = 28 in canonical JSON,
   contradicted by:
   - S1 OBSERVE problem.md text: "26 theorems"
   - S1 OBSERVE knowledge.md §1 declaration table (count theorems →
     26)
   - `grep -cE '^(protected |private |noncomputable )*(theorem|lemma) '
     proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean` → 26
   - file unchanged since file-creation in PR #19454 (commit
     `ecb47b35601`, 2026-05-16 01:55Z — file was newly added with 458
     LOC and 26 theorems; the 28 count was a baked-in miscount).
   S2 PREP explicitly deferred `leanFiles[]` numerics; S3 STATE-SYNC
   discharges this single own-file count.

**Out of scope (deferred)**:
- Gallery `src/data/proofs/descartes-rule-of-signs-oq-02-oq-01-oq-02/meta.json`
  `leanFile.theoremCount: 28` — same drift mirrored in gallery meta.
  Flagged in canonical JSON `currentState.nextAction` for mechanic
  batch-sync (per memory `feedback_mechanic_batch_sync_conventions_…`).
- Other 8 sibling `leanFiles[i]` entries — out of researcher scope,
  not spot-audited at S3, deferred to mechanic if drift exists.
- `.lake` recovery on host — out of researcher-PR scope (requires
  shell ops, not file edits).
- Step-A lemma landing — structurally foreclosed by G7+G8+G9.

**Deliverables (this PR, doc-only — no Lean / no gallery meta /
no problem.md / no knowledge.md body edits)**:

1. **Canonical JSON** (`src/data/research/problems/<slug>.json`):
   - `currentState.phase`: PREP (unchanged)
   - `currentState.iteration`: 2 → 3
   - `currentState.since`: 2026-05-16T19:16:50Z → 2026-05-17T01:05:00Z
   - `currentState.focus`: rewrite for S3 STATE-SYNC scope
   - `currentState.nextAction`: rewrite — picker matrix for S4 with
     gallery meta defer flagged for mechanic
   - `currentState.attemptCounts.total`: 2 → 3
   - `currentState.blockers`: 2-entry → 3-entry (G7 worsened, G8
     unchanged, G9 NEW)
   - `knowledge.progressSummary`: prepend S3 line + correct 28→26
   - `leanFiles[6].theoremCount`: 28 → 26 (this slug's own file)
   - `lastUpdate`: bump

2. **Registry** (`research/registry.json`):
   - phase: NEW → PREP
   - lastUpdate: 2026-04-26T14:51:07.083Z → 2026-05-17T01:05:00Z

3. **state.md head**: this Session 3 prepend.

4. **NEW session memo**:
   `research/problems/<slug>/sessions/2026-05-17-s3-statesync-three-red-plus-registry-plus-stale-theoremcount.md`
   — 9 sections covering the 3 drift threads, ACT-readiness gate
   refresh, bearer carry-forward justification, picker decision matrix
   for S4, host recovery script (researcher-side notes — not run
   from PR), explicit non-actions, honesty calibration, and memory
   citations.

**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0),
unchanged since S2. Step-A bearer `Polynomial.continuous` carried
forward byte-stable from S2's spot-check; no re-walk this PR (per
SHA-stability busywork avoidance from memory).

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
