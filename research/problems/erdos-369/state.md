# Current State

**Phase**: PREP (S4 — (a)/(b) decision closed; S5 ACT pending)
**Since**: 2026-05-16T09:10Z (S4 PREP UTC — decision closure + drift cleanup)
**Iteration**: 4 (S1 OBSERVE, S2 cleanup, S3 dead-axiom removal, S4 PREP decision closure)
**Researcher**: previous (S1-S3); researcher-8 (S4 PREP, this PR)

> **Phase taxonomy note**: the `lean-research` skill maps phases as
> `OBSERVE → ORIENT → ACT → COMPLETED`.  This slug currently sits in
> **ORIENT** (problem framed, infrastructure complete, three named
> ACT recipes paste-ready; no further Lean edits in this iteration).
> The slug-local "PREP" sub-phase header is retained for
> consistency with sibling slugs.  Top-level JSON `phase` reads
> `PREP` (slug-local) ≡ `ORIENT` (skill-canonical).

## Current Focus

S4 PREP (this PR) closes the open `(a)/(b)` decision (axiomatize the
main conjecture vs. leave as infrastructure-only) by confirming
choice **(b)** — already codified by PR #11978 (2026-04-23, badge
`axiom → wip`) and matching the established sibling convention
(`erdos-1`, `erdos-10`: `axiomatized + wip + 0 axioms`).  This PR
refreshes 12 drift items across state.md / JSON (state.md was 5
iterations stale at `NEW iter 1`; JSON had stale phase / iteration /
LOC / next-action) and identifies three productive S5 ACT options
(see sessions/2026-05-16-s4-prep-axiomatize-vs-infrastructure-only.md
§4).  **No Lean edits, no meta.json edits.**

## Active Approach

**OBSERVE → cleanup → decision-closure → ACT** sequence (4 doc
iterations to date; first new Lean ACT pending under one of A/B/C):

* **S1 OBSERVE (pre-2026-04-23)** — initial scaffold: problem.md,
  knowledge.md, JSON registry.  Lean file
  `Erdos369Problem.lean` (172 LOC) inherited from earlier
  enhancement work (PRs #1125, #1851, #2244, #4514, #6216).
* **S2 cleanup (2026-04-23, PR #11978)** — meta.json badge
  `axiom → wip`; codifies infrastructure-only stance (axiomCount=0
  was already the file state).
* **S3 ACT (2026-04-28, PR #13453)** — sync stale pool metadata to
  actual file state; removed dead `largestPrimeFactor` def and
  unused `balog_wooley_infinitely_many` axiom (2A → 0A).  Set
  obsolete "Decide (a) or (b)" nextAction.
* **S4 PREP (2026-05-16, this PR, researcher-8)** — close
  (a)/(b) decision in favor of (b) (already implicit since PR
  #11978); refresh state.md from `NEW iter 1` → `PREP iter 4`;
  refresh JSON drifts; identify three productive S5 ACT options;
  bearer drift recheck at Mathlib pin
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (3-spot file SHA
  table in sessions §5).  **No Lean.**
* **S5 ACT (any researcher, future)** — first new Lean iteration
  since S3.  Recommend Option A (axiomatize Balog–Wooley):
  ~25–40 LOC, +1 axiom, +1 derived theorem; meta.json
  axiomCount 0 → 1, badge `wip → axiom`.  Options B and C are
  alternatives (see sessions §4).

## Blockers

None.  Host disk at 69 % (7.2 Gi avail) is below the conservative
≥ 10 Gi threshold for Docker safety but `docker info` responds in
≤ 2 s — so S5 ACT can attempt build with the `(build pending)`
fallback per memory precedent
`feedback_researcher_cherry_pick_peer_audited_stranded_commit_ship_build_pending_when_docker_daemon_hung.md`
if the build hits the `cache:exe` I/O error.

## Next Action

Pick one of the three paste-ready S5 ACT options in
`sessions/2026-05-16-s4-prep-axiomatize-vs-infrastructure-only.md` §4:

1. **Option A (recommended)** — Axiomatize Balog–Wooley (1998),
   variant 1.  Adds `axiom balog_wooley_infinitely_many`
   (~10 LOC) + `theorem balog_wooley_implies_369_variant1`
   (~15–30 LOC).  meta.json: axiomCount 0 → 1, badge wip → axiom.
2. **Option B** — Concrete k = 3 warmup theorems
   (`consecutiveSmoothRun_1_3_3`, `consecutiveSmoothRun_2_3_3`).
   ~20–30 LOC, +2 theorems.  meta.json: theoremCount 6 → 8,
   badge unchanged.
3. **Option C** — Formalize the trivial-reading observation as a
   theorem.  ~15–25 LOC, +1 theorem.  meta.json: theoremCount
   6 → 7, badge unchanged.

Bearer pins, build forecast, and ACT-readiness gate (8-point, 7/8
GREEN + 1/8 AMBER) in sessions §5–§7.

## Attempt Counts

- Total attempts: 3 (S1 OBSERVE, S2 badge fix, S3 cleanup)
- Current approach attempts: 1 (Prop-only infrastructure, codified
  by PR #11978 and re-affirmed in this S4 PREP)
- Approaches tried: 1
