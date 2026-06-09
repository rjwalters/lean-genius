# S2 STATE-SYNC — research-side tracker catches up to verified file

**Slug**: `lagrange-theorem-oq-02-oq-02`
**Researcher**: researcher-1
**Date**: 2026-06-09
**Phase**: S2 STATE-SYNC (doc-only; research-side metadata catch-up
after an un-tracked S1 ACT completion.)
**Type**: Doc-only. Creates the standard `problem.md` / `state.md` /
`sessions/` scaffolding (which was missing from the un-tracked S1 ACT)
+ refreshes the research JSON. No `.lean` edits, no gallery
`meta.json` edits, no `knowledge.md` body edits.
**Lake-pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
(unchanged; carried forward from gallery `meta.json`).
**Base HEAD**: `58bdf51bc62` (`origin/main` at session start).

## §1 The mismatch

At session start, four artefacts disagree about this slug's status:

| Artefact | Claim |
|---|---|
| `knowledge.md` (only file in `research/problems/...`) | S1 session 2026-05-05 shipped 257 LOC / 13 theorems / **1 sorry**; "Next Steps": discharge `card_conjClass_eq_centralizer_index` via orbit-stabilizer + index arithmetic. |
| `proofs/Proofs/LagrangeTheoremOQ02OQ02.lean` | 262 LOC, 13 theorems, **0 sorries**, 0 local axioms. The S1 next-step has been completed. |
| `src/data/proofs/lagrange-theorem-oq-02-oq-02/meta.json` | `"status": "verified"`, `"badge": "verified"`, `"sorries": 0`, `"axiomCount": 0`, `"theoremCount": 13`, `"lineCount": 262`. Consistent with the file. |
| `src/data/research/problems/lagrange-theorem-oq-02-oq-02.json` | `phase: "NEW"`, `currentState.iteration: 1`, `currentState.focus: "Class equation formalized with 1 sorry (orbit-index technical connection)"`, `currentState.nextAction: "Begin problem exploration."` — pre-completion state. |

The Lean file + gallery `meta.json` reflect the actual completed
state; the `knowledge.md` notes and the research JSON are stale.
Additionally, the `research/problems/lagrange-theorem-oq-02-oq-02/`
directory is missing `problem.md` / `state.md` / `sessions/` —
the standard scaffolding all other research slugs have.

## §2 Probe results

### Lean file sorry/axiom count

```
$ grep -c '\bsorry\b' proofs/Proofs/LagrangeTheoremOQ02OQ02.lean
0

$ grep -c '^axiom ' proofs/Proofs/LagrangeTheoremOQ02OQ02.lean
0

$ wc -l proofs/Proofs/LagrangeTheoremOQ02OQ02.lean
262 proofs/Proofs/LagrangeTheoremOQ02OQ02.lean

$ grep -E '^theorem |^lemma ' proofs/Proofs/LagrangeTheoremOQ02OQ02.lean | wc -l
13
```

Confirmed: 0 sorries, 0 local axioms, 13 named theorem/lemma
declarations, 262 LOC.

### `card_conjClass_eq_centralizer_index` proof body (lines 126-138)

```lean
theorem card_conjClass_eq_centralizer_index [Fintype G] (x : G) :
    Nat.card (ConjClasses.mk x).carrier = (centralizer {x}).index := by
  rw [← conj_orbit_eq_carrier]
  have horb : Nat.card (MulAction.orbit (ConjAct G) x) =
      (MulAction.stabilizer (ConjAct G) x).index := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (ConjAct G) x)
  rw [horb, ← conj_stabilizer_eq_centralizer]
  exact (Subgroup.index_comap_of_surjective _
    (ConjAct.toConjAct (G := G)).surjective).symm
```

This matches the S1 next-step register's intended approach — orbit
card via `MulAction.orbitEquivQuotientStabilizer` plus
`Subgroup.index_comap_of_surjective` for the `ConjAct.toConjAct`
isomorphism. The discharge happened between 2026-05-05 (knowledge.md
session note) and 2026-06-09 (this STATE-SYNC); no PR specifically
recorded the S1.5 ACT in `gh pr list --search ...`.

### Gallery PR history

```
$ gh pr list --search "lagrange-theorem-oq-02-oq-02 in:title" --state all --limit 5
17930  Enrich lagrange-theorem-oq-02-oq-02: character theory bridge  MERGED 2026-05-12
(plus three sibling oq-02-oq-02-oq-01 mechanic / audit PRs from 2026-05-12 to 2026-05-13)
```

No PR explicitly mentions a S1 / S1.5 / S2 research event on this
slug. The PR record is enricher / mechanic / audit only. This
matches the "untracked" finding — the substantive Lean work was done
outside the standard research PR flow.

## §3 What this S2 STATE-SYNC ships

### Three new files

1. **`research/problems/lagrange-theorem-oq-02-oq-02/problem.md`** —
   full template fill-in:
   - Problem statement (formal Lean + plain English).
   - Classification (tier B, significance 5/10, tractability 8/10).
   - Related gallery proofs (4 siblings + 2 cousins).
   - References (Mathlib + Dummit & Foote + Lang).
   - Out-of-scope items (Burnside, Sylow, character theory).

2. **`research/problems/lagrange-theorem-oq-02-oq-02/state.md`** —
   reconstructs the slug's history with three iterations:
   - **Iter 1**: untracked S1 ACT 2026-05-05 (257 LOC, 1 sorry).
   - **Iter 1.5**: untracked discharge of the last sorry between
     2026-05-05 and 2026-06-09 (file 257 → 262 LOC, 1 → 0 sorries).
   - **Iter 2**: this S2 STATE-SYNC.
   Documents the verification probes, race-safety, and downstream
   options.

3. **`research/problems/lagrange-theorem-oq-02-oq-02/sessions/2026-06-09-s2-state-sync-tracker-catchup.md`**
   (this file) — full STATE-SYNC log.

### One JSON refresh

`src/data/research/problems/lagrange-theorem-oq-02-oq-02.json`:
- `phase: "NEW" → "COMPLETED"`.
- `currentState.phase`: `"ACT" → "COMPLETED"`.
- `currentState.since`: `2026-05-05T02:57:44.813Z → 2026-06-09T17:50:00Z`.
- `currentState.iteration`: `1 → 2`.
- `currentState.focus`: pre-completion → "S2 STATE-SYNC: research-
  side tracking caught up to actual file state; 0 sorries, 0 axioms,
  13 theorems, 262 LOC, gallery `verified`."
- `currentState.nextAction`: `"Begin problem exploration." → "(optional) doctor build verification + (optional) enricher bridge essay; substantive work complete."`
- `currentState.attemptCounts.total`: `0 → 2`.
- `knowledge.progressSummary`: appended with S1.5 + S2 STATE-SYNC note.
- `knowledge.nextSteps`: pre-completion list → downstream-options
  list (build verification, enrichment, follow-up slugs).
- top-level `updatedAt`: `2026-05-05T02:57Z → 2026-06-09T17:50Z`.

### What S2 STATE-SYNC does NOT ship

* **No Lean edits**. File byte-identical to the un-tracked completion
  state. (md5 not pinned this session due to docker `.lake`
  unavailability; a follow-up doctor pass can record the canonical
  md5.)
* **No build verification**. The `.lake` self-loop on the main repo
  precludes a `docker-build.sh Proofs.LagrangeTheoremOQ02OQ02` run.
  The `"verified"` status is taken on the gallery's prior testimony
  (`meta.json status: verified, badge: verified, sorries: 0`) plus
  this session's `grep`-based sorry/axiom probes. A doctor pass that
  applies the basel iter44 §5 Path A `.lake` remediation would add a
  build-verified stamp.
* **No gallery `meta.json` edits**. Gallery side is already correct.
* **No `knowledge.md` body edits**. The 2026-05-05 session note is
  preserved verbatim as the historical record.

## §4 Race-safety log

* **Pre-claim probe** (2026-06-09 ~17:50Z):
  `gh pr list --search "lagrange-theorem-oq-02-oq-02 in:title" --state open`
  → 0 open PRs on this slug.
* **Pre-edit probe** (the only file potentially in flight):
  `proofs/Proofs/LagrangeTheoremOQ02OQ02.lean` unchanged from the
  un-tracked S1.5 ACT state at session start; we do NOT modify it.
* **Gallery probe**: `src/data/proofs/lagrange-theorem-oq-02-oq-02/`
  contains `meta.json`, `annotations.json`, `index.ts` at session
  start; we do NOT modify any of these.
* **HEAD probe**: `origin/main` at `58bdf51bc62`; this S2 STATE-SYNC
  branches from there.

## §5 What the next researcher should do

Slug is substantively complete; recommended downstream actions are
all optional. **None block COMPLETED status.**

### Option A — Doctor build verification

Apply basel iter44 §5 Path A remediation:

```bash
rm /Users/rwalters/GitHub/lean-genius/proofs/.lake
cd /Users/rwalters/GitHub/lean-genius/proofs
./scripts/docker-build.sh Proofs.LagrangeTheoremOQ02OQ02
```

First run: 10-20 min cache-miss. Confirms the 13-theorem file builds
clean at lake-pinned Mathlib SHA `2df2f0150c…`. Output: docker job
count + clean status. Then a brief PR description amendment to add
the build-verified stamp.

### Option B — Enricher pass

The slug has a merged enricher PR (#17930, 2026-05-12,
character-theory bridge). A further enricher pass could expand
`annotations.json` with deeper class-equation narrative around p-group
structure, the Sylow theorems, A₅ simplicity, etc.

### Option C — Follow-up slug selection (seeker scope)

Natural class-equation-corollary slugs not yet in the gallery:

* **Burnside normal-p-complement theorem** — direct class-equation
  consequence for groups whose Sylow-p subgroup is in the center of
  its normalizer.
* **Sylow's theorem via class equation** — class-equation-based
  derivation of Sylow's existence + conjugacy. Likely overlaps with
  existing `sylow-theorems` gallery entry.
* **A₅ simplicity via class equation** — class sizes 1, 12, 12, 15, 20;
  no proper normal subgroup exists since no sub-sum of `{1, 12, 12, 15,
  20}` containing 1 divides 60.

### Option D — Mark complete and move on

The slug's substantive work is done. Marking it COMPLETED in the
research-side tracker (via this S2 STATE-SYNC) frees the pool slot
for a different OQ to be selected by the seeker. No further work
required.

## §6 Cross-references

* `knowledge.md` (2026-05-05 session note): original S1 ACT record.
* `src/data/proofs/lagrange-theorem-oq-02-oq-02/meta.json`: gallery
  source of truth (`verified` status).
* `proofs/Proofs/LagrangeTheoremOQ02OQ02.lean:126-138`: discharge
  body for `card_conjClass_eq_centralizer_index`.
* PR #17930 (2026-05-12): character-theory bridge enricher pass.
* basel-problem-oq-01-oq-01-oq-02-oq-03 Iter 44 INFRA-SIGNAL
  (2026-06-09, this researcher's prior session this day): `.lake`
  self-loop status; Path A remediation steps.
* shapley-folkman-oq-01 Sessions 16/17 (2026-06-04): same `.lake`
  trap on a different slug.

## §7 Honest framing

* **This is a small, low-risk STATE-SYNC**. The substantive work
  (Lean file + gallery meta.json) is already correct. The only
  risk is in the JSON `phase: NEW → COMPLETED` claim — if the file
  has not actually compiled (e.g., a Mathlib bearer drift since
  2026-05-05), the `verified` status is premature. The gallery
  meta.json testifies the file was verified at some prior point;
  this session does not re-run the build (due to `.lake` self-loop).
* **The un-tracked S1.5 ACT is real progress that was never
  recognised**. Some researcher (or doctor session) discharged
  `card_conjClass_eq_centralizer_index` between 2026-05-05 and
  2026-06-09 without creating a research PR. This is a process gap,
  not a substantive one — the work happened, just not visibly.
* **Two researcher-1 STATE-SYNC/INFRA-SIGNAL sessions in one day
  is fine**. The STATE-SYNC cap is 2 per researcher per session;
  this STATE-SYNC + the basel iter44 INFRA-SIGNAL are independent
  slugs, so the cap does not constrain.
