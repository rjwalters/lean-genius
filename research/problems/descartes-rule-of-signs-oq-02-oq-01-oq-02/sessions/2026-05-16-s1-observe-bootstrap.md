# Session 1 — S1 OBSERVE bootstrap

**Date**: 2026-05-16T09:25:00Z
**Researcher**: researcher-11
**Mode**: FRESH (claimed from pool, knowledge score 26 RICH, no prior `research/problems/<slug>/` directory)
**Outcome**: SURVEYED — slug bootstrapped from gallery-only to full S1 OBSERVE deliverable

## What I did

1. **Claimed** `descartes-rule-of-signs-oq-02-oq-01-oq-02` via
   `scripts/research/claim-problem.sh claim-random` (660 available, MODERATE+
   tier depth-first, claimed as `researcher-8999`, knowledge score 26
   RICH, expires 2026-05-16T10:46:18Z).
2. **Discovered the inheritance gap**: the slug exists in the gallery
   (`src/data/proofs/descartes-rule-of-signs-oq-02-oq-01-oq-02/`) with a
   complete `meta.json` (458 LOC, 1 axiom, 0 sorries, `status: "axiomatized"`,
   `badge: "axiom"`, 28 theorems claimed in meta but 26 declared in
   the Lean file — `sturm_exact_count` and the four corollaries count
   as 5 but the meta apparently double-counts the axiom alias…
   actual count: 26 proved declarations + 1 axiom = 27 total; gallery
   says 28 — **minor drift, flagged for an Auditor cycle**, not material
   to this PR).
3. **Verified no `research/problems/<slug>/` directory** existed prior
   to this PR (`ls research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02/`
   → "No such file or directory"). The slug is RICH despite never being
   claimed because of cross-references from
   `descartes-rule-of-signs-oq-02-oq-01` (Budan-upper-bound axiom S2 PREP),
   `descartes-rule-of-signs-oq-02` (Budan's theorem), and the gallery
   `annotations.json` (15 entries).
4. **Inventoried the Lean file** at HEAD `ecb47b35601` (worktree
   HEAD, on `origin/main`):
   - 458 LOC organised into 10 sections (`§1` Auxiliary Definitions →
     `§10` Comparison with Budan).
   - 6 definitions (`countSignAlts`, `signVariations`, `rootsInInterval`,
     `sturmSeqAux`, `sturmSeq`, `sturmVariations`).
   - 26 proved theorems + 1 axiom (`sturm_exact_count_axiom` at line 258).
   - 0 sorries, 0 structure-encoded assumptions (verified by
     `grep -nE "^(structure|class) " proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean`:
     only hit is a string `"structure"` inside a comment at line 454).
   - Imports: `Mathlib.Algebra.Polynomial.Basic`, `…Degree.Definitions`,
     `…Eval.Defs`, `…Derivative`, `…Div`, `Mathlib.RingTheory.Squarefree.Basic`,
     `Mathlib.Data.Real.Basic`, `Mathlib.Tactic`. Note: at Mathlib
     v4.26.0 the canonical Squarefree location is now
     `Mathlib/Algebra/Squarefree/Basic.lean` — the file's
     `RingTheory.Squarefree.Basic` import still works via `Mathlib.Tactic`
     transitive re-export but is a future-proofing candidate.
5. **Verified the Mathlib pin** at SHA
   `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) via 4 spot-checks
   on `repos/leanprover-community/mathlib4/contents/<path>?ref=<sha>`:
   - `Mathlib/Algebra/Polynomial/Div.lean` → 200 OK, size 36842
   - `Mathlib/Algebra/Polynomial/Derivative.lean` → 200 OK, size 26309
   - `Mathlib/Algebra/Squarefree/Basic.lean` → 200 OK, size 12275
     (canonical location at v4.26.0)
   - `Mathlib/RingTheory/Squarefree/Basic.lean` → 404 (moved; the file's
     import resolves via `Mathlib.Tactic` re-export)
6. **Drafted the bootstrap deliverables** (4 files this PR):
   - `problem.md` — formal target statement, classification, three "Why
     this matters" bullets, related-proofs table.
   - `knowledge.md` — 10-section S1 OBSERVE survey: inheritance,
     open-question statement, three-step proof strategy, already-proved
     bearers, Mathlib bearer verification, missing infrastructure,
     ACT-readiness gate, S2 PREP queue, honest assessment,
     parallel-work check.
   - `state.md` — Phase NEW → ORIENT, Active Approach table (8-phase
     multi-cycle plan, 4–8 ACT iterations forecast, ~600–950 LOC net),
     blockers (host disk pressure, no prior sessions, continuity
     ergonomics), Next Action = S2 PREP.
   - `sessions/2026-05-16-s1-observe-bootstrap.md` — this file.
7. **Confirmed no Lean source changes** in this PR: the file is
   already-built on `main` and not retouched; build status inherited
   from PR #14919 (origin) / #18059 (cosmetic re-add).

## Why this matters

The Lean file's docstring (lines 1–60) gives the full classical proof
strategy in three steps. The §5 lemmas (`mod_eval_at_root`,
`sturm_interior_sign_property`, `sturm_neighbors_opposite_at_root`) and
§9 lemmas (`squarefree_no_common_roots`,
`squarefree_deriv_ne_zero_of_pos_degree`) are *already proved* and
furnish the algebraic core. **The missing piece is the analytic core**:
piecewise constancy on zero-free intervals (continuity + IVT) plus the
combinatorial sign-change accounting on the pair `(p, p')` for the
drop-by-1 case and on the triple `(pₖ₋₁, pₖ, pₖ₊₁)` for the no-change
case.

This slug is therefore a **tractable but non-trivial multi-cycle target**:
the algebra is done, the analysis is missing. The natural decomposition
is three private lemmas (Step A locally constant, Step B drop-by-1, Step
C no-net-change) plus a final root-set-induction assembly. Each
sub-lemma is 80–180 LOC; the assembly is 80–150 LOC; total ~600–950
LOC over 4–8 ACT cycles.

## Pre-claim PR dedup

Before any planning, ran:

```
gh pr list --repo rjwalters/lean-genius \
  --search "descartes-rule-of-signs-oq-02-oq-01-oq-02 in:title state:all" \
  --limit 5
```

→ **0 results** (ever). The slug was created from PR #14919
("research(sturm): formalize Sturm's theorem for exact real root count")
which used a generic title without the slug. No overlap with any open
or merged PR. **Safe to proceed.**

## Files added (committed in this PR)

- `research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02/problem.md`
  (NEW: ~4 KB; formal statement, classification, related-proofs table)
- `research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02/knowledge.md`
  (NEW: ~13 KB; 10-section S1 OBSERVE survey)
- `research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02/state.md`
  (NEW: ~5 KB; Phase ORIENT, 8-phase plan, blockers, Next Action)
- `research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02/sessions/2026-05-16-s1-observe-bootstrap.md`
  (this file)

**No Lean changes.** Pure OBSERVE bootstrap. No `meta.json`,
`annotations.json`, `index.ts`, or other gallery file modifications.
Build status inherited from current `main` HEAD `ecb47b35601`.

## Host infrastructure snapshot

- `df -h /` → `926Gi / 16Gi used / 6.9Gi avail / 70% capacity` (note:
  capacity number reads low because of APFS containerised volumes; the
  hard cap is the **6.9 Gi available** number, which is below the
  cascade-safety threshold of ~30 Gi per MEMORY trap
  `_host_infra_blocked_buildverify_pivots_to_prep_deferred_reverify`).
- `docker ps -q` → 0 lines, daemon responsive in < 5 s.
- No active Docker `lean-build-*` containers.

The disk pressure is what gates this cycle to PREP-only. Once disk
recovers ≥30 Gi, S2 PREP can be followed by S3 ACT (Step A lemma).

## Honest assessment

- **Significance**: closes the last axiom on the Sturm chain. The four
  practical corollaries (`sturm_no_roots`, `sturm_unique_root`,
  `sturm_two_roots`, `sturmVariations_antitone`) become axiom-free
  on the same day the main axiom is discharged. Eventually upstreamable
  to Mathlib as `Mathlib.Algebra.Polynomial.SturmTheorem`.
- **Cost**: 4–8 ACT cycles, ~600–950 LOC net. Dominant cost is the
  Step B drop-by-1 lemma (~120–180 LOC) because of combinatorial
  sign-change accounting on the `(p, p')` pair.
- **Risk**: Mathlib continuity ergonomics for polynomial evaluation
  on closed intervals. If `Continuous.sign` / IVT helpers don't
  compose cleanly with `signVariations`, the S2/S3 lemma may need a
  manual rewrite (~150 LOC instead of ~80). 2× upward LOC revision
  is plausible per memory trap
  `_postship_pivot_lands_on_audit_corrected_skeleton_with_sorries_docker_unsafe_upgrade_to_paste_ready`.

## Recommended next handoff

**S2 PREP** (doc-only, ACT-pending on disk recovery):

1. 4-spot Mathlib bearer recheck at SHA `2df2f0150c…` including
   `Mathlib/Topology/Algebra/Polynomial.lean` for
   `Polynomial.continuous_eval` (the key not-yet-exercised bearer).
2. Draft paste-ready `private lemma sturmVariations_locally_constant`
   (~80–120 LOC) with `#check` block confirming Mathlib bearers
   resolve under existing imports.
3. Update ACT-readiness gate (item 5 PASTE-READY → GREEN, recheck
   item 1 DISK).
4. Open PR titled
   `research(descartes-rule-of-signs-oq-02-oq-01-oq-02): S2 PREP — bearer recheck + paste-ready Step-A locally-constant lemma (doc-only)`.

S3 ACT (Step A landing) only after disk ≥30 Gi avail.
