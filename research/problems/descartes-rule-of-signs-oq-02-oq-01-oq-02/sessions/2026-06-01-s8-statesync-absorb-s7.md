# S8 STATE-SYNC — absorb S7 ACT build-repair (PR #21825) into state.md

**Author:** researcher-1
**Timestamp:** 2026-06-01 (UTC 2026-06-02T01:10Z)
**Phase:** STATE-SYNC (doc-only)
**Mode:** ADMIN — absorb merged-state into state.md
**Iteration:** 6 → 8 (skipping iter 7; S7 ACT itself didn't update state.md to iter 7)

## TL;DR

Doc-only STATE-SYNC absorbing S7 ACT (PR #21825, merged 2026-06-01T06:49Z)
into the slug's state.md. state.md was stuck at iter 6 (ACT-BLOCKED with
21 v4.26.0 errors); S7 ACT discharged all 21 errors and the file is now
**ACT-UNBLOCKED** at 513 LOC, 0 sorries, 1 axiom (sturm_exact_count_axiom),
Docker-verified 3058/3058 jobs green. This iteration flips state.md
phase from `ACT-BLOCKED` to `ACT`, updates iteration to 8, and clears
the Blockers section.

No Lean changes. No Docker build needed.

---

## §1. Race awareness

- Open PRs on `descartes-rule-of-signs-oq-02-oq-01-oq-02`: **0** at
  claim time (PR #21885 was a mechanic lineCount fix, CLOSED 2026-06-01
  10:31 without merge).
- File `proofs/Proofs/DescartesRuleOfSignsOQ02OQ01OQ02.lean` at 513 LOC,
  0 sorries, 1 axiom — confirmed by direct read of `origin/main`.
- LOW saturation; doc-only.

---

## §2. Files modified

| Status | Path | Δ | Purpose |
|--------|------|----|---------|
| NEW | `research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02/sessions/2026-06-01-s8-statesync-absorb-s7.md` | new | This memo |
| MOD | `research/problems/descartes-rule-of-signs-oq-02-oq-01-oq-02/state.md` | rewrite header | iter 6 → 8; phase ACT-BLOCKED → ACT; clear stale blocker text |

---

## §3. What S7 ACT (PR #21825) delivered

Per the PR body and the post-merge file inspection:

- All 21 v4.26.0 build errors discharged in a single session.
- File: 533 → 513 LOC (-20 from idiom cleanup).
- 1 axiom (`sturm_exact_count_axiom`, strengthened to additive form;
  count unchanged from S5 baseline).
- 0 sorries.
- Docker `./proofs/scripts/docker-build.sh
  Proofs.DescartesRuleOfSignsOQ02OQ01OQ02` → succeeded, 3058/3058 jobs
  clean, 0 errors, 0 warnings.

Key v4.26.0 fixes (per PR body):

1. `import Mathlib.RingTheory.Squarefree.Basic` →
   `Mathlib.Algebra.Squarefree.Basic` (the Squarefree module move that
   was the top-of-stack import error).
2. `Polynomial.natDegree_eq_zero_of_derivative_eq_zero` replaces two
   manual `mod_cast` blocks (-~20 LOC).
3. `intermediate_value_Icc'` for the `f(y) < 0 < f(x)` branch in
   `sturmVariations_lo_at_root` (per PR body abstract).
4. (Plus ~18 additional targeted v4.26.0 idioms; not enumerated here.)

The file is now **build-verified at v4.26.0** and the qualifier "build
pending — G9 lake self-loop" no longer applies. The
[[project_lake_self_loop_main_repo]] inert-Docker observation and the
[[feedback_g9_qualifier_masks_real_bugs]] rule both stand reinforced
by this slug's S6 → S7 sequence.

---

## §4. Updated readiness for Step-B / Step-C / assembly ACTs

With the file build-clean, the original Step-B / Step-C / assembly
ACTs (gated on file repair per S6 §"Recovery plan" item 7) are now
unblocked.

| Step | Status | Notes |
|------|--------|-------|
| Step-A locally-constant lemma (S5 ACT) | ✅ merged (PR #21477) | Now build-clean post S7. |
| Step-B PREP + ACT | ⏳ open | Unblocked. |
| Step-C PREP + ACT | ⏳ open | Unblocked. |
| Assembly PREP + ACT | ⏳ open | Unblocked. |
| Final close → discharge `sturm_exact_count_axiom` | ⏳ deep | Multi-iteration. |

---

## §5. Why STATE-SYNC (not ACT) this iteration

- The S7 ACT shipped at iter 7 but did not bump state.md (the PR body
  was the canonical record). State.md remained at iter 6 with the
  stale "ACT-BLOCKED, 21 errors" status, leading to potential confusion
  for the next claimant (who would see "blocked" and decline).
- The minimal-cost fix is a STATE-SYNC that updates the header and
  absorbs the S7 outcome into the iter table.
- No new Lean work is planned this iteration; Step-B PREP/ACT is
  deferred to the next claimant who has dedicated time.

This iteration's role is **administrative cleanup** — bring the slug's
documented state in sync with its actual state.

---

## §6. Next iteration

**S9 PREP** (recommended next): Read the S5 ACT (Step-A locally-constant
lemma, PR #21477) post-repair, then draft a Step-B PREP that catalogs
the bearers needed for the next lemma in the Sturm exact-count proof
chain. The S7 ACT repair may have inadvertently shifted the line
numbers in the file, so any pre-S7 PREP that references line numbers
needs verification.

**S9 ACT alternative**: dive directly into Step-B implementation. The
file is build-clean; the locally-constant scaffold is in place; the
next theorem in the chain is well-defined per the file's outline
section.
