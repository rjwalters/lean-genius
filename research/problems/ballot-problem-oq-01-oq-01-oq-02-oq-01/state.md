# Current State

**Phase**: ACT (multiple) → PREP cleanup (Lean on `main`: D + D′ infrastructure, Conjecture E strict-alphabet, Path B mixed-down equality/slack all proved; PREP cleanup of spec drift + obsolete OPEN PRs)
**Since**: 2026-05-12T19:42:00Z
**Iteration**: 12
**Last researcher**: researcher-8 (S9 PREP post-merge audit + problem.md amendment, 2026-05-15)
**Last Update**: 2026-05-15 (researcher-8) — S9 PREP: post-merge sanity check of S6/S7 ACT on `main` + drop-in `problem.md` L93 amendment patch + obsolete-PR cleanup map (#19015 close, #19172 let-merge)

## Session Log (S6-S9 update, 2026-05-15, researcher-8)

state.md had drifted again past the S5 STATE-SYNC (researcher-4, 2026-05-13)
through five subsequent mergeable sessions. S9 PREP refreshes the Session Log
and ACT-readiness assessment.

| Session | Date | Mode | PR | Status | Title / focus |
|---|---|---|---|---|---|
| **S6** | 2026-05-14 | ACT | #19015 | OPEN/DIRTY (content on main via #19219 stack) | Conjecture E strict-alphabet discharge (`step_in_one_neg_m_count`) + 2× `linarith→omega` build unblockers |
| **S7 PREP** | 2026-05-14 | PREP | #19172 | OPEN/CLEAN (let deployer merge) | Path B (mixed-down alphabet) transfer audit (doc-only) |
| **S7 ACT** | 2026-05-15 | ACT | #19219 | **MERGED** 18:05:37Z | Path B mixed-down equality + B′ slack form (`_card_eq` + `_card_bound`, Docker-verified 3062 jobs) |
| **S8 PREP** | 2026-05-15 | PREP | #19263 | **MERGED** 18:02:43Z | `problem.md` L93 Conjecture E spec-error audit (doc-only) |
| **S9 PREP** | 2026-05-15 | PREP | *(this PR)* | (this commit) | Post-merge sanity check + drop-in L93 amendment + obsolete-PR cleanup map (doc-only) |

**Cumulative state on `origin/main`**: `BallotProblemOQ01OQ01OQ02OQ01.lean` is now 472 LOC (up from S5-era 228 LOC), 9 theorems, 0 sorries, 0 axioms. Theorems on main: `m_jump_step_bound`, `m_jump_downward_ivt`, `m_jump_downward_ivt_unit_recovery`, `m_jump_step_bound_upward`, `m_jump_upward_ivt`, `m_jump_upward_ivt_unit_recovery`, `step_in_one_neg_m_count` (strict alphabet, S6 ACT, line 285), `step_in_one_pos_mixed_neg_card_eq` (mixed-down, S7 ACT, line 446), `step_in_one_pos_mixed_neg_card_bound` (B′ slack, S7 ACT, line 456). See S9 PREP §2 for line-anchored inventory.

## S10 ACT-readiness assessment (replaces frozen S5-era assessment below)

**Conjecture status against problem.md (post-S9):**

- **A** — `0 < l.sum → 0 < |gR|`. **Proved** (parent file, `goodRotations_nonempty`).
- **B** — `step ≥ -m` slack inequality. **Open as written**; refuted by S1b on the broad family. Path B (S7 ACT) closes the *strict* sub-restriction B′, but B itself stays refuted unless re-stated.
- **C** — sharper per-negative-step slack. **Open**; sibling of B, same refutation.
- **D** — m-jump downward IVT (infrastructure). **Proved** (S2 ACT, line 59).
- **D′** — m-jump upward IVT (infrastructure dual). **Proved** (S4 ACT, line 165).
- **E** — broad-step ceil bound. **Open as written (refuted on weak hypothesis)**; **Proved on strict alphabet** (`x = 1 ∨ x = -(m:ℤ)`, S6 ACT, line 285). **Spec-amendment patch shipped in S9 PREP §4.1** — awaits /doctor or /auditor application.
- **F** *(new, S7 ACT)* — mixed-down `|gR| = l.sum.toNat` (strict equality). **Proved** (line 446).
- **G** *(new, S7 ACT)* — mixed-down B′ slack form. **Proved** (line 456).

**Recommended next session — S10 PREP** (research direction):

Extend the alphabet from mixed-down to **Option C** (`∀ x ∈ l, -(m:ℤ) ≤ x ∧ x ≤ 1`, full two-sided bounded). S8 PREP §6 confirms no Mathlib bearer for any cycle-lemma form, so Option C requires in-repo IVT-on-`[-m,1]` argument. Recommend S10 PREP to first sketch the transfer (200-300 LOC doc-only) before any S10 ACT attempt.

**Recommended next session — S10 doctor/champion** (cleanup, parallel to research):

- Apply S9 PREP §4.1 patch to `problem.md` L93 (Option A; minimal spec-aligning change).
- Close-without-merge PR #19015 per S9 PREP §5.1 (S6 ACT Lean content already on main via #19219 stack; only session-doc was unique).
- Let deployer merge PR #19172 per S9 PREP §5.2 (CLEAN doc-only, unique on main).

---

## ACT readiness assessment (frozen at S5, 2026-05-13, researcher-4 — superseded by S10 above)

## Session Log (STATE-SYNC, 2026-05-13, researcher-4)

state.md had drifted from "Phase: OBSERVE / Iteration 1 / Last researcher: researcher-1"
to its current frozen form after **seven** subsequent merged sessions (S1b/S1c/S2/S3/S4/S5),
each landing a doc-only or build-pending PR that left state.md untouched. This
STATE-SYNC adds 1-entry-per-merged-session and refreshes Phase / Iteration / Last
Update so a returning agent can pick up cold. The `currentState.focus` and
`knowledge.progressSummary` in the companion JSON already encoded the timeline; this
catches state.md up.

| Session | Date | Mode | PR | Title / focus |
|---|---|---|---|---|
| **S1** | 2026-05-12 | OBSERVE | #18253 | Refute naive ⌈S/m⌉ lower bound for step ≥ -m cycle lemma; identify refined conjectures A–E |
| **S1b** | 2026-05-12 | OBSERVE | #18480 | Refute refined Conjectures B and C via `[K, -m]` family |
| **S2** | 2026-05-13 | ACT | #18381 | m-jump downward IVT — primary target lemma `m_jump_downward_ivt` (build-pending) |
| **S3** | 2026-05-13 | PREP | #18424 | Conjecture E bridge to parent's `cycle_lemma` (doc-only) |
| **S1c** | 2026-05-13 | PREP | #18487 | Conjecture B′ (two-sided alphabet) discharge sketch (doc-only) |
| **S4** | 2026-05-13 | ACT | #18693 | `m_jump_upward_ivt` (D′, symmetric dual of D; build-pending) |
| **S5** | 2026-05-13 | PREP | #18703 | Audit S1c §3.2 discharge sketch |

**Cumulative state**: `BallotProblemOQ01OQ01OQ02OQ01.lean` exists (228 LOC, 6 theorems,
0 sorries, 0 axioms — per `leanFiles` snapshot). The build-pending S2/S4 PRs land
`m_jump_downward_ivt` (D) and `m_jump_upward_ivt` (D′). PREP work (S3/S1c/S5) sketches
discharge of remaining refined conjectures B′ and E.

## ACT readiness assessment

- **S6 ACT-E**: discharge Conjecture E by chaining the (now-merged) D + D′ into the
  parent's `cycle_lemma` bridge specified in S3 PREP (#18424). Estimated ~80–120 LOC.
- **S6 ACT-B′**: implement B′ (two-sided alphabet) per S1c §3.2 sketch audited in S5
  (#18703). Estimated ~60–100 LOC.
- **Build verification of S2/S4**: both PRs are build-pending. A subsequent session
  should run `./proofs/scripts/docker-build.sh Proofs.BallotProblemOQ01OQ01OQ02OQ01`
  and report success or failure. If failure, doctor agent (`/doctor`) takes over.

**Recommended next session**: S6 ACT-E (chain D + D′ into parent's cycle_lemma via
S3 bridge). Pre-requisite: confirm S2/S4 build (or pause until that's resolved).

---

## Original Current Focus (frozen at S1, 2026-05-12, researcher-1)

S1 OBSERVE complete: the parent meta's `openQuestions[0]` conjecture
`(step ≥ -m) ∧ (S > 0) → ⌈S/m⌉ ≤ |goodRotations|` is **refuted** by the
two-element family `l = [-m, m + S]` (smallest witness: `m = 2`, `l = [-2, 5]`,
`|goodRotations| = 1`, `⌈3/2⌉ = 2`).

See `problem.md` for the full statement and refutation, and `knowledge.md` for
the worked verification, mechanism-of-failure analysis, and five refined
conjectures **A–E**.

## Active Approach (frozen at S1)

S2 ACT target: **conjecture D — m-jump downward IVT**, the direct
m-generalization of the parent's `unit_decrement_downward_ivt`
(`BallotProblemOQ01OQ01OQ02.lean:60`). The conclusion window
`[v - m + 1, v]` collapses to `{v}` at m = 1, recovering the unit-decrement
IVT. Proof template transfers verbatim (leftmost-crossing `Finset.min'`).

(S2 ACT was subsequently shipped as PR #18381 on 2026-05-13.)

## Blockers

None. No Mathlib gap anticipated (all required primitives — `Finset.min'`,
`Finset.min'_mem`, `Finset.min'_le`, `List.sum_take_succ`, `List.getElem_mem`
— present in v4.26.0).

## Next Action

S2 ACT: create `proofs/Proofs/BallotProblemOQ01OQ01OQ02OQ01.lean` namespaced
`BallotMJumpCycleLemma`, prove `m_jump_downward_ivt` (~50 LOC). Optionally
add `m_jump_levels_achieved` corollary (~30 LOC).

## Attempt Counts

- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (S1 OBSERVE — refutation by example)
