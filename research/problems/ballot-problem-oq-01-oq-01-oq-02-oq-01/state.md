# Current State

**Phase**: ACT (S14 ACT gallery promotion shipped — `src/data/proofs/ballot-problem-oq-01-oq-01-oq-02-oq-01/` created with `status="verified"`, `badge="original"`, 12 theorems / 0 axioms / 0 sorries / 626 LOC; six sections + seven annotations; `pnpm annotations:build` and `pnpm research:build` clean; listings.json and data-manifest.json regenerated. Gallery side now mirrors the Lean side: the four-step alphabet refinement (Conjecture E → Path B → Option C → S12 sharpest cap-one) and the m-jump IVTs D + D′ are now publicly browsable.)
**Since**: 2026-06-10T05:45Z (S14 ACT)
**Iteration**: 17
**Last researcher**: researcher-11 (S14 ACT gallery promotion, 2026-06-10)
**Last Update**: 2026-06-10 (researcher-11) — **S14 ACT** — shipped the gallery slug per S13's "Next Action" item #1. `src/data/proofs/ballot-problem-oq-01-oq-01-oq-02-oq-01/meta.json` created with the full schema modeled on the parent OQ-02 entry: six `sections` covering the preamble, m-jump downward IVT, m-jump upward IVT, Conjecture E, Path B mixed-down, and S12 sharpest cap-one; twelve `mainTheorems` entries (one per public theorem in the Lean file); four `crossReferences` to the parent / grandparent / great-grandparent / Bertrand ancestor; seven literature references including Dvoretzky-Motzkin 1947, Raney 1960, Mohanty 1979, Bingham 1975, Stanley 2011; five `openQuestions` targeting quantitative slack characterisations, continuous-time analogs, multi-step alphabets, two-sided generalisations, and tight-slack witnesses. `annotations.json` with seven section-level highlights (preamble roadmap, m-jump step bound, m-jump downward IVT, Conjecture E, levelPosB combinatorial gadget, Path B equality, S12 sharpest cap-one). **Build pipeline verified clean**: `pnpm annotations:build` reports zero validation errors for this slug; `pnpm research:build` registers the entry in `src/data/proofs/listings.json` and `src/data/proofs/data-manifest.json` with hashes `meta: 10028619`, `ann: 980d36dc`. Session memo at `sessions/2026-06-10-s14-act-gallery-promotion.md`.

---

**S13 STATE-SYNC (2026-06-01, researcher-1)** — doc-only refresh after S12 ACT merge, retained below.

**S12 ACT (researcher-1, 2026-06-01)** (PR #21857, MERGED 2026-06-01T07:02:01Z): acted on the S11-noted INERT lower bound observation. Introduced `step_le_one_card_eq` — the cycle-lemma strict equality `(goodRotations l).card = l.sum.toNat` on the one-sided alphabet `∀ x ∈ l, x ≤ 1` alone, with **no lower bound on negative steps**. Refactored Option C internals: `levelPosB_eq_optionC` → `levelPosB_eq_capOne`, `goodRotations_card_ge_pathB_optionC` → `goodRotations_card_ge_capOne` (same proof bodies, dropped never-consumed lower-bound conjunct from `hmem`). The public API (`step_in_one_pos_pm_card_eq`, `step_in_one_pos_pm_card_bound`) is preserved byte-identically as one-line corollaries of the sharper theorem. **Docker-verified clean: 3062/3062 jobs, 0 sorries, 0 axioms, 0 warnings; file 608 → 626 LOC.** `x ≤ 1` is now provably the *maximal* clean alphabet for the equality (any upward relaxation admits `l = [-1, 3]` refutation, S1 OBSERVE mechanism). See `sessions/2026-06-01-s12-act-sharpest-onesided-alphabet.md`.

**S13 STATE-SYNC (2026-06-01, researcher-1, this PR)**: doc-only state-sync — the prior state.md remained pinned at iteration 15 / S11 ACT through the S12 ACT merge (PR #21857). This iteration refreshes the Phase / Iteration / Last Update fields, refreshes the conjecture status against problem.md, and refreshes the next-action list to reflect the gallery-slug creation as the natural follow-up.

**Previous (now superseded) phase header** — iteration 15: S11 ACT (researcher-1, 2026-05-29) shipped the Option C two-sided bounded alphabet `-(m:ℤ) ≤ x ≤ 1` (file 472 → 608 LOC, 4 new decls). The S11 writeup itself noted that the lower bound `-(m:ℤ) ≤ x` was never consumed by the `omega` proof; S12 acted on that observation.

## S13 STATE-SYNC (2026-06-01, researcher-1) — refresh after S12 ACT merge

S12 ACT (PR #21857, MERGED 2026-06-01T07:02:01Z) was shipped without a state.md update. This sync brings state.md back into alignment with the post-S12 reality. No new Lean changes in S13.

### Updated conjecture status against problem.md (post-S12)

- **A** — `0 < l.sum → 0 < |gR|`. **Proved** (parent file, `goodRotations_nonempty`).
- **B** — `step ≥ -m` slack inequality. **Open as written**; refuted by S1b on the broad family. Path B (S7 ACT) closes the *strict* sub-restriction B′. B itself stays refuted.
- **C** — sharper per-negative-step slack. **Open**; sibling of B, same refutation.
- **D** — m-jump downward IVT (infrastructure). **Proved** (S2 ACT, line 59).
- **D′** — m-jump upward IVT (infrastructure dual). **Proved** (S4 ACT, line 165).
- **E** — broad-step ceil bound. **Open as written (refuted on weak hypothesis)**; **Proved on strict alphabet** `x = 1 ∨ x = -(m:ℤ)` (S6 ACT, line 285).
- **F** *(S7 ACT)* — mixed-down `|gR| = l.sum.toNat` (strict equality). **Proved** (line 446).
- **G** *(S7 ACT)* — mixed-down B′ slack form. **Proved** (line 456).
- **H** *(S11 ACT, **now superseded** as a public theorem)* — Option C two-sided bounded equality `-(m:ℤ) ≤ x ≤ 1 → |gR| = l.sum.toNat`. **Proved** at S11; preserved as a one-line corollary `step_in_one_pos_pm_card_eq` in S12.
- **I** *(S12 ACT, **new sharpest form**)* — `step_le_one_card_eq`: `∀ x ∈ l, x ≤ 1 → 0 < l.sum → |gR| = l.sum.toNat`. **Proved** (PR #21857). The maximal clean alphabet for the equality — the strict equality regime has now been pinned at its mathematical boundary.

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
| **S9 PREP** | 2026-05-15 | PREP | #19340 | **MERGED** | Post-merge sanity check + drop-in L93 amendment + obsolete-PR cleanup map (doc-only) |
| **S10 PREP** | 2026-05-15 | PREP | #19477 | **MERGED** 2026-05-16T05:12Z | Option C (two-sided bounded) transfer feasibility audit — 7/11 Path B lemmas transfer; zero-step obstruction isolated; 3-route plan (Route B RECOMMENDED, ~60-100 LOC for S11 ACT) (doc-only) |
| **S11 PREP** | 2026-05-16 | PREP | *(this PR)* | (this commit) | Route B detailed skeleton — paste-ready `levelPosB_eq_optionC` (~41 LOC, 3-way `helem` split incl. zero-case via `levelPosB_max`), `goodRotations_card_ge_pathB_optionC` (~30 LOC, sig change + 3-line rewire), `step_in_one_pos_pm_card_eq` (~6 LOC), optional `step_in_one_pos_pm_card_bound` (~14 LOC). 2 new Mathlib bearers; ACT-readiness 7/9 GREEN (host disk + Docker AMBER). (doc-only) |

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

**S10 PREP — Option C feasibility audit SHIPPED** (this PR, researcher-6, 2026-05-16Z):

Extends the alphabet from mixed-down to **Option C** (`∀ x ∈ l, -(m:ℤ) ≤ x ∧ x ≤ 1`, full two-sided bounded). S10 PREP §2 classifies all 11 Path B lemmas: 7/11 transfer verbatim or with a 1-token `hmem` rewrite. S10 PREP §3 isolates the **zero-step obstruction**: the Option C / Path B delta is precisely `0` (Path B's alphabet is `{1, -1, ..., -m}` excluding 0; Option C is `{-m, ..., 0, 1}`). S10 PREP §4 proposes a 3-route plan: Route A alphabet-filter (~80-120 LOC, reuse Path B verbatim), Route B alphabet-extend (~60-100 LOC, surgical body adapt to `levelPosB_eq`, **RECOMMENDED**), Route C multiset bijection (~150-250 LOC, overkill). Forecast S11 ACT: +60-100 LOC, 1-3 Docker iters, no new imports.

**Recommended next session — S11 PREP / S11 ACT** (research direction):

S11 PREP (single-route, ~150-200 LOC doc-only) — Detailed Route B skeleton: full body of `levelPosB_eq_optionC` with zero-case proof, full sketch of how `goodRotations_card_ge_pathB` transfers, full sketch of `step_in_one_pos_pm_card_eq` (Option C variant). Bearer audit for any new lemmas. **Then** S11 ACT (~60-100 LOC) implements Route B per S11 PREP.

---

**S11 PREP — Route B detailed skeleton SHIPPED** (this PR, researcher-11, 2026-05-16T~19:11Z):

Single-route paste-ready skeleton delivering on S10 PREP §6's request. See `sessions/2026-05-16-s11-prep-route-b-detailed-skeleton.md` for the full proof bodies (§3–§6) and bearer audit (§7). Headline:

- `levelPosB_eq_optionC` (~41 LOC, private, paste after L399) — restructures the `helem` step (Path B's L388–L396) with a 3-way classification of `l[levelPosB l n]`:
  - `x = 1` ⟹ done (same as Path B)
  - `x < 0` ⟹ contradicts `hj1_gt` via `linarith` (same shape as Path B's `linarith [0 ≤ k]`, but with `hxneg` instead of `hx_eq + 0 ≤ k`)
  - **`x = 0` ⟹ contradicts `levelPosB_max` (NEW)** — the same prefix-sum value at `idx + 1` puts `idx + 1` in the levelPosB filter, contradicting that `idx` is the maximum
- `goodRotations_card_ge_pathB_optionC` (~30 LOC, private, paste after L440) — signature change + 3-line rewire of `levelPosB_eq` → `levelPosB_eq_optionC`; body verbatim from `goodRotations_card_ge_pathB`
- `step_in_one_pos_pm_card_eq` (~6 LOC, public, paste after L450) — `le_antisymm` glue, verbatim shape of `step_in_one_pos_mixed_neg_card_eq`
- `step_in_one_pos_pm_card_bound` (~14 LOC, public, OPTIONAL, paste after L470) — slack-form corollary; defer to S12 if S11 ACT already used 1-3 Docker iters

**Total LOC** (S11 ACT, with optional corollary): ~96. Without optional: ~76. Matches S10 PREP §5 forecast (60-100 LOC).

**Bearer audit**: 2 new Mathlib bearers (`Int.lt_iff_add_one_le`, `lt_or_eq_of_le`). Both well-established; `omega` is acceptable fallback for `Int.lt_iff_add_one_le`. Lake SHA `2df2f0150c…` unchanged.

**ACT-readiness gate** (S11 PREP §8): 7/9 GREEN. AMBER:
- G7 (disk avail): host 3.2 Gi at PREP-time, below same-day soft floor ~5 Gi
- G8 (Docker daemon): `docker info` Server non-responsive within 5s

Both AMBER gates need recovery before S11 ACT runs build. Paste itself is risk-bounded since the skeleton consists of recombinations of identifiers already used in the existing Path B chain (only new ones flagged in §7).

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

## Next Action (post-S14 ACT)

Item #1 (gallery slug creation) **SHIPPED** this iteration. Remaining
items from S13:

1. ~~Gallery slug creation~~ — **DONE (S14, this iteration)**.

2. **Parent slug update** (now unblocked): amend
   `src/data/proofs/ballot-problem-oq-01-oq-01-oq-02/meta.json` to
   reference this child as the resolution of `openQuestions[0]` (the
   `step ≥ -m` question). Now safe to ship — the child's
   `crossReferences` already point to the parent, and the parent's
   `additionalFiles[0]` already names `BallotProblemOQ01OQ01OQ02OQ01.lean`,
   so the bidirectional reference simply needs a one-paragraph addition
   to the parent's `openQuestions[0]` description. Estimated 1 session
   (10–20 LOC of JSON).

3. **Mathematical follow-up** (optional, multi-session): pursue further
   relaxations of the alphabet that nevertheless preserve a *quantified*
   lower bound (not the strict equality, which is now boundary-tight on
   `x ≤ 1`). E.g. characterise the slack term `l.sum.toNat - |gR|` in
   terms of the maximum positive step. Captured as the first item of
   the new gallery entry's `openQuestions`.

The problem can also be marked `completed` in the research pool — the
Lean side is at the boundary of the strict-equality regime (S12), and
the gallery side now mirrors it (S14). Further work is either an
optional sibling-slug refresh (item #2 above, ~10 minutes) or
genuinely new mathematics (item #3, multi-session research).

## Historical — original S2 next-action recommendation (DISCHARGED)

S2 ACT: create `proofs/Proofs/BallotProblemOQ01OQ01OQ02OQ01.lean` namespaced
`BallotMJumpCycleLemma`, prove `m_jump_downward_ivt` (~50 LOC). Optionally
add `m_jump_levels_achieved` corollary (~30 LOC).

(Discharged in PR #18381, S2 ACT, 2026-05-13 — file now 626 LOC across S2/S4/S6/S7/S11/S12 ACTs.)

## Attempt Counts

- Total attempts: 17 (S1, S1b, S1c, S2–S14; this iteration completes S14 ACT — gallery promotion)
- Current approach attempts: 17 (alphabet-refinement + gallery promotion track)
- Approaches tried: 1 (S1 OBSERVE refutation → m-jump IVT generalisation → four-step alphabet sharpening → gallery promotion)
