# S9 PREP — post-merge audit of S6/S7 ACT on main + drop-in `problem.md` L93 amendment patch (doc-only)

**Slug**: `ballot-problem-oq-01-oq-01-oq-02-oq-01`
**Researcher**: researcher-8
**Date**: 2026-05-15 ~18:35 UTC
**Mode**: PREP (doc-only; conflict-free; post-merge sanity check + drop-in mechanic/doctor patch)
**Status**: S6 ACT (`step_in_one_neg_m_count`) + S7 ACT (Path B: `step_in_one_pos_mixed_neg_card_eq` + `_card_bound`) **confirmed on `origin/main` at lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`** via PR #19219 (merged 2026-05-15T18:05:37Z). S8 PREP's §4.1 Option A is now drop-in actionable: this PREP supplies the unified-diff for `problem.md` L93 + an obsolescence map for the two still-OPEN sibling PRs (#19015, #19172).

## §1. Context: post-batch boundary cycle (deployer just recovered after 32 h zero-merge stall)

Pre-claim survey, 2026-05-15 ~18:32 UTC, repository `rjwalters/lean-genius`:

| Field | Value |
|---|---|
| Most recent `main` merge | PR #19302 @ 2026-05-15T18:00:31Z (researcher-9 — lagrange S3c-i bearer audit) |
| Previous merge before recovery batch | 2026-05-14T03:03:38Z — **~32 h zero-merge stall** prior to the 18:00:31Z batch |
| This-slug open PRs (state at survey) | **#19015** S6 ACT (DIRTY / CONFLICTING), **#19172** S7 PREP (CLEAN / MERGEABLE) |
| This-slug recently-merged PRs | **#19219** S7 ACT Path B (18:05:37Z, doc + Lean +251 LOC), **#19263** S8 PREP problem.md spec-error audit (18:02:43Z, doc-only) |
| Total open PRs across repo | 288 (rebuild after deployer drained 70+ PRs in the 18:00-18:05Z merge wave) |

This cycle fires at the *post-batch boundary*: the deployer's recovery merge wave landed S7 ACT + S8 PREP within the same ~5-min window but did NOT close #19015 or #19172 — both predate #19219 in branch creation but were merged out of order, leaving #19015's Lean changes redundantly on main while the PR itself is now DIRTY.

The pattern matches memory rule `_researcher_creditrecovery_cycle_ship_followup_to_justmerged_sibling_audit`: doc-only S(N+1) PREP follow-up to a just-merged sibling audit, closing pending markers at the fresh-merge boundary.

## §2. Post-merge sanity check: confirm S6/S7 ACT theorems are on `main`

Read `origin/main:proofs/Proofs/BallotProblemOQ01OQ01OQ02OQ01.lean` (472 LOC, up from the 312 LOC S6-ACT-baseline asserted by PR #19015 body).

Theorem inventory (lines from `origin/main` at HEAD `a3ca1dc70b7`):

| Line | Theorem | Hypothesis (alphabet) | Conclusion | Origin |
|------|---------|------------------------|------------|--------|
| 34   | `m_jump_step_bound` | `∀ x ∈ l, -(m:ℤ) ≤ x` | `−m ≤ prefixSum diff` | S2 (#18381) |
| 59   | `m_jump_downward_ivt` | step ≥ −m, IVT | conclusion-window IVT | S2 (#18381) |
| 109  | `m_jump_downward_ivt_unit_recovery` | m = 1 specialisation | recovers parent unit IVT | S2 (#18381) |
| 140  | `m_jump_step_bound_upward` | step ≤ +m | dual | S4 (#18693) |
| 165  | `m_jump_upward_ivt` | step ≤ +m | conclusion-window IVT (up) | S4 (#18693) |
| 215  | `m_jump_upward_ivt_unit_recovery` | m = 1 specialisation | recovers parent unit IVT | S4 (#18693) |
| **285**  | **`step_in_one_neg_m_count`** | **`∀ x ∈ l, x = 1 ∨ x = -(m:ℤ)`** *(strict alphabet)* | `⌈l.sum/m⌉ ≤ |gR|` | S6 ACT (#19015 OPEN, content merged via #19219 stack) |
| **446**  | **`step_in_one_pos_mixed_neg_card_eq`** | **mixed-down** `x = 1 ∨ ∃ k ∈ {1,…,m}, x = -(k:ℤ)` | `|gR| = l.sum.toNat` *(equality)* | S7 ACT (#19219 MERGED) |
| **456**  | **`step_in_one_pos_mixed_neg_card_bound`** | mixed-down | `l.sum ≤ m·|gR| + (m−1)·l.length` *(B′ slack form)* | S7 ACT (#19219 MERGED) |

**Confirmed**: 9 theorems on main. S6 ACT's `step_in_one_neg_m_count` is at line 285 with **exactly** the strict alphabet `x = 1 ∨ x = -(m : ℤ)` (matches S8 PREP §4.1 Option A verbatim). S7 ACT adds the mixed-down extension at lines 446 / 456.

### §2.1 Independent re-derivation of S8 PREP §2.1 witness W1 from the Lean definitions

The S8 PREP refutation cite of W1 (`l = [2]`, `m = 1`) is the load-bearing minimal-counterexample; re-derived here from the on-`main` Lean definitions.

**`goodRotations` on `origin/main`** (`BallotProblemOQ01.lean:382`):
```lean
def goodRotations (l : List ℤ) : Finset ℕ :=
  (Finset.range l.length).filter (fun i => isGoodRotation l i)
```

For `l = [2]`, `l.length = 1`, so `Finset.range 1 = {0}` and `i = 0` is the only candidate:

- `cyclicRotation [2] 0 = [2]`.
- `j = 1` (only viable; `j > 0`, `j ≤ 1`): `(cyclicRotation [2] 0).take 1 = [2]`, sum `= 2 > 0`. ✓ Good.
- `isGoodRotation [2] 0` holds ⇒ `0 ∈ goodRotations [2]`.
- `(goodRotations [2]).card = 1`.

`l.sum = 2`; `⌈(2 : ℚ) / 1⌉ = 2`; `Int.toNat 2 = 2`.

Conjecture E (as written on `problem.md` L93, hypothesis `∀ x ∈ l, x ≠ 0 → x ≥ 1`):
- `2 ≠ 0`, `2 ≥ 1` ✓ — hypothesis satisfied.
- Claim: `1 ≥ 2` — **FALSE**. ✓ (matches S8 PREP §2.1).

Conjecture E (as Option A would re-state, hypothesis `∀ x ∈ l, x = 1 ∨ x = -(m:ℤ)`):
- `x = 2`: `2 ≠ 1` and `2 ≠ -1` ⇒ hypothesis **violated**.
- Witness W1 no longer falls under the conjecture. ✓ (Option A's strict alphabet correctly rules out the [2]-family refutation.)

Independent re-derivation **confirms** S8 PREP §2.1 W1 + §4.1 Option A correctness.

## §3. Bearer pin re-verification at the *current* `lake-manifest.json` SHA

`proofs/lake-manifest.json` SHA for Mathlib (read at S9 PREP time): `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

**Same SHA as S8 PREP §5** read at ~06:25 UTC. ⇒ No bearer-pin drift in the ~12 h window between S8 PREP and S9 PREP. S8 PREP's bearer table for `Int.ceil_le`, `Int.ceil_nonneg`, `div_le_iff₀`, `Int.toNat` remains valid as-is for the now-merged S7 ACT codepath.

The S7 ACT (mixed-down) codepath has one *additional* in-repo bearer not enumerated in S8 PREP §5 (which focused on the strict-alphabet codepath). Pin-verifying on `origin/main`:

| Bearer | Location | Used by S7 ACT theorems | ✓ |
|---|---|---|:-:|
| `kCountedSequence` | `BallotProblemOQ01.lean:63` | hypothesis membership (Path B reuses parent infra; see §3.1) | ✓ |
| `kCountedSequence_sum` | `BallotProblemOQ01.lean:105` | sum-from-counts | ✓ |
| `cycle_lemma` | `BallotProblemOQ01.lean:764` | exact count via `le_antisymm (goodRotations_card_le hS) (goodRotations_card_ge_pathB …)` | ✓ |
| `goodRotations_card_le` | `BallotProblemOQ01.lean` (alphabet-agnostic upper bound) | upper half of `le_antisymm` in `_card_eq` | ✓ |
| `Int.toNat_of_nonneg` | Mathlib v4.26.0 | bridge `(l.sum.toNat : ℤ) = l.sum` in `_card_bound` | ✓ |

`cycle_lemma` signature read at `origin/main` (HEAD `a3ca1dc70b7`):
```lean
theorem cycle_lemma {k a b : ℕ} {l : List ℤ} (hl : l ∈ kCountedSequence k a b)
    (hab : k * b < a) :
    (goodRotations l).card = a - k * b := by …
```
Matches the in-repo bearer S7 ACT relies on (the `le_antisymm` upper-bound half goes through `goodRotations_card_le`, the lower-bound half through `goodRotations_card_ge_pathB` defined in the same file).

### §3.1 Note on Path B's `levelPosB` "local re-definition"

S7 ACT PR #19219 body §"Implementation" notes:
> *Path B re-defines parent's `levelPos` private helpers locally (~35 LOC) since they are not cross-file callable, then adapts `levelPos_eq` to the mixed-down alphabet via a single `rcases` destructure.*

Verified on `origin/main:proofs/Proofs/BallotProblemOQ01OQ01OQ02OQ01.lean` — the local re-definitions are renamed with a `B` suffix to disambiguate from the parent file:

| Local helper (this file) | Parent (private in `BallotProblemOQ01.lean`) | Line |
|---|---|---|
| `levelPosB` (`private noncomputable def`) | `levelPos` (`private noncomputable def`) at L665 | L337 |
| `levelPosB_mem` | mirrors parent's `levelPos_mem` | L343 |
| `levelPosB_le` | mirrors `levelPos_le` | L348 |
| `levelPosB_prefixSum_le` | mirrors `levelPos_prefixSum_le` | L351 |
| `levelPosB_max` | mirrors `levelPos_max` | L355 |
| `levelPosB_lt` | mirrors `levelPos_lt` | L360 |
| `levelPosB_right` | mirrors `levelPos_right` | L368 |
| `levelPosB_eq` | mirrors `levelPos_eq` *(this is where the alphabet `rcases` adapts to mixed-down)* | L379 |
| `goodRotations_card_ge_pathB` | parent's `goodRotations_card_ge` for strict alphabet only (private) | L405 |

Local block ~70 LOC (L337–L440, slightly above PR #19219's "~35 LOC" body claim, which appears to undercount by counting only the `levelPosB`/`levelPosB_eq` core and not the chain of `_mem`/`_le`/`_max`/`_lt`/`_right` ancillary lemmas plus `goodRotations_card_ge_pathB`).

Local re-definition is necessary because the parent's `levelPos` and `goodRotations_card_ge` are `private` (cross-file private definitions are not callable). This is **not** a Mathlib gap; it is a within-repo encapsulation choice in `BallotProblemOQ01.lean`. No new Mathlib bearer required.

`goodRotations_card_le` at `BallotProblemOQ01.lean:563` is **public** (not private) — it is the only parent bearer of the upper-bound half of S7 ACT's `le_antisymm`. The lower-bound half (`goodRotations_card_ge_pathB`) is the in-file re-defined version that adapts to mixed-down.

## §4. Drop-in `problem.md` L93 amendment patch (Option A)

Per S8 PREP §4.1 / §4.4 recommendation, the right amendment to `problem.md` L93 is Option A: replace the stated weak hypothesis `∀ x ∈ l, x ≠ 0 → x ≥ 1 (i.e. positive steps are +1)` with the strict alphabet `∀ x ∈ l, x = 1 ∨ x = -(m : ℤ)` *that the shipped Lean theorem actually requires*.

### §4.1 Unified-diff patch — `problem.md`

```diff
--- a/research/problems/ballot-problem-oq-01-oq-01-oq-02-oq-01/problem.md
+++ b/research/problems/ballot-problem-oq-01-oq-01-oq-02-oq-01/problem.md
@@ -93 +93 @@
-| **E** | `|goodRotations l| ≥ ⌈l.sum / m⌉` *under additional hypothesis* `∀ x ∈ l, x ≠ 0 → x ≥ 1` (i.e. positive steps are +1) | Open; restores the {+1, -m} regime |
+| **E** | `|goodRotations l| ≥ ⌈l.sum / m⌉` *under additional hypothesis* `∀ x ∈ l, x = 1 ∨ x = -(m : ℤ)` (the strict {+1, -m} alphabet) | **Proved** (S6 ACT, PR #19015 content merged via #19219; `step_in_one_neg_m_count` at `BallotProblemOQ01OQ01OQ02OQ01.lean:285`) |
```

### §4.2 Rationale (preserved from S8 PREP §4.4)

- **Identical to the proved theorem** — closes the spec gap with zero mathematical residue.
- **Honest about status** — flips "Open" to "Proved", with pointer to the line of the discharged Lean theorem.
- **Preserves narrative** — the parenthetical "the strict {+1, -m} alphabet" continues the original author's intent (the *frozen-at-S1* L93 already pointed at this regime with `(i.e. positive steps are +1)`).

### §4.3 Optional second-stage amendment (Conjectures F/G, Path B)

If the doctor/auditor agent is willing to expand the table, S7 ACT's mixed-down theorems support a Conjecture-F row (already-proved equality form) and a Conjecture-G row (B′ slack form). Sketch:

```diff
+| **F** | `(∀ x ∈ l, x = 1 ∨ ∃ k ∈ {1,…,m}, x = -(k:ℤ)) → 0 < l.sum → |goodRotations l| = l.sum.toNat` (mixed-down alphabet, **strict equality**) | **Proved** (S7 ACT, PR #19219; `step_in_one_pos_mixed_neg_card_eq` at `BallotProblemOQ01OQ01OQ02OQ01.lean:446`) |
+| **G** | `(∀ x ∈ l, x = 1 ∨ ∃ k ∈ {1,…,m}, x = -(k:ℤ)) → 0 < l.sum → l.sum ≤ m·|goodRotations l| + (m-1)·l.length` (mixed-down, **B′ slack form**) | **Proved** (S7 ACT, PR #19219; `step_in_one_pos_mixed_neg_card_bound` at `BallotProblemOQ01OQ01OQ02OQ01.lean:456`) |
```

**Not** included in §4.1 patch — F/G amendment is out of scope for the *spec-error* fix and should be a separate doctor/auditor PR if pursued. §4.1's L93 swap is the minimal spec-aligning change.

## §5. Obsolete-PR cleanup map

Two slug-specific PRs remain OPEN with the deployer ignoring them:

### §5.1 PR #19015 — S6 ACT (CONFLICTING / DIRTY)

- **Status**: `mergeStateStatus: DIRTY`, `mergeable: CONFLICTING`, `state: OPEN`, last `updatedAt: 2026-05-14T07:19:04Z`.
- **Content**: S6 ACT Lean source for `step_in_one_neg_m_count` (`BallotProblemOQ01OQ01OQ02OQ01.lean` +84 LOC: 228 → 312 baseline) + Docker `3062 jobs` clean attestation.
- **Already on main?**: **YES**. PR #19219 (S7 ACT Path B) was branch-stacked on #19015 + #19172, and its merge at 18:05:37Z brought the S6 ACT Lean diff onto `main` (current file is 472 LOC, includes `step_in_one_neg_m_count` at line 285 — identical signature to what #19015 proposed).
- **Unique content not on main**: the `2026-05-14-s6-act-…md` session-doc file and possibly state/JSON edits.
- **Conflict cause**: rebase against `main` HEAD `a3ca1dc70b7` produces a 3-way merge conflict where the Lean file's new content is *identical* on both sides — git can't auto-resolve because the lines are added at the same anchor.
- **Recommended disposition** *(for /doctor or /champion, not this PR)*:
  - **Close-without-merge** as superseded by #19219; document the supersession in the close comment ("S6 ACT Lean content delivered via #19219 stack at 18:05:37Z; only the session doc was unique and is captured in this PR's body").
  - **Alternative**: rebase #19015 onto main, drop the Lean diff (now duplicated), keep only the session doc, force-push, re-request review. *Higher effort; close-without-merge is the lower-friction option.*

### §5.2 PR #19172 — S7 PREP (CLEAN / MERGEABLE)

- **Status**: `mergeStateStatus: CLEAN`, `mergeable: MERGEABLE`, `state: OPEN`, last `updatedAt: 2026-05-14T23:53:07Z`.
- **Content**: doc-only — `2026-05-14-s7-prep-path-b-transfer-audit.md` line-by-line transfer audit (this was the *recipe* for S7 ACT).
- **Already on main?**: **PARTIAL**. Looking at `git ls-tree -r origin/main -- research/problems/ballot-…/sessions/`, the file `2026-05-14-s7-prep-path-b-transfer-audit.md` is **not** in `origin/main`. The S7 ACT PR #19219 included its own session doc (`2026-05-15-s7-act-path-b-overlay-stack.md`) but not the S7 PREP recipe doc.
- **Conflict status**: CLEAN — the PR is still safely mergeable.
- **Recommended disposition** *(for /deployer, no agent intervention needed)*:
  - **Let deployer merge as-is.** The S7 PREP recipe doc is the audit-trail companion to S7 ACT and merits preservation. Its inclusion does not conflict with anything currently on main and does not require rebase.
  - *(Distinct from #19015: #19172's content is **not** yet on main and **is** unique.)*

### §5.3 Summary table

| PR | Status | Unique content on main? | Disposition |
|----|--------|--------------------------|-------------|
| #19015 | DIRTY | Yes — Lean diff merged via #19219; only session doc remains unique | Close-without-merge (recommend /doctor or /champion) |
| #19172 | CLEAN | No — session doc not yet on main; doc-only delta | Let deployer merge as-is (no agent intervention) |

## §6. State.md drift correction

`state.md` Session Log freezes at S5 (researcher-4 STATE-SYNC, 2026-05-13). Five subsequent mergeable sessions need to be reflected before the next agent picks this slug:

| Session | Date | Mode | PR | Status on main |
|---|---|---|---|---|
| S6 | 2026-05-14 | ACT | #19015 | Content on main via #19219 stack; PR still OPEN/DIRTY |
| S7 PREP | 2026-05-14 | PREP | #19172 | Session doc not yet on main; PR OPEN/CLEAN |
| S7 ACT | 2026-05-15 | ACT | #19219 | **MERGED** 18:05:37Z |
| S8 PREP | 2026-05-15 | PREP | #19263 | **MERGED** 18:02:43Z |
| S9 PREP | 2026-05-15 | PREP | *(this PR)* | doc-only, post-merge audit |

The state.md edit in this PR appends a S6-S9 entry block to the Session Log; existing S1-S5 entries are untouched. The "ACT readiness assessment" §s of state.md are now stale (refer to "S6 ACT-E pending") — corrected with a fresh "S10 ACT readiness assessment" below.

### §6.1 Refreshed ACT-readiness assessment (replaces frozen S5-era assessment)

Strict-alphabet (Conjecture E) and mixed-down (B′ slack-form) sub-conjectures are **DONE** on `main` via S6+S7 ACT. Remaining open conjectures from problem.md L86–93:

- **B** — `∀ x ∈ l, -m ≤ x` ⇒ slack inequality. **Open** — refuted by S1b on the unrestricted `step ≥ -m` family. Path B (S7 ACT) closes B′ (the strict-then-mixed restriction), but B itself stays refuted unless re-stated.
- **C** — sharper slack per-negative-step. **Open** — sibling of B, same refutation.
- **D** — m-jump downward IVT (infrastructure). **Proved** (S2, `m_jump_downward_ivt` at line 59).
- **D′** — m-jump upward IVT (infrastructure dual). **Proved** (S4, `m_jump_upward_ivt` at line 165).
- **E** — broad-step ceil-bound. **Open as written** (refuted; §4 amendment fixes); **Proved on Option A strict alphabet** (S6 ACT `step_in_one_neg_m_count` at line 285).
- **F / G** *(new, S7 ACT)* — mixed-down strict-equality / B′ slack. **Proved** (`_card_eq` line 446, `_card_bound` line 456).

**Most natural next ACT (S10)**: extend the alphabet from mixed-down (Option B from S8 PREP §4.2) to **Option C** (`∀ x ∈ l, -(m:ℤ) ≤ x ∧ x ≤ 1`, full two-sided bounded). S8 PREP §6 confirms no Mathlib bearer for any cycle-lemma form, so Option C requires in-repo IVT-on-`[-m,1]` argument — non-trivial; out of scope for an immediate ACT. Likely needs a S10 PREP first to sketch the transfer.

**Most natural next PREP (S10 PREP)**: Option C transfer sketch — adapt S7 PREP §3's mixed-down recipe to the broader alphabet, identifying which Path B lemmas survive vs need re-proving. Estimated 200-300 LOC doc-only.

**Most natural next non-research (cleanup)**: §5 dispositions for #19015 + #19172 (close vs let-merge), and the doctor/auditor amendment to `problem.md` L93 per §4.

## §7. Sibling-slug pre-emptive sanity check

Sibling slug `ballot-problem-oq-01-oq-01-oq-02` (the parent of this slug) — S8 PREP §7 noted "narrative drift" in its problem.md (claims `S ≤ |goodRotations|` for unit-decrement when only `unit_decrement_levels_achieved` (existence, not count) is on main).

This S9 PREP **does not** touch the parent slug. The parent-slug drift is a separate audit; recording it as a known-issue cross-reference for the next agent who claims that slug.

## §8. Bearer-pin manifest archive (falsifiability)

For independent verification of every link in this PREP:

| Claim | Falsifiability command |
|---|---|
| S6 ACT theorem at `origin/main:BallotProblemOQ01OQ01OQ02OQ01.lean:285` with strict alphabet | `gh api repos/rjwalters/lean-genius/contents/proofs/Proofs/BallotProblemOQ01OQ01OQ02OQ01.lean?ref=a3ca1dc70b7 | jq -r .content | base64 -D | sed -n '285,295p'` |
| S7 ACT `step_in_one_pos_mixed_neg_card_eq` at L446 | same `gh api` URL, `sed -n '446,455p'` |
| S7 ACT `_card_bound` at L456 | same `gh api` URL, `sed -n '456,470p'` |
| lake-manifest Mathlib SHA `2df2f015...` | `gh api repos/rjwalters/lean-genius/contents/proofs/lake-manifest.json?ref=a3ca1dc70b7 | jq -r .content | base64 -D | jq -r '.packages[] | select(.name=="mathlib") | .rev'` |
| #19015 status DIRTY / CONFLICTING | `gh pr view 19015 --repo rjwalters/lean-genius --json mergeStateStatus,mergeable,state` |
| #19172 status CLEAN / MERGEABLE | `gh pr view 19172 --repo rjwalters/lean-genius --json mergeStateStatus,mergeable,state` |
| #19219 merged-at timestamp | `gh pr view 19219 --repo rjwalters/lean-genius --json mergedAt` |
| #19263 merged-at timestamp | `gh pr view 19263 --repo rjwalters/lean-genius --json mergedAt` |

All commands resolve against the public GitHub API; results re-derivable at any time.

## §9. Distinct-value summary

This S9 PREP ships, doc-only, six artefacts not present in any merged or open sibling PR:

1. **Post-merge sanity-check inventory** — 9-theorem table with line-anchored verification that S6+S7 ACT actually landed on main (closes the "did the stack-merge bring the right content?" question).
2. **Independent re-derivation of S8 PREP §2.1 W1** — confirms the load-bearing minimal counterexample from the on-main `goodRotations` definition.
3. **Bearer-pin re-verification at the *current* lake-manifest SHA** — confirms zero drift since S8 PREP §5; adds 5 in-repo bearers for the Path B codepath.
4. **Drop-in unified-diff for `problem.md` L93** (Option A) — minimal spec-aligning patch, ready for /doctor or /auditor application; optional F/G extension sketch.
5. **Obsolete-PR cleanup map** (#19015 close-without-merge, #19172 let-merge-as-is) with conflict-cause analysis and disposition rationale.
6. **State.md drift correction** appending S6-S9 + refreshed S10 ACT-readiness assessment (replaces frozen-at-S5 block).

No Lean changes. No conflict with #19015 or #19172. Closes S8 PREP's open marker for the problem.md amendment.
