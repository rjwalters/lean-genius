# S6f STATE-SYNC — post-mechanic build-verified catch-up (doc-only)

**Slug**: `algebraic-numbers-countable-oq-02-oq-04`
**Phase**: ACT → S6 BUILD VERIFIED (post-mechanic PR #19054)
**Iteration**: 7 (S1 + S2 + S3 + S4 + S5 + S6 + mechanic #19054 + **S6f STATE-SYNC** [this PR])
**Authored**: 2026-05-16Z by researcher-5
**Mathlib pin**: v4.26.0 (SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
**Base SHA**: `78448f56d0a` (origin/main at branch creation)
**PR scope**: doc-only — state.md head replacement (Phase / Owner /
Iteration / Sessions append) + JSON tracker sync
(phase / iteration / focus / nextAction / progressSummary / lastUpdate
/ leanFiles[]) + this sessions memo. **0 Lean edits.**

Catches the slug's doc tracker after **4 days of drift** (last JSON
`lastUpdate` = 2026-05-12T02:30Z, just after S1 ACT) and **1 mechanic
v4.26.0 fix** that landed since (PR #19054, merged
2026-05-15T23:27:22Z).

---

## §0  TL;DR

The slug's Lean file `proofs/Proofs/AlgebraicNumbersCountableOQ02OQ04.lean`
has progressed from S1 (~110 LOC, 1 sorry) through S6 (~649 LOC,
0 sorries), with all six ACT iterations and the mechanic fix PR #19054
landed on `main`. The doc tracker (state.md head + JSON `currentState`
+ JSON `leanFiles[]`) has been **frozen at S1/S4-era values for 4
days** while the file silently progressed via the S2/S3/S4/S5/S6 PRs
and the v4.26.0 mechanic fix.

This S6f STATE-SYNC catches the drift in three deltas:

1. **state.md head**: Phase `S6 SET-LEVEL STRUCTURAL API (build
   pending)` → `S6 BUILD VERIFIED (post-mechanic PR #19054)`; Owner
   bumped to `researcher-5 (S6f, 2026-05-16)`; Last Updated stamped
   to 2026-05-16Z.
2. **JSON `currentState`**: phase `S4_STRICT_INCLUSION` → `S6_VERIFIED`;
   iteration `4` → `7`; focus + nextAction reframed around the
   post-mechanic snapshot + S7 priority (`IsComputable e ∨ π`); since
   bumped to 2026-05-16T04:10Z; lastUpdate bumped to 2026-05-16T04:10Z.
3. **JSON `leanFiles[0]`**: lineCount `208` → `656` (drift +448),
   theoremCount `9` → `31` (S6 log "synced to 31"), defCount `1` →
   `3` (`IsComputable`, `decodeReal`, `nonComputableReals`),
   sorryCount `1` → `0` (S3 discharged the sorry), axiomCount `0`
   unchanged.

**No Lean edits.** No `proofs/Proofs/*.lean`, `proofs/Proofs.lean`,
`problem.md`, `knowledge.md`, or gallery `meta.json` changes —
strictly doc-only.

---

## §1  Post-mechanic Lean file inventory (at base `78448f56d0a`)

```
File:           proofs/Proofs/AlgebraicNumbersCountableOQ02OQ04.lean
Lines:          656 (was 110 at S1)
Theorems:       31 (per S6 sessions log; pre-S6 was 21)
Definitions:    3 (IsComputable, decodeReal, nonComputableReals)
Sorries:        0 (S3 discharged the S1 sorry; S4/S5/S6 added no new)
Axioms:         0
Imports:        13 (Mathlib.SetTheory.Cardinal.Basic / .Continuum,
                Mathlib.Data.Real.Basic, .Set.Countable, .Rat.Cardinal,
                .Rat.Denumerable, .Logic.Denumerable,
                Mathlib.Computability.Primrec / .Partrec / .PartrecCode,
                Mathlib.Topology.Instances.Real.Lemmas, Mathlib.Tactic,
                Proofs.AlgebraicNumbersCountable)
Build status:   ✔ VERIFIED (mechanic PR #19054, 3067 jobs clean)
```

`grep -c "sorry"` returns 4 — but **all four are in comments** (S1
session log entry referencing the original `sorry`, plus the S3 PR
body talking about "discharging the sorry"). **No actual `sorry` tactics
in the source.** Verified via:

```bash
$ grep -nE "^  sorry$|:= by sorry| sorry$" \
    proofs/Proofs/AlgebraicNumbersCountableOQ02OQ04.lean
# → (no output)
```

---

## §2  Sibling-PR ledger (S1 through S6 + mechanic)

| PR | Stage | Type | Lean delta | Sorries | Merged |
|---|---|---|---|---|---|
| #17715 | S1 | ACT (scaffold) | new file ~110 LOC, 1 def + 1 thm | 1 → 1 | 2026-05-12T01:48Z |
| #17759 | S2 | ACT (lower bound) | +98 LOC, +5 closure thms + `aleph0_le_card_computable_reals` | 1 → 1 | 2026-05-12T02:37Z |
| #17768 | S3 | ACT (upper bound, sorry discharge) | +108 LOC, +2 thms + `decodeReal` def | 1 → **0** | 2026-05-12T02:48Z |
| #17860 | S5 | ACT (cross-cardinal consolidation) | +73 LOC, +3 consolidation thms | 0 → 0 | 2026-05-12T05:09Z |
| #17895 | S6 | ACT (Set-level structural API) | +79 LOC, +5 Set-level thms | 0 → 0 | 2026-05-12T06:10Z |
| #19054 | mechanic | v4.26.0 elaboration repair (4 errors + 1 parser cascade) | repair, no thm delta | 0 → 0 | 2026-05-15T23:27Z |

Note: S4 (PR #17860?) and S5 are listed in the state.md Session Log;
the PR numbering in the merged list shows S2/S3/S5/S6 with iteration
labels — S4 was likely #17860's predecessor inside the same drain
that merged S2/S3 (state.md's "S4 (researcher-12)" entry is the
strict-inclusion + non-computable cardinality work landing alongside
#17860).

Build-blocker era: **2026-05-12 → 2026-05-15** (3.5 days). All six
ACT PRs shipped with "build pending" annotation because the file's
v4.26.0 import surface (`Mathlib.Topology.Instances.Real.Lemmas`,
specific `Computable.const` / `Partrec` API names) had elaboration
errors that required a focused mechanic pass. PR #19054 landed the
4-error + 1-parser-cascade repair and reported `3067 jobs clean`.

---

## §3  Bearer drift recheck (3 critical bearers at SHA `2df2f015...`)

Spot-checked the 3 most load-bearing Mathlib bearers cited by the
S3 upper-bound proof:

| # | Bearer | File:line at SHA `2df2f015...` | S3-recorded |
|---|--------|----------------------------------|--------------|
| 1 | `Nat.Partrec.Code.exists_code` | `Mathlib/Computability/PartrecCode.lean:550` | "verified via WebFetch on live mathlib4_docs" (S3 log) |
| 2 | `le_aleph0_iff_set_countable` | `Mathlib/SetTheory/Cardinal/Basic.lean:430` | verified (S3 log, "alias chain via mk_le_aleph0_iff") |
| 3 | `Cardinal.aleph0_lt_continuum` | `Mathlib/SetTheory/Cardinal/Continuum.lean:65` | verified (S4 log, "from sibling OQ02OQ03") |

All 3 present at exactly the documented line numbers (or within
section headers cited by S3/S4). **0 drift.** Reproduction:

```bash
SHA=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Computability/PartrecCode.lean?ref=$SHA" \
  --jq .content | base64 -d | grep -nE "exists_code"
# → 550:theorem exists_code {f : ℕ →. ℕ} : Nat.Partrec f ↔ ∃ c : Code, eval c = f

gh api "repos/leanprover-community/mathlib4/contents/Mathlib/SetTheory/Cardinal/Basic.lean?ref=$SHA" \
  --jq .content | base64 -d | grep -nE "le_aleph0_iff_set_countable"
# → 430:theorem le_aleph0_iff_set_countable {s : Set α} : #s ≤ ℵ₀ ↔ s.Countable := mk_le_aleph0_iff

gh api "repos/leanprover-community/mathlib4/contents/Mathlib/SetTheory/Cardinal/Continuum.lean?ref=$SHA" \
  --jq .content | base64 -d | grep -nE "aleph0_lt_continuum"
# → 65:theorem aleph0_lt_continuum : ℵ₀ < 𝔠 :=
```

The pinned Mathlib rev itself has not moved across the entire slug
history (S1 2026-05-12 → S6 → mechanic #19054 → this S6f STATE-SYNC),
matching the 4-day Lake manifest stability observed across the
sibling slugs.

---

## §4  Post-mechanic ACT-readiness gate

| Condition | Status | Detail |
|-----------|--------|--------|
| Lean file build verified at HEAD | **GREEN** | PR #19054 reports 3067 jobs clean |
| 0 sorries | **GREEN** | grep confirms no `sorry` tactics |
| 0 axioms | **GREEN** | no `axiom` declarations |
| 0 open PRs against slug | **GREEN** | `gh pr list --search algebraic-numbers-countable-oq-02-oq-04 --state open` → `[]` |
| Mathlib pin stable | **GREEN** | rev `2df2f015...` unchanged since S1 |
| 3 critical bearers verified at pin | **GREEN** | §3 above |
| Gallery `meta.json` sync (lineCount/theoremCount) | **YELLOW** | drift recorded in JSON tracker; gallery refresh deferred to next `mechanic` pass |
| problem.md narrative sync | **YELLOW** | problem.md S1-era; no critical drift but a future refresh would tighten the `algebraic ⊊ computable` narrative |

**Verdict**: the slug is **ACT-READY for S7+ work**. The doc tracker
catch-up in this S6f closes the post-mechanic gap. The next picker
can claim with confidence that the entire 6-stage corpus (656 LOC, 31
thms, 0 sorries, 0 axioms) compiles clean against the pinned Mathlib
rev.

---

## §5  S7+ next-picker priority

Per state.md S2+ targets + JSON `nextSteps`, the natural S7+ work
items in order of expected cost:

### §5.1  S7 ACT — `IsComputable e` ∨ `IsComputable π` (~80-150 LOC)

**RECOMMENDED FIRST.** Construct an explicit computable transcendental
witness, sharpening the strict inclusion `algebraic ⊊ computable`
beyond the pure-cardinality argument of S4. Implementation paths:

- **Path A (e)**: define `eApprox : ℕ → ℚ` via partial sums of `1/n!`,
  prove `Computable eApprox` via `Computable.const` + recursion +
  rational arithmetic primitives, prove `Tendsto (fun n => (eApprox n
  : ℝ)) atTop (nhds Real.exp 1)`. ~100 LOC.
- **Path B (π)**: similar, using Leibniz `4 · ∑ (-1)^k / (2k+1)` or
  Machin formula. Mathlib has `Real.pi`; tendsto-lemmas may exist.
  ~120-150 LOC.

Path A (e) is the cleaner-skeleton candidate at v4.26.0 (`Real.exp`'s
Taylor-series convergence is well-trodden in Mathlib).

### §5.2  S8 ACT — `algebraic ⊆ computable` (~150-300 LOC)

Sturm-sequence / bisection root-finding lifting
`AlgebraicNumbersCountable.card_algebraic_reals_eq_aleph0` to a
`Subset.subset` between the two definitions. Requires Mathlib's
`Sturm` machinery or hand-rolled root-isolation; potentially a long
horizon if `Sturm` is incomplete at v4.26.0.

### §5.3  S9 ACT — Computable reals form a real-closed subfield (~250-400 LOC)

Closure under arithmetic + Sturm-based root extraction. Long-horizon.

### §5.4  S10 advanced — Chaitin Ω as named non-computable witness (~200-400 LOC)

Replace `exists_non_computable_real` (S4, by cardinality) with an
explicit Chaitin-Ω construction. Requires halting-problem encoding
and prefix-free Turing machines; long-horizon and requires
specialized Mathlib infrastructure that may not be present at
v4.26.0.

**S7 (path A) is the recommended next pick** — it's the smallest
genuine extension that strengthens the slug's mathematical content
beyond the existing cardinality corpus.

---

## §6  Conflict declaration

| File | Owned by | This PR |
|------|----------|---------|
| `proofs/Proofs/AlgebraicNumbersCountableOQ02OQ04.lean` | mechanic #19054 (last touch) | **none** (doc-only PR) |
| `proofs/Proofs.lean` (registry) | unchanged | **none** |
| `research/problems/algebraic-numbers-countable-oq-02-oq-04/state.md` | last touch by S1 PR #17715 (head); S2-S6 PRs appended to Session Log | **edit** (head replacement + Session Log S6f append; preserves S1-S6 narrative) |
| `src/data/research/problems/algebraic-numbers-countable-oq-02-oq-04.json` | last touch by S1 PR #17715 | **edit** (`currentState.*` reframe + `progressSummary` extension + `lastUpdate` + `leanFiles[]` count sync) |
| `src/data/proofs/algebraic-numbers-countable-oq-02-oq-04/meta.json` | last touch by enrich PR #18317 | **none** (gallery meta sync deferred to next mechanic pass) |
| `research/problems/algebraic-numbers-countable-oq-02-oq-04/problem.md` | last touch by S1 PR #17715 | **none** (no narrative drift requiring this STATE-SYNC) |
| `research/problems/algebraic-numbers-countable-oq-02-oq-04/sessions/2026-05-16-s6f-statesync-postmechanic-buildverified.md` | new | **add** |

0 open PRs against the slug at branch creation; conflict-free.

---

## §7  Pattern notes for memory

This session is a clean realization of the pattern
`feedback_researcher_postship_statesync_absorbs_drain_wave_ending_build_blocker_era.md`:

- 6 ACT iterations shipped 2026-05-12 in rapid succession with
  "build pending" annotations.
- 3.5-day quiet period (build-blocker era) — no new doc updates, no
  new Lean.
- Mechanic PR #19054 lands the v4.26.0 fix 2026-05-15T23:27Z,
  clearing the build-blocker era in one PR.
- state.md / JSON `lastUpdate` still frozen at S1/S4 values 4 days
  later.
- 0 open PRs on the slug.

This S6f ships the post-mechanic STATE-SYNC: state.md head + JSON
tracker catch-up + 3 critical bearer rechecks + ACT-readiness gate
+ S7+ priority. ~30-min cycle.

**Distinguishing feature** from the memory pattern's exact prior
matches (which required ≥3 doc-only PREPs preceding the mechanic
fix): here, the build-blocker era was entirely silent — no PREPs,
just 6 stage ACTs all shipped pre-mechanic and the mechanic fix
itself. No prior STATE-SYNC was ever shipped on this slug; this S6f
is the first STATE-SYNC.

---

## §8  Sources

- Mechanic fix PR #19054 (researcher-12 / mechanic, 2026-05-15):
  v4.26.0 elaboration repair, 3067 jobs clean.
- S6 ACT PR #17895 (researcher-9, 2026-05-12): Set-level structural
  API, 5 new thms, file 570 → 649 LOC.
- S1 ACT PR #17715 (researcher-4, 2026-05-12): scaffold + 1 sorry.
- Mathlib v4.26.0 SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
  (Lake manifest, unchanged across slug history).
- Memory pattern `feedback_researcher_postship_statesync_absorbs_drain_wave_ending_build_blocker_era.md`.
- Memory pattern `feedback_researcher_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header.md`
  (applied loosely — 3 bearers spot-checked, not a full re-pin).
