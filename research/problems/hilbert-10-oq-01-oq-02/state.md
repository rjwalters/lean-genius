# Current State

**Phase**: ACT
**Since**: 2026-05-15T22:58:32Z (iter 26a merged in PR #19117)
**Iteration**: 27 (iter 26a MERGED PR #19117; iter 27 = next picker's slot; S29 STATE-SYNC doc-only sync below — iter 27 has not yet fired over T+15d)
**Last Updated**: 2026-05-31 (researcher-1, S29 STATE-SYNC — T+15d temporal drift refresh + bearer pin recheck + iter 27e null-content promotion to anti-candidate)

## Session 29 — S29 STATE-SYNC (researcher-1, 2026-05-31, T+15d)

**Goal**: doc-only refresh after a +15d window in which iter 27 has not fired.
The slug's mathematical surface is in a stable holding pattern (iter 26a merged
2026-05-15; no file edits since); the picker's task today is to verify that
the bearer pin, the open-PR hygiene, and the candidate matrix remain valid at
T+15d so future pickers don't inherit stale signals.

**Findings**:

| Surface | Pre-S29 | S29 verification | Δ |
|---|---|---|---|
| Mathlib pin (`proofs/lake-manifest.json`) | `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0) | UNCHANGED — direct file read | = |
| Bearer 1: `Mathlib/Algebra/Order/Ring/Basic.lean` @ pin | size=9086 sha=aa9e6f80679196767a86ed41af66b7703aa57359 (S28 §2) | size=9086 sha=aa9e6f80679196767a86ed41af66b7703aa57359 | = (byte-stable; content-addressed) |
| Bearer 2: `Mathlib/Data/Finset/Dedup.lean` @ pin | size=6020 sha=05133e2c8c5718337eeca546abf51a3d28822672 | size=6020 sha=05133e2c8c5718337eeca546abf51a3d28822672 | = |
| `proofs/Proofs/Hilbert10OQ01OQ02.lean` LOC | 3082 | 3082 (`wc -l`) | = |
| File git activity since 2026-05-16 | n/a | 0 commits | = |
| Open PRs on slug | 0 (S28 §1.5) | 0 (`gh pr list` empty) | = |
| ACT-readiness gate (10 items, S28 §5) | 10/10 GREEN | 10/10 GREEN | = |

All seven surfaces unchanged over T+15d. **No regression, no drift.**

**Iter 27e re-survey (formally null content)**:

S28 §3.1 classified iter 27e as "low leverage" but kept it as a viable candidate.
S29 sharpens the verdict: iter 27e is **formally NULL content**, not just low
leverage. Argument:

1. **Class-congruence theorems already exist**:
   `existentialUniversalDefinition_iff_of_pred_iff` (Σ₂, line 437),
   `universalExistentialDefinition_iff_of_pred_iff` (Π₂, line 379),
   `diophantineDefinition_iff_of_pred_iff` (Σ₁, line 399),
   `coDiophantineDefinition_iff_of_pred_iff` (Π₁, line 417). No
   class-congruence "sharpening" is missing.

2. **Trivial-set iff-form bundling is semantically vacuous**:
   The four trivial-set Σ₂/Π₂ facts (Part VIII.6 lines 591-629) are
   `empty_isUniversalExistentialDefinition`, `universe_isUniversalExistentialDefinition`,
   `empty_isExistentialUniversalDefinition`, `universe_isExistentialUniversalDefinition`.
   An iff-form like "`Σ₂(∅) ↔ Π₂(univ)`" between TWO DIFFERENT subsets where
   both sides are provable is just `True ↔ True` — no content. The actual
   useful iff form `Σ₂(S) ↔ Π₂(¬S)` for arbitrary `S` is iter 5's
   `existentialUniversal_iff_universalExistential_complement` — already on file.

3. **Verdict**: promote iter 27e from "low-leverage candidate" to **ANTI-CANDIDATE**
   alongside 27b (level-2 separation cells, anti-axiom), 27c (close stale PRs,
   NO-OP), 27d (Daans 2021 refinement, anti-axiom-policy).

**Picker matrix (post-S29)**:

| ID | Description | Status |
|---|---|---|
| 27a | Σ₂(ℤ) attack via Koenigsmann lift + complement-collapse against `IntegersAreExistentialUniversalOverQ` | ✅ **SOLE forward candidate** — high leverage, high risk, multi-cycle ACT budget |
| 27b | Close any of the four un-closed level-2 cells (Σ₂ ¬, Π₂ ¬, Σ₂\\Π₂, Π₂\\Σ₂) | 🚫 anti-candidate (would settle the slug's central OPEN question or collapse Σ₂=Π₂) |
| 27c | Close stale CONFLICTING stack PRs (#17602 + #17552 + #18997) | 🚫 anti-candidate (NO-OP — all already CLOSED) |
| 27d | Daans 2021 10-quantifier reduction as a refinement axiom | 🚫 anti-candidate (anti-axiom-policy) |
| 27e | Symmetric trivial-set iff dualities + class-congruence "sharpening" | 🚫 **anti-candidate (NEW at S29, formally null)** |

**Honest implication for the next picker**: the only forward-motion candidate
for this slug is iter 27a, a multi-cycle Σ₂(ℤ) attack on the central OPEN
question. Doc-only STATE-SYNC iterations like S28/S29 are the only zero-risk
available moves; they remain valuable for keeping the tracker fresh and the
bearer pin spot-checked, but they do not advance the mathematical content.
Future ACT pickers who pull iter 27 should either:

- (a) commit to a multi-cycle 27a PREP+ACT pair (high leverage, requires
  reading Koenigsmann 2016 in detail and identifying which sub-step admits a
  Σ₂ upgrade); OR
- (b) ship another doc-only STATE-SYNC if the +Nd window has accumulated drift;
  OR
- (c) release the claim and let a different problem absorb the cycle.

**Deliverables (this PR, doc-only — no Lean / no gallery meta / no problem.md /
no knowledge.md body edits)**:

1. **Canonical JSON** (`src/data/research/problems/<slug>.json`):
   `knowledge.progressSummary` prepend with S29 narrative; `lastUpdate`
   2026-05-16T03:30:00Z → 2026-05-31T04:00:00Z. `currentState.*` carried
   forward verbatim — no underlying condition has changed.
2. **state.md head**: this Session 29 prepend.
3. **NEW session memo**:
   `sessions/2026-05-31-s29-statesync-t15d-bearer-recheck.md`.

**Out of scope (deferred)**:

- Gallery `meta.json` numerics — file unchanged, no drift.
- `currentState.{phase, since, iteration, focus, blockers, nextAction,
  attemptCounts}` — S28 already synced these correctly; carry-forward.
- `.knowledge.{insights, builtItems, mathlibGaps, nextSteps}[]` — S28 already
  refreshed these.
- Iter 27a PREP draft — declined for this cycle; doc-only S29 is the
  proportionate iteration today.
- `pnpm build` — slug-targeted JSON edit.

**Mathlib pin**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0), unchanged.

## Current Focus

S28 STATE-SYNC (2026-05-16, researcher-1, this PR): doc-only absorption
of four residual drift items left behind by S27 STATE-SYNC PR #19379
(MERGED 2026-05-15T20:53 PT), now invisible from `currentState` but
present in adjacent tracker surfaces.

| Drift item | Pre-S28 state | Post-S28 state | File |
|------------|---------------|----------------|------|
| (i) `.knowledge.progressSummary` | "ITERATING (iter 25)" + iter 25 narrative | iter 26a + S27 absorption narrative + iter 27 outlook | `src/data/research/problems/hilbert-10-oq-01-oq-02.json` |
| (ii) `.knowledge.nextSteps[]` | S10.1-S10.5 (decade-old, all done) | Iter 27 candidates + anti-candidates + long-term Koenigsmann discharge | same JSON |
| (iii) `.leanFiles[3]` counts | lineCount 1260 / theoremCount 54 / defCount 12 | 3082 / 85 / 15 | same JSON |
| (iv) `meta.json` Mathlib import + count | `Mathlib.Algebra.Order.Ring.Lemmas` (dropped at v4.26.0) in `leanFile.imports[]` and `mathlibDependencies[mul_self_nonneg].module`; `definitionCount = 16` (actual 15); `Mathlib.Tactic.Ring` (line 84) missing from imports | replaced with `Mathlib.Algebra.Order.Ring.Basic` (per mechanic 4-kit PR #19137); `definitionCount = 15`; `Mathlib.Tactic.Ring` added | `src/data/proofs/hilbert-10-oq-01-oq-02/meta.json` |
| (v) §"Open PR hygiene" below | "Sole remaining OPEN PR: #17602" | #17602 now CLOSED — zero open PRs on slug | this `state.md` |

Iter 27 next picker's slot inherits ACT-readiness gate **10/10 GREEN**
from S27 (Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` v4.26.0
unchanged; 18-bearer drift recheck = 0 events since Session 26;
no open PRs on slug). See `sessions/2026-05-16-s28-statesync-knowledge-subtree-and-meta-drift.md`
for the full drift inventory and per-item verification.

### Drain-wave summary (historical from S27 STATE-SYNC PR #19379)

| PR     | Drain-wave merge time     | Effect on this slug                                                                            |
|--------|---------------------------|------------------------------------------------------------------------------------------------|
| #19137 | 2026-05-15T22:57:42Z      | mechanic v4.26.0 4-kit — drops obsolete `Mathlib.Algebra.Order.Ring.Lemmas` barrel import. Unblocks Docker build for the entire iter 22-26 chain in one shot. |
| #19117 | 2026-05-15T22:58:32Z      | research iter 26a Finset transport — adds Part VIII.31 (`sigma2_unionFinset_…`) + Part VIII.32 (`pi2_intersectionFinset_…`). Completes the Finset-arity row of the level-2 Σ₂/Π₂ closure grid. |
| #19344 | 2026-05-16T01:08:47Z      | `fix(meta)` — `meta.json` `lineCount` 2652 → 3082, syncing tracker to iter 25 + iter 26a file growth. |
| #18997 | (CLOSED, not merged)      | STATE-SYNC retcon — superseded by this S27 STATE-SYNC (#18997's edits would now be stale: it described iter 25 build-pending; reality is iter 26a merged + parent regression cleared). |

### Iter 26a content (now on `main`, retroactively build-verified)

Two new theorems in two clean sections (Part VIII.31 + VIII.32, lines
2657-2782 on `main` SHA `8a3cda556b6`), all axiom-free, using ONLY iter
25's list closures (Part VIII.29/30) plus iter 4 Σ₂/Π₂ class congruence
and the standard `Finset.mem_toList` bridge. **Zero new Mathlib
imports, zero new helper lemmas.** Direct mirror of iter 22's
`sigma2_intersectionFinset_isExistentialUniversalDefinition` and
`pi2_unionFinset_isUniversalExistentialDefinition`, swapping the
list-lift target from iter 21 (Part VIII.23/24) to iter 25
(Part VIII.29/30).

- `sigma2_unionFinset_isExistentialUniversalDefinition (s : Finset RatSubset)
  (h : ∀ S ∈ s, IsExistentialUniversalDefinition S) :
  IsExistentialUniversalDefinition (fun q => ∃ S ∈ s, S q)` — Σ₂ closed
  under arbitrary Finset-indexed ∪ of Σ₂-definable subsets. Transports
  iter 25's `sigma2_unionList_isExistentialUniversalDefinition` via
  `Finset.mem_toList.mp`/`.mpr` + iter 4 Σ₂ class congruence.
- `pi2_intersectionFinset_isUniversalExistentialDefinition (s : Finset RatSubset)
  (h : ∀ S ∈ s, IsUniversalExistentialDefinition S) :
  IsUniversalExistentialDefinition (fun q => ∀ S ∈ s, S q)` — Π₂ closed
  under arbitrary Finset-indexed ∩ of Π₂-definable subsets. Symmetric
  Finset transport of iter 25's
  `pi2_intersectionList_isUniversalExistentialDefinition`.

### Closure grid — complete at level 2 for the four established cells

| Class | binary ∪    | binary ∩    | list ∪      | list ∩      | finset ∪      | finset ∩      |
|-------|-------------|-------------|-------------|-------------|---------------|---------------|
| Σ₁    | iter 9      | iter 12     | iter 15     | iter 14     | iter 17       | iter 17       |
| Π₁    | iter 13     | iter 9      | iter 14     | iter 15     | iter 17       | iter 17       |
| Σ₂    | iter 24a    | iter 20     | iter 25     | iter 21     | **iter 26a**  | iter 22       |
| Π₂    | iter 20     | iter 24a    | iter 21     | iter 25     | iter 22       | **iter 26a**  |

Every finite-arity (binary / list / Finset) union/intersection of
arbitrary Σ₂/Π₂-definable subsets now stays in the same class. The grid
is **complete** at level 2 for the four established cells (Σ₂ ∪, Σ₂ ∩,
Π₂ ∪, Π₂ ∩). The four un-closed cells (Σ₂ ¬, Π₂ ¬, Σ₂ \ Π₂ separation,
Π₂ \ Σ₂ separation) remain OPEN — their closure would collapse Σ₂ = Π₂
or settle the level-2 open question, and so they are **NOT viable
iter-27 ACT targets** under the slug's anti-axiom-policy.

### Build status (post-drain-wave)

**Parent v4.26.0 regression CLEARED**: import line 77 on `main` reads
`import Mathlib.Algebra.Order.Ring.Basic` (the merged-mechanic 4-kit's
replacement for the removed `…Ring.Lemmas` barrel at pinned rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`). The entire iter 22-26
build-pending chain (PRs #18107, #18178/#18256, #18659, #18785, #19117)
**retroactively builds** on `main` — no per-iter rebuild required.

### Open PR hygiene (updated S28, 2026-05-16)

**Zero open PRs on slug** (verified at S28 base SHA `cf1cfa085e4`,
2026-05-16T03:18Z probe via `gh api repos/rjwalters/lean-genius/pulls/17602`).
The prior CONFLICTING iter-19 stack PR **#17602** is now `state=closed`
(was OPEN at S27 ship time 2026-05-15T20:53 PT; closed sometime in the
~5h window between S27 merge and S28 claim — doctor / mechanic /
maintainer hygiene close, no merge). PRs #17552 (iter 18 stack) and
#18997 (S25 retcon STATE-SYNC) were already CLOSED at S27 ship time.
The slug-clean signal means iter 27 ACT pickers have no file-orthogonality
constraints when touching `proofs/Proofs/Hilbert10OQ01OQ02.lean`.

### Bearer drift recheck (Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, unchanged)

Re-verified at 2026-05-16T02:25Z against the pinned Mathlib SHA: all 9
bearers used by iter 22-26a (`Finset.mem_toList` at
`Mathlib/Data/Finset/Dedup.lean:171`; `Mathlib.Algebra.Order.Ring.Basic`
present; `…Ring.Lemmas` correctly 404; `Mathlib.Data.Finset.Basic`,
`Mathlib.Algebra.Group.Basic`, `Mathlib.Algebra.GroupWithZero.Basic`,
`Mathlib.Tactic.Linarith`, `Mathlib.Tactic.Ring` all present) and all 9
in-file bearers (Part III iter 3-4 helpers + Part VIII.25-27/29-30/31-32
iter 22/23/25/26a anchors) are stable with zero drift since Session 26
(2026-05-15T01:29Z). Full table in
`sessions/2026-05-15-s27-statesync-iter26a-merged-drain-wave.md` §2.

## Historical Focus (iter 25, MERGED PR #18785, build pending)

Iteration 25 (2026-05-13, researcher-12, this PR): **list-arity versions
of iter 24a's binary Σ₂ ∪ and Π₂ ∩ closures**.

Two new theorems in two clean sections (Part VIII.29 + VIII.30), all
axiom-free, using ONLY iter 24a's binary closures (already on main via
PR #18659) plus iter 5 trivial subsets and iter 4 Σ₂/Π₂ class
congruence. **No new Mathlib imports, no new helper lemmas.**

- `sigma2_unionList_isExistentialUniversalDefinition (l : List RatSubset)
  (h : ∀ S ∈ l, IsExistentialUniversalDefinition S) :
  IsExistentialUniversalDefinition (fun q => ∃ S ∈ l, S q)` — Σ₂ closed
  under finite list ∪. List induction: empty list → `empty_isExistentialUniversalDefinition`
  via Σ₂ class congruence; cons step → iter 24a `sigma2_union_isExistentialUniversalDefinition`
  + iter 4 Σ₂ class congruence + `List.mem_cons` case split.
- `pi2_intersectionList_isUniversalExistentialDefinition (l : List RatSubset)
  (h : ∀ S ∈ l, IsUniversalExistentialDefinition S) :
  IsUniversalExistentialDefinition (fun q => ∀ S ∈ l, S q)` — Π₂ closed
  under finite list ∩. List induction: empty list → `universe_isUniversalExistentialDefinition`
  via Π₂ class congruence; cons step → iter 24a `pi2_intersection_isUniversalExistentialDefinition`
  + iter 4 Π₂ class congruence + `List.mem_cons` case split.

**Significance** — completes the list-arity row of the level-2 Σ₂/Π₂
binary Boolean closure grid:

| Class | binary ∪          | binary ∩          | list ∪              | list ∩              |
|-------|-------------------|-------------------|---------------------|---------------------|
| Σ₁    | iter 9            | iter 12           | iter 15             | iter 14             |
| Π₁    | iter 13           | iter 9            | iter 14             | iter 15             |
| Σ₂    | iter 24a (#18659) | iter 20 (#17628)  | **iter 25 (this)**  | iter 21 (#17676)    |
| Π₂    | iter 20 (#17628)  | iter 24a (#18659) | iter 21 (#17676)    | **iter 25 (this)**  |

After iter 25 lands, every finite list ∪/∩ combination of arbitrary
Σ₂/Π₂-definable subsets stays in the same class — strictly bigger
than iter 14's diagonal transports (which only handled Σ₁/Π₁ inputs
lifted to Σ₂/Π₂ via the trivial inclusions iter 11). Neither Σ₂ nor
Π₂ is (known to be) closed under complement; that would collapse
Σ₂ = Π₂ at level 2 — a level-2 analog of the OPEN level-1 question,
currently OPEN at level 2 as well.

**Orthogonality** to the two open stacked PRs (#17552 iter 18,
#17602 iter 19): those PRs targeted iter-16-based level-2 cells but
sit on a stale stack from before iter 16 PR #17456 was CLOSED on
2026-05-08; iter 25 lifts iter 24a (the live re-implementation of
iter 16 off current main) to list arity. Iter 25 branches cleanly
off **origin/main** at iter 24a's HEAD (PR #18659).

**File status**: 2775 → 2942 lines (+167). Theorems 87 → 89 (+2:
`sigma2_unionList_isExistentialUniversalDefinition`,
`pi2_intersectionList_isUniversalExistentialDefinition`). Defs 15
(unchanged). Axioms 1 (unchanged). Sorries 0 (unchanged). **No new
imports.**

**Build risk**: very low. The two new theorems use only existing
helpers (iter 24a binary closures, iter 5 trivial subsets, iter 4
class congruence) and standard Lean-core list helpers
(`List.mem_cons_self`, `List.mem_cons_of_mem`, `List.mem_cons`). The
proof skeleton is structurally identical to iter 21's
`sigma2_intersectionList_isExistentialUniversalDefinition` and
`pi2_unionList_isUniversalExistentialDefinition` (already CI-verified
on main via PR #17676) — only the binary-closure ingredient is
swapped from iter 20 to iter 24a. Worktree's `proofs/.lake` is the
known recursive self-symlink (per
`feedback_researcher_lake_symlink_broken.md`), so a local Docker
build would re-fresh-clone Mathlib (~30-45 min); CI is the ground
truth, following the slug's iter 14-24a build-pending merge precedent.

---

## Iteration 23 (historical record — merged in PR #18178 / #18256)

Iteration 23 (2026-05-12, researcher-1): **Name the level-2
OPEN question Σ₂(ℤ) as a top-level `Prop` and prove its complement
duality Σ₂(ℤ) ⟺ Π₂(ℚ \ ℤ)**.

Three new declarations in a single small section (Part VIII.27), all
axiom-free, using ONLY existing iter-5 (`existentialUniversal_iff_universalExistential_complement`)
and iter-7 (`universalExistentialDefinition_iff_of_pred_iff`) helpers
plus `koenigsmann_2016_universal`. **No new Mathlib imports.**

- `def IntegersAreExistentialUniversalOverQ` — the level-2 OPEN Σ₂(ℤ)
  question as a named `Prop`, mirroring iter 0's
  `IntegersAreDiophantineOverQ` for the level-1 Σ₁(ℤ) OPEN question.
  Currently OPEN: Koenigsmann places ℤ in Π₂ and Σ₂(ℚ\ℤ) is proved
  by iter 5 duality, but Σ₂(ℤ) itself is not known.
- `theorem integers_existentialUniversal_iff_complement_universalExistential`
  — one-line specialization of iter 5's symmetric Σ₂/Π₂ duality
  at `S := IntSubset`. Gives `Σ₂(ℤ) ⟺ Π₂(ℚ \ ℤ)`, the level-2
  analog of iter 0's `integers_diophantine_iff_complement_codiophantine`.
- `theorem koenigsmann_2016_universal_doubleNeg` — `Π₂(¬¬ ℤ)`
  re-export of Koenigsmann via iter 7's Π₂ doubleNeg invariance.
  Useful when a downstream argument naturally produces `¬¬ IntSubset`
  (e.g. via `Classical.byContradiction` on a Π₁ counter-witness).

**Significance** — completes the *symmetric pair* of complement-dualities
for the two OPEN questions tracked in this file:

| Level | Theorem on `IntSubset`                                                              | Dual question on `NotIntSubset`         | Status        |
|-------|-------------------------------------------------------------------------------------|-----------------------------------------|---------------|
| 1     | `integers_diophantine_iff_complement_codiophantine` (iter 0)                        | `IsCoDiophantineDefinition NotIntSubset` | both OPEN     |
| 2     | `integers_existentialUniversal_iff_complement_universalExistential` (iter 23)        | `IsUniversalExistentialDefinition NotIntSubset` | both OPEN     |

The level-2 row has the asymmetry that the *other* side
(`koenigsmann_implies_complement_existentialUniversal`) is PROVED via
Koenigsmann + iter 5 duality — so the level-2 OPEN content collapses
to the single Σ₂(ℤ) question. At level 1, neither side is currently
known.

**Orthogonality** to the three open stacked PRs (#17456 iter 16,
#17552 iter 18, #17602 iter 19): iter 23 introduces a new top-level
`Prop` and an iff theorem *about `IntSubset` itself*, not about the
generic Σ₂ ∪ / Π₂ ∩ closure cells those PRs target. Names are disjoint
(`IntegersAreExistentialUniversalOverQ`, `integers_existentialUniversal_iff_complement_universalExistential`,
`koenigsmann_2016_universal_doubleNeg` vs the open-PR names
`sigma2_union_*`, `pi2_intersection_*`, etc.). Iter 23 branches
cleanly off **origin/main** at iter 22's HEAD (PR #18107).

**File status**: 2539 → 2652 lines (+113). Theorems 86 → 88 (+2:
`integers_existentialUniversal_iff_complement_universalExistential`,
`koenigsmann_2016_universal_doubleNeg`). Defs 15 → 16 (+1:
`IntegersAreExistentialUniversalOverQ`). Axioms 1 (unchanged). Sorries 0
(unchanged). **No new imports.**

**Build risk**: very low. The two new theorems use only existing
helpers `existentialUniversal_iff_universalExistential_complement`,
`universalExistentialDefinition_iff_of_pred_iff`, plus the
`koenigsmann_2016_universal` axiom. The pattern is identical to
iter 0's `integers_diophantine_iff_complement_codiophantine` (line
260-262), which already typechecks on origin/main — same
def-equality unfolding for `IntegersAreExistentialUniversalOverQ ≡
IsExistentialUniversalDefinition IntSubset` and `NotIntSubset ≡
fun q => ¬ IntSubset q`. Worktree's `proofs/.lake` is the known
recursive self-symlink (per `feedback_researcher_lake_symlink_broken.md`),
so a local Docker build would take 30-45 min; CI is the ground
truth, following the slug's iter 14-22 build-pending merge precedent.

---

## Iteration 17 (historical record below — superseded)

Iteration 17 (2026-05-08, researcher-11): **Finset transport
of the list-indexed Σ₁/Π₁ closures (S11.4 + arbitrary-subset Finset
analogs)**.

Eight new theorems in two clean blocks (Part VIII.19 + Part VIII.20),
all axiom-free and using a single new Mathlib lemma
(`Finset.mem_toList`):

**Part VIII.19 — Finset transport of iter 10's singletons-list
closure (S11.4)**:

- `finUnionFinset_singletons_isDiophantineDefinition (s : Finset Rat)`
  — every `Finset Rat`-indexed finite subset of ℚ is Σ₁-definable,
  via `Finset.mem_toList.symm` + iter 4 congruence + iter 10.
- `finIntersectionFinset_complement_singletons_isCoDiophantineDefinition`
  — Π₁ dual via `not_congr Finset.mem_toList`.
- Two trivial Π₂/Σ₂ corollaries via Σ₁ ⊆ Π₂ and Π₁ ⊆ Σ₂.

**Part VIII.20 — Finset transport of iter 14/15's arbitrary-subset
list closures**:

- `finIntersectionFinset_isDiophantineDefinition` — Σ₁ ∩ over Finset.
- `finUnionFinset_isCoDiophantineDefinition` — Π₁ ∪ over Finset.
- `finUnionFinset_isDiophantineDefinition` — Σ₁ ∪ over Finset.
- `finIntersectionFinset_isCoDiophantineDefinition` — Π₁ ∩ over Finset.

All four arbitrary-subset Finset closures route the iter 14/15 list
witnesses through the membership bridge `∀/∃ S ∈ s, S q ↔ ∀/∃ S ∈
s.toList, S q` (proved via `Finset.mem_toList.mp/mpr`) and the iter 4
class congruence helper.

**Significance**: completes the iter-13 "S11.4" priority and lifts
iter 14/15's list-arity 2×2 closure grid to Finset-arity. The
underlying polynomial witnesses are unchanged from iter 9/12/13/14/15
— only the indexing structure is promoted from `List` to `Finset`.
The 2×2 finite Boolean closure grid for Σ₁/Π₁ over ℚ is now populated
at three arities:

    | Class | binary    | list      | Finset    |
    |-------|-----------|-----------|-----------|
    | Σ₁ ∪ ∩ | iter 9, 12 | iter 14,15| iter 17 |
    | Π₁ ∪ ∩ | iter 13, 9 | iter 14,15| iter 17 |

The OPEN content remains unchanged: it is still the COUNTABLY-INFINITE
union ⋃_{n : ℤ} {n} that requires a UNIFORM Σ₁ witness; iter 17 only
extends the FINITE side.

**File status**: 1904 → 2059 lines (+155). Theorems 69 → 77 (+8).
Definitions 15 (unchanged). Axioms 1 (unchanged). Sorries 0
(unchanged). One new import: `Mathlib.Data.Finset.Basic` for
`Finset.mem_toList`.

**Build risk**: low. `Finset.mem_toList` is a standard Mathlib lemma
(used elsewhere in this repo, e.g., `Hilbert3ScissorsCongruence.lean`).
The 8 new theorems use only `Finset.mem_toList.mp`/`.mpr`/`.symm` plus
`not_congr` (Mathlib core); no new tactics. Worktree's `proofs/.lake`
is a recursive self-symlink (per
`feedback_researcher_lake_symlink_broken.md`), so a local Docker
build would re-fresh-clone Mathlib (~30-45 min). CI is the ground
truth, per the slug's iter 14/15/16 build-pending pattern.

---

(Historical iteration 13 narrative below preserved for context. Iter
14, 15, 16 PRs landed but did not advance the state.md iteration
counter; iter 17 is the next user-visible state advancement after
iter 13's record.)

## Iteration 13 historical record

Iteration 13 (2026-05-08, researcher-12): **Π₁ closed under
binary union (S12.2)** — the missing dual of iter 9's Σ₁-union
closure. Combined with iter 9 (Σ₁ ∪, Π₁ ∩) and iter 12 (Σ₁ ∩), the
**2×2 finite Boolean closure grid** for Σ₁ and Π₁ over ℚ is now
complete:

    | Class | ∪ closure | ∩ closure |
    |-------|-----------|-----------|
    | Σ₁    | iter 9    | iter 12   |
    | Π₁    | iter 13   | iter 9    |

Neither class is (known to be) closed under complement; that would
collapse Σ₁ = Π₁ over ℚ, equivalent to the OPEN question.

**Strategy** (no new Mathlib lemmas, no new imports): chain through

    Π₁(S₁), Π₁(S₂)
      →[iter 5 codiophantine_iff_diophantine_complement]  Σ₁(¬S₁), Σ₁(¬S₂)
      →[iter 12 intersection_isDiophantineDefinition]      Σ₁(¬S₁ ∧ ¬S₂)
      →[iter 4 diophantineDefinition_iff_of_pred_iff
         via constructive de Morgan ¬S₁ ∧ ¬S₂ ↔ ¬(S₁ ∨ S₂)] Σ₁(¬(S₁ ∨ S₂))
      →[iter 5 codiophantine_iff_diophantine_complement]   Π₁(S₁ ∨ S₂)

The "underlying" polynomial witness (after unfolding the iter 5
duality, which is identity on the polynomial family P) is the same
sum-of-squares construction as iter 12:

    P(q, x) = (P₁(q, evenProj x))² + (P₂(q, oddProj x))²

with P_i now interpreted as the Π₁ witness of S_i. The de Morgan
bridge `¬S₁∧¬S₂ ↔ ¬(S₁∨S₂)` is **constructive** (no LEM needed); the
duality steps each use the iter 5 `Classical.byContradiction` move
internally, but no NEW classical reasoning is introduced beyond what
iter 5 already required.

Two new theorems:

1. `union_isCoDiophantineDefinition` — Π₁ closed under binary union
   (main theorem).
2. `union_isExistentialUniversalDefinition` — corollary via Π₁ ⊆ Σ₂.

**Mathlib API surface**: ZERO new lemmas, ZERO new imports. Pure
logical bridging on top of iter 5 (duality), iter 9 (Π₁ class), and
iter 12 (Σ₁ ∩ closure).

**Net new content**: 0 definitions, 2 theorems, 0 axioms, 0 sorries.
**Updated total**: 15 definitions, 61 theorems, 1 axiom, 0 sorries,
1610 lines (was 1495).

## Iteration 12 (2026-05-08, prior researcher-12 PR #17375): **Σ₁ closed under
binary intersection (S11.2)** — the missing dual of iter 9's union
closure. Combined with iter 9, Σ₁ over ℚ is now closed under finite
Boolean combinations using ∪ and ∩ (NOT under complement, which would
collapse Σ₁ = Π₁).

Iter 12 witness: sum-of-squares with variable packing,

    P(q, x) = (P₁(q, evenProj x))² + (P₂(q, oddProj x))²

with `evenProj`, `oddProj`, `interleave` packing infrastructure;
forward direction interleaves witnesses; reverse uses
`mul_self_nonneg` + `linarith` + `mul_eq_zero` over ℚ.
Two main theorems plus three private supporting defs and two private
projection lemmas. Adds 2 Mathlib imports
(`Mathlib.Algebra.Order.Ring.Lemmas` and `Mathlib.Tactic.Linarith`).
Net new (iter 12): 3 defs, 4 thms (2 priv + 2 pub), 0 axioms,
0 sorries; total at iter-12 close: 15 defs, 59 thms, 1 axiom,
0 sorries, 1495 lines.

## Iteration 11 (2026-05-08, prior researcher-12 PR #17338): **Π₁ ⊆ Π₂
via polynomial inversion (S11.1)** — closes the last "diagonal"
containment in the Σ₁/Π₁/Σ₂/Π₂ square not derivable from a
dummy-block argument.

The Π₂ polynomial witness for a Π₁ subset is

    P'(q, y, x) := P(q, y) · x 0 - 1

where `P` is the Π₁ witness. The inversion trick `a ≠ 0 ⟺ ∃ z, a·z = 1`
over ℚ makes `∀ y, ∃ x, P(q, y)·x 0 - 1 = 0` equivalent to
`∀ y, P(q, y) ≠ 0`, i.e., the Π₁ form of `S q`. Path B: uses
`mul_inv_cancel₀` (already imported for S9) and `sub_eq_zero` (S8).

## Iteration 10 (2026-05-08, prior researcher-12 PR #17307): **finite-list closure
(S10.3)** — every FINITE subset of ℚ is Σ₁-definable, and every
complement of a finite subset is Π₁-definable. Direct application of
S9's binary union/intersection closure to a `List Rat` by induction.

Two main theorems plus two trivial Π₂/Σ₂ corollaries:

1. `finUnionList_singletons_isDiophantineDefinition (l : List Rat)` —
   the predicate `fun q : Rat => q ∈ l` is Σ₁-definable. By induction
   on `l`:
   * **Base** (`l = []`): predicate reduces to `False`, covered by S5's
     `empty_isDiophantineDefinition`.
   * **Step** (`l = a :: t`): `q ∈ a :: t` unfolds (via Lean core
     `List.mem_cons`) to `q = a ∨ q ∈ t`. Apply S9's
     `union_isDiophantineDefinition` to the head witness
     `singletonOf_isDiophantineDefinition a` (S8) and the inductive
     hypothesis. Bridge `q ∈ a :: t ↔ q = a ∨ q ∈ t` is closed via
     `diophantineDefinition_iff_of_pred_iff` (S5 logical congruence).
2. `finIntersectionList_complement_singletons_isCoDiophantineDefinition (l : List Rat)`
   — dual statement for the Π₁ class: `fun q : Rat => q ∉ l` is
   Π₁-definable. Same induction structure, with
   `notSingletonOf_isCoDiophantineDefinition` (S8 head) and
   `intersection_isCoDiophantineDefinition` (S9 step).
3. `finUnionList_singletons_isUniversalExistentialDefinition (l : List Rat)`
   — Π₂ corollary via the trivial inclusion Σ₁ ⊆ Π₂.
4. `finIntersectionList_complement_singletons_isExistentialUniversalDefinition (l : List Rat)`
   — Σ₂ corollary via the trivial inclusion Π₁ ⊆ Σ₂.

**Mathlib API surface**: zero new lemmas. Uses only Lean-core
`List.mem_cons` (in the cons case) plus `simp` for the empty-list
equivalence `q ∈ [] ↔ False`. No new imports.

**Net new content**: 0 definitions, 4 theorems, 0 axioms. **Updated
total**: 12 definitions, 54 theorems, 1 axiom, 0 sorries, 1260 lines
(was 1163).

## Sharpening of the OPEN Σ₁ Question (iter 10 update)

S10.3 closes the finite-list induction story explicitly: every FINITE
subset of ℚ is Σ₁-definable; every complement of a FINITE subset is
Π₁-definable. The OPEN Σ₁ question for ℤ ⊂ ℚ is therefore EQUIVALENT
to:

    is the COUNTABLE union ⋃_{n : ℤ} {n} Σ₁-definable in ℚ?

with the precise gap being the lift from finite to countable. Finite
truncations `⋃_{n ∈ [-N, N] ∩ ℤ} {n}` are Σ₁-definable for every finite
`N` (instantiate `finUnionList_singletons_isDiophantineDefinition` at
`l = [(-N : Rat), -(N-1), …, (N : Rat)]`). The OPEN content is
precisely the limit `N → ∞`: a uniform polynomial witness whose
existence is the question.

---

## Iteration 9 (2026-05-08, researcher-9): closure of Σ₁ under
binary union and Π₁ under binary intersection via the **product
polynomial witness**

    P(q, x) = P₁(q, x) · P₂(q, x)

where `P₁` and `P₂` are the witnesses for `S₁` and `S₂` respectively
(both polynomials share the same infinite variable assignment block).

The same product polynomial serves both directions:

* **Union (Σ₁)**: `∃ x, P₁(q,x)·P₂(q,x) = 0  ⟺  (∃ x, P₁(q,x) = 0) ∨
  (∃ x, P₂(q,x) = 0)`. Both directions trivial — for the forward (∨ →
  ∃), pick the existential witness for whichever side holds and use
  `zero_mul` / `mul_zero`; for the reverse (∃ → ∨), apply `mul_eq_zero`
  at the witness.
* **Intersection (Π₁)**: `(∀ x, P₁(q,x)·P₂(q,x) ≠ 0)  ⟺  (∀ x, P₁(q,x) ≠ 0)
  ∧ (∀ x, P₂(q,x) ≠ 0)`. The universal "splits" across the conjunction
  — same `mul_eq_zero` (in its contrapositive form) does the work.

The Mathlib API surface is one new lemma — `mul_eq_zero` over ℚ — and
the elementary `zero_mul` / `mul_zero`. ℚ is a field, hence
`NoZeroDivisors`, so `mul_eq_zero` applies. Adds the import
`Mathlib.Algebra.GroupWithZero.Basic` (the **second** Mathlib import
in this file, after S8's `Mathlib.Algebra.Group.Basic`).

Two main theorems plus four concrete corollaries:

  1. `union_isDiophantineDefinition` — Σ₁ is closed under binary union.
  2. `intersection_isCoDiophantineDefinition` — Π₁ is closed under
     binary intersection.
  3. `singletonPair_isDiophantineDefinition a b` — every PAIR
     `{a, b} ⊂ ℚ` is Σ₁-definable (corollary of #1 applied to two S8
     `singletonOf` witnesses).
  4. `notSingletonPair_isCoDiophantineDefinition a b` — every
     complement-of-pair `ℚ \ {a, b}` is Π₁-definable (corollary of #2).
  5. `singletonPair_isUniversalExistentialDefinition a b` — every PAIR
     `{a, b}` is Π₂-definable (corollary via Σ₁ ⊆ Π₂).
  6. `notSingletonPair_isExistentialUniversalDefinition a b` — every
     complement-of-pair is Σ₂-definable (corollary via Π₁ ⊆ Σ₂).

Net new content: 0 definitions, 6 theorems, 0 axioms.
Updated total: 12 definitions (incl. 4 private), 50 theorems (incl.
4 private), 1 axiom, 0 sorries, 1163 lines (was 999).

## Sharpening of the OPEN Σ₁ Question

The S9 closure theorems make precise the boundary of what S8 + S9
reach. Combining them with finite induction:

    every FINITE subset {a₀, a₁, …, a_k} ⊂ ℚ is Σ₁-definable

(Sketch: by induction on `k`, using S8 `singletonOf_isDiophantineDefinition`
for the base and S9 `union_isDiophantineDefinition` for the step.
This is straightforward but not formalized in this PR — left as S10.3.)

The OPEN Σ₁ question for ℤ ⊂ ℚ is equivalent to the question:

    is the COUNTABLE union ⋃_{n : ℤ} {n} Σ₁-definable in ℚ?

i.e., does there exist a SINGLE polynomial `P(t, x₁, …, x_k) ∈ ℚ[t,x]`
whose rational-solution slices simultaneously witness `t = n` for every
`n : ℤ`. **Finite truncations** `⋃_{n ∈ [-N, N] ∩ ℤ} {n}` are Σ₁-definable
for every finite `N` (corollary of S8 + S9), so the OPEN content is
*precisely the limit `N → ∞`*: a uniform polynomial witness whose
existence is the question.

This is the cleanest restatement of the OPEN Σ₁ question yet:

* The non-uniform "case-by-case" Σ₁-definability of each integer is
  settled (S8): `{n}` is Σ₁ for every `n : ℤ ⊂ ℚ`.
* The non-uniform "any finite collection" Σ₁-definability is settled
  (S9 + induction): `{n₀, n₁, …, n_k}` is Σ₁ for every finite list
  `n₀, n₁, …, n_k : ℤ`.
* The **uniform** Σ₁-definability of all of ℤ is the OPEN question:
  no single polynomial is known to witness `t ∈ ℤ` for all `t : ℚ`.

## Iteration 15 Builds (researcher-12, 2026-05-08)

Focus: **complete the 2×2 closure grid at finite-list arity** by
filling the two remaining cells (Σ₁ list ∪ and Π₁ list ∩) for
ARBITRARY Σ₁/Π₁-definable subsets, paired with the iter 14 cells.

### Part VIII.16 / .17 additions (axiom-free)

- `finUnionList_isDiophantineDefinition (l : List RatSubset)
  (h : ∀ S ∈ l, IsDiophantineDefinition S) :
  IsDiophantineDefinition (fun q => ∃ S ∈ l, S q)` — Σ₁ list ∪ of
  ARBITRARY Σ₁-definable subsets (generalizes iter 10's singleton-only
  `finUnionList_singletons_isDiophantineDefinition`). Empty list:
  `∃ S ∈ [], S q ↔ False`, dispatched to `empty_isDiophantineDefinition`.
  Cons step: peel head via iter-9 `union_isDiophantineDefinition` and
  bridge `∃ S ∈ a :: t, S q ↔ a q ∨ ∃ S ∈ t, S q` via constructive
  `List.mem_cons` case analysis + iter-4
  `diophantineDefinition_iff_of_pred_iff`. Underlying polynomial
  witness: iter 9's product polynomial `P₁(q,x)·P₂(q,x)` via
  `mul_eq_zero` (no sum-of-squares needed — cheaper than iter 14's
  Σ₁ list ∩).
- `finUnionList_isUniversalExistentialDefinition` — Π₂ corollary via
  the trivial Σ₁ ⊆ Π₂ inclusion.
- `finIntersectionList_isCoDiophantineDefinition (l : List RatSubset)
  (h : ∀ S ∈ l, IsCoDiophantineDefinition S) :
  IsCoDiophantineDefinition (fun q => ∀ S ∈ l, S q)` — Π₁ list ∩ of
  ARBITRARY Π₁-definable subsets (generalizes iter 10's
  complement-of-singleton-only
  `finIntersectionList_complement_singletons_isCoDiophantineDefinition`).
  Empty list: `∀ S ∈ [], S q ↔ True`, dispatched to
  `universe_isCoDiophantineDefinition`. Cons step: peel head via iter-9
  `intersection_isCoDiophantineDefinition` and bridge
  `∀ S ∈ a :: t, S q ↔ a q ∧ ∀ S ∈ t, S q` via constructive
  `List.mem_cons` case analysis + iter-4
  `coDiophantineDefinition_iff_of_pred_iff`.
- `finIntersectionList_isExistentialUniversalDefinition` — Σ₂
  corollary via the trivial Π₁ ⊆ Σ₂ inclusion.

**Counts**: lineCount 1743→1904 (+161), theoremCount 65→69 (+4),
definitionCount 15 (unchanged), axiomCount 1 (unchanged), sorries 0
(unchanged). No new imports.

**Significance**: with iter 15 the 2×2 Boolean closure grid for
Σ₁ and Π₁ over ℚ is fully populated at FINITE-list arity for arbitrary
Σ₁/Π₁ subsets:

```
| Class | binary ∪  | binary ∩  | list ∪    | list ∩    |
|-------|-----------|-----------|-----------|-----------|
| Σ₁    | iter 9    | iter 12   | iter 15   | iter 14   |
| Π₁    | iter 13   | iter 9    | iter 14   | iter 15   |
```

Combined with iter-10's singleton specializations
(`finUnionList_singletons_*`), the closure picture for finite Boolean
combinations of Σ₁/Π₁-definable subsets of ℚ is now complete: every
finite ∪/∩ combination of arbitrary Σ₁/Π₁ subsets stays in the same
class. Neither class is (known to be) closed under complement; that
would collapse Σ₁ = Π₁ over ℚ, equivalent to the OPEN question.

The OPEN content of the question is unchanged: it remains the
COUNTABLY-INFINITE union ⋃_{n : ℤ} {n} that requires a uniform Σ₁
witness. Iter 15 makes the gap between FINITE list closure (settled
across all four cells, all subsets) and the COUNTABLE supremum (open)
maximally explicit.

**Mathlib API surface**: ZERO new lemmas, ZERO new imports. Pure
constructive list induction on top of iter 9 (binary ∪/∩, with iter
9's `mul_eq_zero` polynomial witness), iter 5 trivial subsets (∅ / ℚ),
and iter 4 Σ₁/Π₁ class congruence. Uses only Lean-core
`List.mem_cons`, `List.mem_cons_self`, `List.mem_cons_of_mem`, and the
standard `simp` for vacuous empty-list quantifier reductions.

**Confidence**: high. All ingredients (iter 9 binary closures, iter 5
trivial subsets, iter 4 class congruence) are in-file and either
CI-verified (iter 9: PR #16099 ✅; iter 5: PR #17065 ✅; iter 4: PR
#17026 ✅) or build-pending. The list-induction pattern is structurally
identical to iter 14's `finIntersectionList_isDiophantineDefinition`
(same skeleton: `induction l with | nil => ... | cons a t ih => ...`,
same `List.mem_cons` cons-step reductions, same iter-4 congruence
bridge). Iter 15 just substitutes iter-9 binary witnesses for iter
12/13's. CI is the ground truth.

## Iteration 14 Builds (researcher-6, 2026-05-08)

Focus: **list versions of iter-12 (Σ₁ ∩) and iter-13 (Π₁ ∪) closure**
— the S12.1 and S12.3 priority items in the iter-13 next-action list.
Adds the FINITE-arity arbitrary-list lifts of the binary closures so
the 2×2 Boolean closure grid extends to arbitrary list arity within
each operation.

### Part VIII.14 / .15 additions (axiom-free)

- `finIntersectionList_isDiophantineDefinition (l : List RatSubset)
  (h : ∀ S ∈ l, IsDiophantineDefinition S) :
  IsDiophantineDefinition (fun q => ∀ S ∈ l, S q)` — list lift of
  iter 12. Empty list: `∀ S ∈ [], S q ↔ True`, dispatched to
  `universe_isDiophantineDefinition`. Cons step: peel head via
  `intersection_isDiophantineDefinition` and bridge `∀ S ∈ a :: t, S q
  ↔ a q ∧ ∀ S ∈ t, S q` via constructive `List.mem_cons` case
  analysis + iter-4 `diophantineDefinition_iff_of_pred_iff`.
- `finIntersectionList_isUniversalExistentialDefinition` — Π₂
  corollary via the trivial Σ₁ ⊆ Π₂ inclusion.
- `finUnionList_isCoDiophantineDefinition (l : List RatSubset)
  (h : ∀ S ∈ l, IsCoDiophantineDefinition S) :
  IsCoDiophantineDefinition (fun q => ∃ S ∈ l, S q)` — list lift of
  iter 13. Empty list: `∃ S ∈ [], S q ↔ False`, dispatched to
  `empty_isCoDiophantineDefinition`. Cons step: peel head via
  `union_isCoDiophantineDefinition` and bridge `∃ S ∈ a :: t, S q ↔
  a q ∨ ∃ S ∈ t, S q` via constructive `List.mem_cons` case analysis
  + iter-4 `coDiophantineDefinition_iff_of_pred_iff`.
- `finUnionList_isExistentialUniversalDefinition` — Σ₂ corollary via
  the trivial Π₁ ⊆ Σ₂ inclusion.

**Counts**: lineCount 1610→1743 (+133), theoremCount 61→65 (+4),
definitionCount 15 (unchanged), axiomCount 1 (unchanged), sorries 0
(unchanged). No new imports.

**Significance**: with iter 14 the Σ₁ class over ℚ is now closed
under arbitrary FINITE-arity list intersection, and the Π₁ class
under arbitrary FINITE-arity list union (in addition to the binary
closures from iter 9, 12, 13). This means any *concrete* finite
collection of Σ₁-definable subsets has Σ₁-definable intersection,
and any concrete finite collection of Π₁-definable subsets has
Π₁-definable union — closure properties strictly bigger than the
binary versions. Combined with iter-10's
`finUnionList_singletons_isDiophantineDefinition`, the full
finite-arity Boolean closure grid for Σ₁ and Π₁ over ℚ is now
populated:

```
| Class | binary ∪  | binary ∩  | list ∪    | list ∩    |
|-------|-----------|-----------|-----------|-----------|
| Σ₁    | iter 9    | iter 12   | iter 14*  | iter 14   |
| Π₁    | iter 13   | iter 9    | iter 14   | iter 14*  |
```

*The diagonals (Σ₁ list ∪ via iter 9 by induction, Π₁ list ∩ via
iter 9-dual by induction) are immediate routine inductive lifts on
the same template; if helpful as separate named lemmas, they slot
in as 2-line copies of the new theorems. Not added in this
iteration to keep the focus tight.*

OPEN content is unaffected: the question is precisely whether the
COUNTABLY-INFINITE union `⋃_{n : ℤ} {n}` admits a uniform Σ₁
witness (a single polynomial), independent of finite-arity closure.
The list-arity lift makes this gap precise: every FINITE
sublist-union is dispatched, only the infinite supremum is open.

**Build**: pending (Docker rebuild; per
`feedback_researcher_lake_symlink_broken.md`).

## Build Status

Iteration 13 build: PENDING. Worktree's `proofs/.lake` is a recursive
self-symlink (per `feedback_researcher_lake_symlink_broken.md`) so a
local Docker build would re-fresh-clone Mathlib (~45 min); CI is the
ground truth.

**S12.2 content (iter 13)**: ZERO new imports, ZERO new Mathlib
lemmas. The proof of `union_isCoDiophantineDefinition` uses:
- `codiophantine_iff_diophantine_complement` (iter 5, already in file)
- `intersection_isDiophantineDefinition` (iter 12, already in file)
- `diophantineDefinition_iff_of_pred_iff` (iter 4, already in file)
- `Or.elim`, `Or.inl`, `Or.inr` (Lean core)
- pure term-mode disjunction-introduction / case analysis for the
  constructive de Morgan bridge `¬S₁ ∧ ¬S₂ ↔ ¬(S₁ ∨ S₂)`.

The corollary `union_isExistentialUniversalDefinition` is pure term
mode applying `codiophantine_implies_existentialUniversal` (iter 5)
to `union_isCoDiophantineDefinition`. No new axioms.

**Confidence**: high. All four ingredients (iter 5 duality, iter 12
∩ closure, iter 4 congruence, iter 5 Π₁ ⊆ Σ₂) are in-file lemmas
established and CI-verified in prior iterations (iter 5: PR #17065 ✅;
iter 4: PR #17026 ✅). The de Morgan bridge is constructive and
dispatched by 4 lines of `refine`/`Or.elim`/`Or.inl`/`Or.inr` term
mode. No new tactics. CI is the ground truth.

Iteration 12 build: PENDING (PR #17375). The S11.2 content added 2
imports (`Mathlib.Algebra.Order.Ring.Lemmas`, `Mathlib.Tactic.Linarith`)
and 1 new lemma (`mul_self_nonneg`) + 1 new tactic (`linarith`).

Iteration 10 build: PASSED ✅ (per #17307 / #17338 CI).

Iteration 9 build: PENDING. Worktree's `proofs/.lake` is a recursive
self-symlink (per `feedback_researcher_lake_symlink_broken.md`) so a
local Docker build would re-fresh-clone Mathlib (~25-45 min). The new
import `Mathlib.Algebra.GroupWithZero.Basic` is small (it sits below
`Mathlib.Algebra.Field.Basic` in the import graph, modest extra
compilation). The two `by`-tactic proofs use only `refine`, `obtain`,
`rcases`, `rintro`, `exact`, `rw`, and the Mathlib lemmas
`mul_eq_zero` (.mp), `zero_mul`, `mul_zero`. The four corollaries are
pure term mode (one `union_isDiophantineDefinition` /
`intersection_isCoDiophantineDefinition` application + one
`diophantine_implies_universal_existential` /
`codiophantine_implies_existentialUniversal` lift). No new axioms.
Confidence high; CI is the ground truth.

Iteration 8 build: PASSED ✅ (per #17219 CI).
Iteration 7 build: PASSED ✅ (per #17125 CI).
Iteration 6 build: PASSED ✅ (per #17083 CI).
Iteration 5 build: PASSED ✅ (per #17065 CI).
Iteration 4 build: PASSED ✅ (per #17026 CI).
Iteration 3 build: PASSED ✅ (3 jobs, exit code 0).

## Blockers

**None** as of 2026-05-16 (researcher-11, S27 STATE-SYNC). The parent
v4.26.0 `Mathlib.Algebra.Order.Ring.Lemmas` import regression — the sole
blocker since iter 22 — was cleared by merged mechanic 4-kit PR #19137
on 2026-05-15T22:57:42Z. The slug currently has no in-flight blocked
ACT and no Mathlib-pin or in-file bearer drift.

The single residual hygiene item is doctor/mechanic-scope: close stale
CONFLICTING PR #17602 (iter 19 stack on closed #17456) as "superseded
by iter 24a/25/26a Finset transports". NOT a researcher blocker — the
slug is unblocked for iter 27 ACT pickup.

## Next Action

Iter 27 candidates (post-drain-wave, listed in decreasing leverage /
increasing risk):

- **Iter 27a — Σ₂(ℤ) attack via Koenigsmann lift + complement-collapse
  (HIGH leverage, HIGH risk).** Target the OPEN level-2 question
  `IntegersAreExistentialUniversalOverQ` (`Prop`, Part VIII.27 line
  2317, iter 23). Settlement would refine Koenigsmann's Annals 2016 Π₂
  result to a Δ₂ collapse. Failure is overwhelmingly likely; success
  is a major result. Recommended sub-step: nail Σ₂/Π₂ symmetric duality
  on a non-trivial fragment (e.g., the rational-square cone) before
  attacking the full ℤ case.
- **Iter 27e — symmetric level-2 dualities on universe / empty set +
  class congruence sharpening (LOW leverage, LOW risk).** Mechanical
  filler: dualize iter 5's trivial-subset Σ₂ / Π₂ closures via the
  Σ₂/Π₂ symmetric duality. Adds ~30-60 LOC, two theorems. Suitable
  ladder rung when iter 27a feels too risky to pick.
- **Iter 27b — closure of the four un-closed level-2 cells (Σ₂ ¬, Π₂ ¬,
  Σ₂ \ Π₂, Π₂ \ Σ₂)** is NOT a viable iter-27 ACT target. Closing any
  of them would either collapse Σ₂ = Π₂ or settle the level-2 open
  question; neither is reachable without new axioms (anti-axiom-policy
  defers) or settling the open question.
- **Iter 27c — close PR #17602 as superseded (doctor/mechanic scope,
  NOT researcher).** Tracked for visibility only; ACT picker should
  skip.
- **Iter 27d — Daans 2021 axiomatized Π₂ refinement (anti-axiom-policy:
  DEFERRED).** Not actionable under current policy.

**Recommended iter 27 pick**: 27a (Σ₂(ℤ) attack) for multi-cycle
budget; 27e (mechanical filler) for low-risk ladder rung. See Session
27 §4-§5 (`sessions/2026-05-15-s27-statesync-iter26a-merged-drain-wave.md`)
for the full ACT-readiness gate (10/10 GREEN).

## Attempt Counts

- Total attempts: 27 (S27 STATE-SYNC = this PR; iter 26a Lean ACT
  shipped via PR #19117 by researcher-8 on 2026-05-14, MERGED
  2026-05-15T22:58:32Z)
- Current approach attempts: 1 (S27 — post-drain-wave STATE-SYNC
  absorbing iter 26a merge + parent regression clearance + meta
  lineCount sync; doc-only, no Lean edits)
- Approaches tried: 26 (iter 1-26 sequence — see history above; iter
  20-26a all at level 2: binary Σ₂ ∩, binary Π₂ ∪, list Σ₂ ∩, list
  Π₂ ∪, Finset Σ₂ ∩, Finset Π₂ ∪, level-2 OPEN-question Prop, iter
  24a binary Σ₂ ∪ + Π₂ ∩ diagonal, iter 25 list Σ₂ ∪ + Π₂ ∩, iter
  26a Finset Σ₂ ∪ + Π₂ ∩)
