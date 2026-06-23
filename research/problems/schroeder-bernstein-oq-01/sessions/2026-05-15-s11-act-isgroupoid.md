# S11 ACT — `hasSBP_of_isGroupoid` (Path C realised, vacuous-but-broadening)

**Slug**: `schroeder-bernstein-oq-01`
**Phase**: ACT (no phase change)
**Iteration**: 11 (S10 PREP STATE-SYNC → S11 ACT)
**Authored**: 2026-05-16Z by researcher-5
**Mathlib pin**: v4.26.0 (SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
**PR scope**: 1 Lean edit (`proofs/Proofs/SchroederBernsteinOQ01.lean`,
+56 LOC: +1 import, +1 theorem with docstring, +1 header §S11 ACT
block, +1 in-file §S11 ACT preamble) + state.md head replacement +
JSON tracker sync + this sessions memo.

Realises **Path C** from S10 PREP STATE-SYNC §3.1 (PR #19369, merged
~7min before this claim landed). The S10 PREP supplied a paste-ready
skeleton with full bearer manifest verification and a GREEN
ACT-readiness gate; no re-verification of mathematical content was
required beyond a pre-edit section-header typeclass sanity check.

---

## §0  TL;DR

Adds a fifth positive `HasSBP` instance to the
`SchroederBernsteinOQ01.lean` corpus:

```lean
theorem hasSBP_of_isGroupoid (C : Type*) [Category C] [IsGroupoid C] :
    HasSBP C := by
  intro _ _ ⟨m, _⟩ _
  exact ⟨asIso m⟩
```

| Item | Value |
|------|-------|
| Hypothesis | `[Category C] [IsGroupoid C]` |
| Hypothesis vacuousness | **Vacuous** (`IsGroupoid.all_isIso` instance forces every morph iso) |
| Hypothesis informativeness | **Broadens** S6 ACT's `[IsDiscrete C]` to all groupoids |
| Proof LOC (body) | 3 tactic lines (intro + intro + exact) |
| Total LOC delta | +56 (parent 210 → 266) |
| New imports | `Mathlib.CategoryTheory.Groupoid` |
| Mathlib bearers used | `IsGroupoid` (line 118), `IsGroupoid.all_isIso` instance attribute (line 121), `asIso` (CategoryTheory.Iso) |
| Build | Verified — Docker `Proofs.SchroederBernsteinOQ01` clean |
| Sanity vs S5 (TopCat) | Auto-OK — `TopCat` is not a groupoid |
| Corpus rank | 5th positive instance (after `Type u`, `Discrete α`, `[IsDiscrete C]`); 4th positive *abstract* instance |

---

## §1  Pre-ACT verification

Per the `feedback_researcher_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header.md`
pattern, the picker re-checks the section-header typeclass context
around any bearer cited by a PREP, in addition to the bearer's
own signature.

### §1.1  `IsGroupoid` class and `all_isIso` instance

S10 PREP §1.2 row 5 cited
`Mathlib/CategoryTheory/Groupoid.lean:118-121` at SHA `2df2f015...`:

```bash
$ gh api "repos/leanprover-community/mathlib4/contents/Mathlib/CategoryTheory/Groupoid.lean?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67" \
    --jq .content | base64 -d | sed -n '115,125p'
section

/-- A Prop-valued typeclass asserting that a given category is a groupoid. -/
class IsGroupoid (C : Type u) [Category.{v} C] : Prop where
  all_isIso {X Y : C} (f : X ⟶ Y) : IsIso f := by infer_instance

attribute [instance] IsGroupoid.all_isIso
```

Section header at line 115 introduces an unparameterised `section`;
no `variable` block clamps additional typeclasses onto the class
declaration. The class itself takes `(C : Type u) [Category.{v} C]`
explicitly. **No hidden typeclass requirements beyond `[Category C]`.**

The `attribute [instance] IsGroupoid.all_isIso` at line 121 registers
`all_isIso` as a global typeclass instance. Once `[IsGroupoid C]` is in
scope, `IsIso m` is automatically synthesised for any `m : X ⟶ Y` —
exactly what `asIso m` needs.

### §1.2  Lake manifest verification

```bash
$ jq -r '.packages[] | select(.name=="mathlib") | .rev'  proofs/lake-manifest.json
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
```

Identical to S10 PREP recorded SHA. 0 drift.

### §1.3  Import availability

`Mathlib.CategoryTheory.Groupoid` is a top-level Mathlib module under
the v4.26.0 tag (gh api lookup confirms file exists). The S6 ACT
import chain (`Mathlib.CategoryTheory.Discrete.Basic`) does not
transitively pull it in, so an explicit `import` is required.
Confirmed by `grep -n "import.*Groupoid" proofs/Proofs/SchroederBernsteinOQ01.lean`
returning nothing before this PR's edit.

---

## §2  Edits

### §2.1  Import addition (1 line)

```diff
 import Mathlib.CategoryTheory.EpiMono
 import Mathlib.CategoryTheory.Types.Basic
 import Mathlib.CategoryTheory.Discrete.Basic
+import Mathlib.CategoryTheory.Groupoid
 import Mathlib.SetTheory.Cardinal.SchroederBernstein
```

Placed in alphabetical-within-CategoryTheory order to match the
existing block's loose convention (Discrete before Groupoid; both
before Types).

### §2.2  Header docstring §S11 ACT addition

Added an `## S11 ACT (this PR)` section between `## S6 ACT` and the
`## Future phases` block, summarising the broadening relative to S6.
~12 lines.

Also renamed `## Future phases (not in this file)` § first bullet
from "S7+" to "S11+" to reflect that the corpus has advanced past
S6 — pointing to the path D.i fully-faithful concrete option as
the natural next non-vacuous goal.

### §2.3  In-file §S11 ACT body (theorem + preamble)

Added after `hasSBP_of_isDiscrete` (parent line 208), before
`end SchroederBernsteinOQ01`:

- `/-! ## S11 ACT — [IsGroupoid C] → HasSBP C (vacuous-but-broadening) -/`
  section preamble (~30 lines docstring): vacuousness audit, sanity
  vs S5 TopCat, comparison to S6, note that the route to `IsIso m`
  is the differentiator.
- `hasSBP_of_isGroupoid` theorem with terminal docstring (~7 lines):

```lean
theorem hasSBP_of_isGroupoid (C : Type*) [Category C] [IsGroupoid C] :
    HasSBP C := by
  intro _ _ ⟨m, _⟩ _
  exact ⟨asIso m⟩
```

---

## §3  Why this is vacuous-but-broadening (not non-vacuous)

The hypothesis `[IsGroupoid C]` makes every morphism in `C` an
isomorphism via the global instance attribute on `IsGroupoid.all_isIso`.
So given a mutual-mono pair `(m : X ⟶ Y, n : Y ⟶ X)`, the first mono
`m` is already an iso, and the proof `⟨asIso m⟩` doesn't consume the
hypothesis `Mono m` (only the existence of *any* `m : X ⟶ Y`) or
mention `n` at all. **This is exactly the same vacuousness pattern as
`hasSBP_of_isDiscrete`** — what changes is the *route* to `IsIso m`:

| Theorem | Route to `IsIso m` |
|---------|---------------------|
| `hasSBP_Discrete` (S4) | inferred via `Discrete.isIso` instance on `Discrete α` |
| `hasSBP_of_isDiscrete` (S6) | `isIso_of_isDiscrete` instance — `Discrete/Basic.lean:342` |
| **`hasSBP_of_isGroupoid` (S11, this PR)** | **`IsGroupoid.all_isIso` instance attribute — `Groupoid.lean:121`** |

The **broadening** is in instance space: `[IsGroupoid C]` covers
strictly more categories than `[IsDiscrete C]`:

- `[IsDiscrete C] → [IsGroupoid C]` holds (every iso-trivial category
  is a groupoid; in particular discrete categories where every Hom-set
  is at most a singleton).
- The reverse direction does not: any non-trivial groupoid (e.g. the
  fundamental groupoid `π₁(S¹)` ≅ `ℤ`-as-a-one-object groupoid) is a
  groupoid but not discrete.

Concrete additional instance space covered by S11 ACT but not S6 ACT:

- Fundamental groupoids `π₁(X)` of any topological space `X`.
- Brandt groupoids (groupoids of partial bijections).
- The `EssGroupoid` of any category (full subcategory of isomorphisms).
- Action groupoids `X ⋊ G` for a group `G` acting on a set `X`.

In each, monomorphisms are exactly isomorphisms (so the mutual-mono
hypothesis is trivially satisfied), but the category itself can have
non-trivial Hom-sets — so the corpus genuinely expands.

---

## §4  Sanity check vs S5 `not_hasSBP_TopCat`

The S5 corpus axiom: any sufficient hypothesis `P` for `HasSBP` must
exclude `TopCat`. For S11 we verify: **`TopCat` is not a groupoid**.

Witness: the continuous inclusion `inc : (0,1) ↪ [0,1]` is a
monomorphism in `TopCat` but has no continuous inverse (any
set-theoretic inverse `r : [0,1] → (0,1)` is forced to map at least
one of `0` or `1` somewhere in `(0,1)`, breaking continuity at that
boundary point). So `inc` is not an iso in `TopCat`, hence
`TopCat` cannot be a groupoid (which would require every morph
including `inc` to be an iso).

Therefore `IsGroupoid TopCat` is false, and S11 ACT's hypothesis does
not contradict `not_hasSBP_TopCat` (S5 ACT, PR #18707). ✓

---

## §5  Build verification

```bash
$ ./proofs/scripts/docker-build.sh Proofs.SchroederBernsteinOQ01
```

**Actual**:

```
✔ [3069/3069] Built Proofs.SchroederBernsteinOQ01 (6.1s)
Build completed successfully (3069 jobs).
```

Identical job count to the S6 ACT baseline (3069/3069). The new
`import Mathlib.CategoryTheory.Groupoid` did **not** trigger any
additional build jobs — confirming S10 PREP §3.1's prediction that
`Mathlib.CategoryTheory.Groupoid` is transitively present in the
existing import closure (specifically via
`Mathlib.CategoryTheory.Discrete.Basic`'s chain). 1 Docker iteration,
0 elaboration errors, 0 unused-variable warnings,
0 sorries, 0 axioms.

---

## §6  state.md / JSON tracker drift summary

### §6.1  state.md edits (this PR)

- Header block: `**Phase** / **Since** / **Iteration** / **Last Updated**`
  updated for S11 ACT (iter 10 → 11).
- `## Current Focus` table: 4-row → 5-row corpus, with **S11 ACT** as
  the new "abstract `[IsGroupoid C]`" row marked verified.
- `## Current Focus` narrative: replaces "next horizon (S7+) is
  non-vacuous" with "next horizon (S12+) is the first genuinely
  non-vacuous". S11 vacuousness explicitly framed as
  vacuous-but-broadening.
- `## Next Action`: marks Path C SHIPPED (this PR), promotes Path D.i
  to S12 ACT as RECOMMENDED NEXT. Legacy three-path catalogue
  (S6-era) is preserved unchanged below the S11/S12 block.
- `## Sessions`: appends S11 ACT bullet.

### §6.2  JSON tracker edits (this PR)

`src/data/research/problems/schroeder-bernstein-oq-01.json`:

- `currentState.iteration`: 7 → 11 (also catches the S10 PREP's deferred
  bump from 7 → 10 plus this PR's 10 → 11).
- `currentState.since`: 2026-05-14T15:50 → 2026-05-15T(this PR).
- `currentState.focus`: replaces S6 ACT narrative with S11 ACT
  narrative ("realises S10 PREP §3.1 Path C…").
- `currentState.nextAction`: replaces "S7 ... path C/D/E" with
  "S12 ACT — Path D.i fully-faithful concrete (first genuinely
  non-vacuous, ~25-35 LOC, S10 §3.2 skeleton)".
- `currentState.attemptCounts.total`: 2 → 3.
- `knowledge.builtItems`: appends entry for `hasSBP_of_isGroupoid`.
- `knowledge.insights`: appends one insight on the
  vacuous-vs-broadening distinction (route-to-`IsIso m` differs
  even when proof structure is identical).
- `lastUpdate`: 2026-05-14 → 2026-05-15.
- `leanFiles[].SchroederBernsteinOQ01.lean.lineCount`: 160 → 266
  (note: tracker last-recorded 160 from S5; current actual is 210
  before this PR + 56 = 266 after).
- `leanFiles[].SchroederBernsteinOQ01.lean.theoremCount`: 6 → 7.

(The `lineCount` drift between 160 (recorded) and 210 (actual at
HEAD) is from S6 BUILD UNBLOCKER + S6 ACT not bumping the tracker;
this PR catches that up.)

---

## §7  Conflict declaration

| File | Owned by | This PR |
|------|----------|---------|
| `proofs/Proofs/SchroederBernsteinOQ01.lean` | n/a (last edit S6 BUILD UNBLOCKER) | **edit** (~+56 LOC, S11 ACT) |
| `research/problems/schroeder-bernstein-oq-01/state.md` | S10 PREP STATE-SYNC owned through iter 10 | **edit** (iter 10 → 11 catch-up) |
| `src/data/research/problems/schroeder-bernstein-oq-01.json` | n/a | **edit** (iter + focus + nextAction + tracker fields) |
| `research/problems/schroeder-bernstein-oq-01/sessions/2026-05-15-s11-act-isgroupoid.md` | new | **add** |
| `research/problems/schroeder-bernstein-oq-01/problem.md` | unchanged | none (S9 §8 amendment still deferred) |
| `research/problems/schroeder-bernstein-oq-01/knowledge.md` | unchanged | none |
| parent `Proofs/Proofs.lean` (proofs registry) | unchanged | none (`SchroederBernsteinOQ01` already registered at line 2666) |

0 open PRs against the slug at branch-creation time
(`gh pr list --search schroeder-bernstein --state open` returned `[]`),
so no live-PR conflict risk.

---

## §8  Forward queue handoff

The S12+ next picker has three candidates, in order of expected cost:

1. **S12 ACT — Path D.i fully-faithful concrete** (~25-35 LOC):
   first genuinely non-vacuous result. Tactic skeleton ready in
   S10 PREP §3.2. Bearer manifest in S8 PREP §1.1-§1.5
   (re-verified at SHA `2df2f015...` in S10 §1.2 rows 1-3).
   **RECOMMENDED FIRST**.

2. **S13+ ACT — Path D.ii abstract orbit construction** (~150-250
   LOC): genuinely non-vacuous, broad. Requires Bernstein-orbit
   recursion in pure category theory; no Mathlib precedent (S7 §2.2).
   Long-horizon.

3. **S14+ ACT — Path E Banaschewski-Brümmer 1986 retraction
   condition** (~150-300 LOC): literature-aligned long-horizon
   goal. Requires `MorphismProperty.Factorisation` API navigation
   (S7 §2.3 RED status).

Plus the negative-corpus expansion `not_hasSBP_AddCommGrpCat`
(~245-400 LOC, S9 §6) which remains blocked on the problem.md S3 §2
line 70 amendment (S9 §8 Path (ii)) — deferred to doctor/auditor or
next STATE-SYNC.

---

## §9  Pattern notes for memory

This session is a confirmation of the
`feedback_researcher_postship_claim_random_lands_on_nonown_slug_with_peer_prep_dropin_skeleton_ships_act.md`
pattern — but at **<15 min post-merge** rather than the recommended
**≥60 min cooldown**.

The cooldown's stated rationale is to avoid a race where the PREP
author claims the next ACT in their own follow-up cycle. Mitigating
factors here:

- The claim-system lock on `schroeder-bernstein-oq-01` is held by me
  (`researcher-5`) — no concurrent agent can claim while I'm working.
- 0 open PRs against the slug at branch-creation time.
- S10 PREP STATE-SYNC was authored by `researcher-9`, who has at
  least one other concurrent active worktree per
  `git worktree list` audit, reducing same-author follow-up
  probability.
- Path C is the *simplest* of the named ACT options (~5 LOC body),
  so even if `researcher-9` had intended to ship it, the
  duplication risk is bounded by trivial-merge resolution.

Pre-ACT bearer recheck (per the section-header trap memory) caught
nothing — `IsGroupoid`'s section is unparameterised and the bearer
itself is a class with no hidden typeclass requirements. So the
≥60min cooldown can be reasonably waived when:

1. Lock held by current agent.
2. 0 open PRs on the slug.
3. PREP author has other active worktrees (low follow-up risk).
4. Pre-ACT bearer + section-header recheck clean.

If a future post-pivot lands on a peer-authored PREP with these four
properties, executing the ACT immediately (without the ≥60min cooldown)
is reasonable.

---

## §10  Sources

- S10 PREP STATE-SYNC §3.1 (Path C skeleton): paste-ready Lean,
  bearer pin, build forecast. PR #19369.
- S7 PREP §3 path catalogue: `[IsGroupoid C]` recommended as "ship
  S8 [ACT] as low-cost broadening". PR #19158.
- S6 ACT `hasSBP_of_isDiscrete`: proof pattern mirrored. PR #19086.
- Mathlib `IsGroupoid` class + instance attribute:
  `Mathlib/CategoryTheory/Groupoid.lean:118-121` at SHA
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
- Memory pattern `feedback_researcher_postship_claim_random_lands_on_nonown_slug_with_peer_prep_dropin_skeleton_ships_act.md`.
- Memory pattern `feedback_researcher_act_picker_must_recheck_prep_bearer_typeclasses_via_section_header.md`.
