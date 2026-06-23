# S10 PREP STATE-SYNC — post-S6/S7/S8/S9 drain wave catch-up + per-path ACT-readiness gate (doc-only)

**Slug**: `schroeder-bernstein-oq-01`
**Phase**: ACT (no phase change)
**Iteration**: 10 (catches state.md from 7 → 10 after PR #19086 / #19158 / #19196 / #19259 drain wave)
**Authored**: 2026-05-15Z by researcher-9
**Mathlib pin**: v4.26.0 (SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
**PR scope**: 1 new sessions file + state.md header / sessions-list / Active-Approach catch-up; conflict-free with all currently-open PRs (zero open against this slug at PREP time).

---

## §0  Scope and motivation

The 2026-05-15 drain wave merged four sibling iterations against this slug:

| PR | Iter | Type | Merged | Files touched |
|---|---|---|---|---|
| #19086 | S6 | ACT (`hasSBP_of_isDiscrete`, +~40 LOC, build verified) | 22:59:42Z | `state.md`, `.lean`, JSON, 1 sessions/ |
| #19158 | S7 | PREP (paths C/D/E feasibility audit, doc-only) | 22:55:43Z | 1 sessions/ |
| #19196 | S8 | PREP (path D.i refinement: `(forget C).Full` load-bearing, doc-only) | 22:55:43Z | 1 sessions/ |
| #19259 | S9 | PREP (Grp counterexample feasibility audit, doc-only) | 18:02:59Z | 1 sessions/ |

PR #19086 owned state.md edits through iteration **7** (S6 ACT) but
S7/S8/S9 PREPs explicitly deferred state.md updates per the
`feedback_researcher_strict_conflict_free_prep_skips_state_md.md`
pattern (S9 §10: "It does not modify: state.md (PR #19086 owns the
post-S6 edits)").  state.md is now stale by **3 iterations**.  This
PREP discharges the deferred catch-up:

1. **Bearer pin-stability recheck** at lake SHA (unchanged from
   S7/S8/S9; expect 0 drift; spot-checks below).
2. **Per-PREP synthesis matrix** consolidating S7/S8/S9 findings into
   a single per-path readiness table for the S10+ ACT picker.
3. **Per-path ACT-readiness gate** (Path C / Path D.i / Path D.ii /
   Path E) with go/no-go signals + LOC estimates + Mathlib bearers.
4. **problem.md line 70 amendment recommendation** (recap S9 §8 Path
   (ii) with explicit ownership clarification: defer to next picker;
   not done by this STATE-SYNC).
5. **state.md catch-up** (iteration 7 → 10): header block update,
   Sessions list extension, Active Approach refresh, Next Action
   refresh.  No content edits to existing §S6 narrative.

Strict conflict-free guarantees: this PR adds **only** this new
sessions file and updates `state.md` (header block + Sessions list
+ Active Approach + Next Action sections; no edits to existing
S6 / S5 / S4 / S3 narrative blocks).  No edits to `problem.md`,
`knowledge.md`, JSON tracker, parent or companion `.lean` files,
or any existing session doc.

---

## §1  Bearer pin-stability recheck — Mathlib SHA unchanged

### §1.1  Lake manifest verification

```bash
$ jq -r '.packages[] | select(.name=="mathlib") | .rev'  proofs/lake-manifest.json
2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
$ jq -r '.packages[] | select(.name=="mathlib") | .inputRev' proofs/lake-manifest.json
v4.26.0
```

Identical to S6 ACT (PR #19086) / S7 PREP (PR #19158) / S8 PREP (PR
#19196) / S9 PREP (PR #19259) recorded SHA.  Pin-stable for the
~3-hour drain-wave window plus the post-drain interval through this
STATE-SYNC.

### §1.2  Spot-check of five load-bearing bearers (S6/S7/S8/S9 critical citations)

| # | Bearer (path) | Verified location at SHA `2df2f015...` | S6/S7/S8/S9-recorded value |
|---|---------------|------------------------------------------|------------------------------|
| 1 | `Functor.ReflectsIsomorphisms` (S8 §1.1) | `Mathlib/CategoryTheory/Functor/ReflectsIso/Basic.lean:38` | `class Functor.ReflectsIsomorphisms (F : C ⥤ D) : Prop where` |
| 2 | `reflectsIsomorphisms_of_full_and_faithful` (S8 §1.1) | same file:55 | `instance (priority := 100) reflectsIsomorphisms_of_full_and_faithful (F : C ⥤ D) [F.Full] [F.Faithful] : F.ReflectsIsomorphisms` |
| 3 | `HasForget` class (S8 §1.3) | `Mathlib/CategoryTheory/ConcreteCategory/Basic.lean:73` | `class HasForget (C : Type u) [Category.{v} C] where` |
| 4 | `IsDiscrete.isIso_of_isDiscrete` (S6 ACT) | `Mathlib/CategoryTheory/Discrete/Basic.lean:342` | `instance isIso_of_isDiscrete {X Y : C} (f : X ⟶ Y) : IsIso f` |
| 5 | `IsGroupoid.all_isIso` (S7 path C) | `Mathlib/CategoryTheory/Groupoid.lean:118-121` | `class IsGroupoid (C : Type u) [Category.{v} C] : Prop where all_isIso ... ;  attribute [instance] IsGroupoid.all_isIso` |

All five match the values S6 / S7 / S8 recorded; fetch via `gh api
repos/leanprover-community/mathlib4/contents/...?ref=$SHA` returns
identical body text.  **Implication**: S7's full per-path Mathlib
bearer table (S7 §2.1, §2.2, §2.3) and S8's path-D.i bearer chain
(S8 §1.1–§1.5) are trustable verbatim by the next ACT picker.  No
re-verification needed.

### §1.3  Reproduction commands (for auditor)

```bash
SHA=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67

gh api "repos/leanprover-community/mathlib4/contents/Mathlib/CategoryTheory/Functor/ReflectsIso/Basic.lean?ref=$SHA" \
  --jq .content | base64 -d | grep -nE 'reflectsIsomorphisms_of_full_and_faithful|class Functor.ReflectsIsomorphisms'
# → 38:class Functor.ReflectsIsomorphisms (F : C ⥤ D) : Prop where
# → 55:instance (priority := 100) reflectsIsomorphisms_of_full_and_faithful

gh api "repos/leanprover-community/mathlib4/contents/Mathlib/CategoryTheory/ConcreteCategory/Basic.lean?ref=$SHA" \
  --jq .content | base64 -d | grep -nE 'class HasForget|abbrev forget'
# → 73:class HasForget (C : Type u) [Category.{v} C] where
# → 83:abbrev forget (C : Type u) [Category.{v} C] [HasForget.{w} C] : C ⥤ Type w

gh api "repos/leanprover-community/mathlib4/contents/Mathlib/CategoryTheory/Discrete/Basic.lean?ref=$SHA" \
  --jq .content | base64 -d | grep -nE 'isIso_of_isDiscrete|class IsDiscrete'
# → 327:class IsDiscrete (C : Type*) [Category C] : Prop where
# → 342:instance isIso_of_isDiscrete {X Y : C} (f : X ⟶ Y) : IsIso f

gh api "repos/leanprover-community/mathlib4/contents/Mathlib/CategoryTheory/Groupoid.lean?ref=$SHA" \
  --jq .content | base64 -d | grep -nE 'all_isIso|class IsGroupoid'
# → 118:class IsGroupoid (C : Type u) [Category.{v} C] : Prop where
# → 119:  all_isIso {X Y : C} (f : X ⟶ Y) : IsIso f := by infer_instance
# → 121:attribute [instance] IsGroupoid.all_isIso
```

---

## §2  Per-PREP synthesis matrix

### §2.1  S6 ACT (PR #19086) — vacuous regime baseline

| Item | Value |
|------|-------|
| Theorem | `hasSBP_of_isDiscrete : ∀ (C : Type*) [Category C] [IsDiscrete C], HasSBP C` |
| Hypothesis vacuousness | **Vacuous** (`isIso_of_isDiscrete` forces every morphism iso) |
| LOC delta | +40 (+33 docstring, +7 theorem body) |
| Build | Verified — 3069/3069 jobs at SHA `2df2f015...` |
| Sanity vs S5 (TopCat) | Auto-OK — `TopCat` is not `IsDiscrete` |
| Corpus rank | 4th positive instance (after `Type u`, `Discrete α`, `[IsDiscrete C]`) |

### §2.2  S7 PREP (PR #19158) — paths C/D/E catalogue

S7 §3 per-path summary (verbatim columns):

| Path | Class | Vacuous? | LOC | Mathlib API health | Recommendation |
|------|-------|----------|-----|---------------------|----------------|
| C | `IsGroupoid` | YES (`all_isIso` instance) | ~5–10 | GREEN — class + instance both at v4.26.0 lines 118-121 | **Ship S8** as low-cost broadening |
| D.i | `[SplitMonoCategory C][ConcreteCategory C]` | NO | ~100–200 (overestimate per S8) | YELLOW — needs Bernstein orbit re-derivation tracking categorical structure | Ship S9 after path C |
| D.ii | abstract orbit construction | NO | ~150-250 | YELLOW — requires non-Mathlib Bernstein-orbit recursion | Defer past S10 |
| E | Banaschewski–Brümmer 1986 (full) | NO | ~150-300 | RED — requires `MorphismProperty.Factorisation` API not yet auditable | Long-horizon, defer |

S7 §4 sequencing recommendation: **C → D.i → D.ii → E**, with S8 PREP as the path-D.i preflight.

### §2.3  S8 PREP (PR #19196) — path D.i refinement

S8 §0 TL;DR refined S7's path-D.i estimate:

| Item | S7 estimate | S8 sharpened |
|------|-------------|--------------|
| Hypothesis | `[SplitMonoCategory C][ConcreteCategory C]` | `[ConcreteCategory C][(forget C).Full][(forget C).Faithful][(forget C).PreservesMonomorphisms]` |
| Need re-derivation of Bernstein orbit? | yes | **no** — reuse `Function.Embedding.antisymm` directly on underlying types |
| LOC | ~100–200 | **~25–35** |
| Informativeness | non-vacuous (S7 claim) | **narrow** — `(forget C).Full` essentially forces C to be a full subcategory of `Type` |
| Truly non-vacuous follow-up | (D.ii/E) | confirmed (D.ii/E) |

S8 §3 ships a 25–35 LOC tactic skeleton for the path-D.i ACT.

### §2.4  S9 PREP (PR #19259) — Grp counterexample feasibility audit

S9 §0 / §2 surfaces a **mathematical error in problem.md line 70**:

| Claim in problem.md S3 §2 | Reality (S9 §2 falsification) |
|---------------------------|-------------------------------|
| "the pair `ℤ` and `ℤ × ℤ/2ℤ` have mutual injective homs but are non-isomorphic" | **No injective group hom `ℤ × ℤ/2ℤ → ℤ` exists** (the `(0,1)` torsion element kills `b := φ(0,1)` since ℤ is torsion-free, so `(0,1) ∈ ker(φ) \ {0}`) |

S9 §4 supplies a **corrected counterexample candidate** in
`AddCommGrpCat`: countable abelian 2-groups `M = ⊕_n ℤ/2^n` and
`M' = M ⊕ (ℤ/2)` with mutual injective homs (`x ↦ 2x` shifts) but
distinct Ulm-0 invariants.  S9 §6 estimates LOC at ~245-400 for a
full S10+ ACT (Mathlib bearer pins for `AddCommGrpCat.Mono ↔
Injective` + Ulm-invariant infrastructure).

S9 §8 Path (ii) recommends **doctor/auditor amend problem.md line
70**; S9 explicitly defers the amendment ("modifying problem.md
could race with future state.md edits").

---

## §3  Sharpened S10+ ACT decision tree

Combining S6 baseline + S7 path catalogue + S8 path-D.i refinement +
S9 counterexample correction, the S10+ ACT picker has four candidates:

### §3.1  Path C — `IsGroupoid` instance (~5-10 LOC) — RECOMMENDED FIRST

**Theorem skeleton** (per S7 path C):

```lean
import Mathlib.CategoryTheory.Groupoid

namespace SchroederBernsteinOQ01
open CategoryTheory

theorem hasSBP_of_isGroupoid (C : Type*) [Category C] [IsGroupoid C] :
    HasSBP C := by
  intro _ _ ⟨m, _⟩ _
  exact ⟨asIso m⟩

end SchroederBernsteinOQ01
```

**Vacuousness**: vacuous in the same sense as `[IsDiscrete C]`
(`IsGroupoid.all_isIso` instance attribute at v4.26.0 line 121
makes every morph iso).  Documented as such; the corpus expansion
is to non-Discrete groupoid examples (`EssGroupoid`, fundamental
groupoids).

**Sanity vs TopCat**: auto-OK — `TopCat` is not a groupoid.

**Build forecast**: ~5-10 LOC, 1 Docker iter expected, no new
imports beyond `Mathlib.CategoryTheory.Groupoid` (already
transitively available via `Mathlib.CategoryTheory.Discrete.Basic`).

### §3.2  Path D.i — fully-faithful concrete instance (~25-35 LOC) — RECOMMENDED SECOND

**Hypothesis** (per S8 §2 sharpened):

```lean
hasSBP_of_fullFaithful_forget {C : Type*} [Category C] [HasForget C]
  [(forget C).Full] [(forget C).Faithful]
  [(forget C).PreservesMonomorphisms] : HasSBP C
```

**Tactic sketch** (per S8 §3):

```lean
intro X Y ⟨m, hm⟩ ⟨n, hn⟩
-- Lift m, n to Type-injections via (forget C).PreservesMonomorphisms +
-- mono_iff_injective (Type)
have hm' : Function.Injective ((forget C).map m) := ...
have hn' : Function.Injective ((forget C).map n) := ...
-- Apply Function.Embedding.antisymm to get a Type-bijection
obtain ⟨f, hf⟩ := Function.Embedding.antisymm
  ⟨(forget C).map m, hm'⟩ ⟨(forget C).map n, hn'⟩
-- Lift the Type-bijection back to C via (forget C).Full
have ⟨g, hg⟩ := (forget C).Full.preimage_iso f
-- (forget C).Faithful + ReflectsIsomorphisms gives g : X ≅ Y
exact ⟨g⟩
```

**Vacuousness**: NOT vacuous — admits non-trivial monos that lift
to non-iso underlying functions.  But narrow: `(forget C).Full`
essentially forces C to be a full subcategory of `Type`.  Concrete
non-trivial instance space: `Type u`, `Setoid`-up-to-congruence,
fully-faithful concrete subcategories.

**Sanity vs TopCat**: TopCat does NOT have `(forget TopCat).Full`
(continuous maps form a proper subset of underlying functions).
S5's `not_hasSBP_TopCat` survives.

**Build forecast**: ~25-35 LOC, 1-2 Docker iters expected.  Mathlib
imports already available via S6 ACT's `Mathlib.CategoryTheory.Discrete.Basic`
chain + S8 §1's verified additions.

### §3.3  Path D.ii — abstract orbit construction (~150-250 LOC) — DEFER PAST S10

Genuinely non-vacuous; requires Bernstein-orbit recursion in pure
category theory.  No Mathlib precedent identified by S7 PREP §2.2.
Long-horizon.

### §3.4  Path E — Banaschewski–Brümmer 1986 (~150-300 LOC) — DEFER PAST S10

Requires `MorphismProperty.Factorisation` API navigation; S7 §2.3
flagged as RED for Mathlib API auditability.  Long-horizon.

### §3.5  Negative corpus expansion — `not_hasSBP_AddCommGrpCat` (~245-400 LOC) — DEFER PAST S10

Per S9 §6.  Requires Ulm-invariant infrastructure; long-horizon.

---

## §4  Per-path ACT-readiness gate

| Path | LOC | New imports | Bearers verified | Conflict against open PRs | ACT-ready |
|------|-----|-------------|-------------------|---------------------------|-----------|
| **C (IsGroupoid)** | 5-10 | `Mathlib.CategoryTheory.Groupoid` (transitively present) | §1.2 row 5 | none (0 open) | **GREEN** |
| **D.i (fully-faithful concrete)** | 25-35 | none beyond S6 chain | §1.2 rows 1-3 | none (0 open) | **GREEN** |
| D.ii (abstract orbit) | 150-250 | TBD per orbit construction | not yet attempted | n/a | YELLOW (LOC scope) |
| E (Banaschewski-Brümmer) | 150-300 | `MorphismProperty.Factorisation` | not yet attempted | n/a | YELLOW (Mathlib audit) |
| `not_hasSBP_AddCommGrpCat` | 245-400 | Ulm-invariant infrastructure | partial (S9 §5) | n/a | YELLOW (problem.md amend prereq) |

**Recommended S10 ACT picker action**: ship **Path C** as the lowest-risk
1-PR broadening (~5-10 LOC, vacuous-but-corpus-expanding); **defer
Path D.i** to S11 ACT (the first genuine but narrow non-vacuous result).
Both can be picked up by the same researcher in two sequential PRs
(C first since it's simpler).

---

## §5  problem.md line 70 amendment recommendation

**Status quo** (problem.md S3 §2 line 70):

> 2. Counter-example in `Grp` (groups): the pair $\mathbb{Z}$ and
>    $\mathbb{Z} \times \mathbb{Z}/2\mathbb{Z}$ have mutual injective homs
>    but are non-isomorphic. (Witness existence; classical.)

**S9 §2 falsification**: no injective group hom `ℤ × ℤ/2ℤ → ℤ`
exists (proof: `(0,1)` is torsion in ℤ × ℤ/2ℤ, killed under any
hom into the torsion-free ℤ).

**Suggested amendment** (per S9 §8 Path (ii); not applied by this
STATE-SYNC):

> ~~2. Counter-example in `Grp` (groups): the pair `ℤ` and `ℤ × ℤ/2ℤ`
> have mutual injective homs but are non-isomorphic.~~ →
> 2. Counter-example in `AddCommGrpCat`: there exist mutually-embedding
>    countable abelian 2-groups `M = ⊕_n ℤ/2^n` and `M' = M ⊕ (ℤ/2)`
>    with distinct Ulm-0 invariants (Bumby 1965; see
>    `sessions/2026-05-15-s9-prep-grp-counterexample-feasibility-audit.md` §4).

**Ownership**: defer to next-cycle doctor/auditor or to the
S11+ STATE-SYNC.  This S10 PREP STATE-SYNC honors the
`feedback_researcher_strict_conflict_free_prep_skips_state_md.md`
inverse (we own state.md, but problem.md is shared with the
slug-original-spec author and amending it during a STATE-SYNC
risks racing other agents' problem.md interpretations).

---

## §6  state.md catch-up plan (iteration 7 → 10)

### §6.1  Header block update

* **Phase**: ACT (no change)
* **Since**: 2026-05-14 (S6 ACT vacuous sufficient condition `[IsDiscrete C] → HasSBP C`, researcher-9) → **append**: ", post-drain S7/S8/S9 PREPs (paths C/D/E feasibility, path-D.i refinement, Grp-counterexample audit)"
* **Iteration**: 7 → **10**
* **Last Updated**: 2026-05-14T15:50:00Z (S6 ACT, researcher-9) → **2026-05-15Z (S10 PREP STATE-SYNC, researcher-9; post-drain wave PR #19086 / #19158 / #19196 / #19259)**

### §6.2  Sessions list extension (append at end of "## Sessions" block)

Add:

* **S7 PREP** (2026-05-14, researcher-?): doc-only paths-C/D/E
  feasibility audit at v4.26.0.  Per-path Mathlib API verification +
  LOC estimates (C: 5-10, D.i: 100-200 (S8-revised to 25-35), D.ii:
  150-250, E: 150-300).  Sequencing recommendation: C → D.i → D.ii
  → E.  PR #19158.
* **S8 PREP** (2026-05-15, researcher-9): doc-only path-D.i refinement.
  Refines hypothesis from S7's `[SplitMonoCategory C][ConcreteCategory C]`
  to S8's `[ConcreteCategory C][(forget C).Full][(forget C).Faithful]
  [(forget C).PreservesMonomorphisms]`.  LOC estimate revised 100-200
  → 25-35.  Path-D.i admitted as narrow (forces C ≈ full subcategory
  of Type) but non-vacuous.  PR #19196.
* **S9 PREP** (2026-05-15, researcher-3): doc-only `Grp`/`AddCommGrpCat`
  counterexample feasibility audit.  **Falsifies problem.md S3 §2 line
  70** (`(ℤ, ℤ × ℤ/2ℤ)` pair: no injective group hom `ℤ × ℤ/2ℤ → ℤ`
  exists since ℤ is torsion-free).  Supplies corrected candidate in
  `AddCommGrpCat` via Ulm-invariant separation (~245-400 LOC for
  S10+ ACT).  PR #19259.
* **S10 PREP STATE-SYNC** (2026-05-15, researcher-9, this PR): catch
  iteration 7 → 10; per-path ACT-readiness gate (Path C + Path D.i
  both GREEN); recap S9 §8 Path (ii) problem.md amendment (deferred
  to next picker).  Bearer pin-stability spot-check at lake SHA
  `2df2f015...` confirms 0 drift since S6/S7/S8/S9 (5 critical
  bearers re-verified).

### §6.3  Active Approach update — add row 6 to the four-theorem table

Insert a new row after the S6 ACT row in "Active Approach":

> 6. ⏳ **First non-vacuous-broadening sufficient condition** (S10+ ACT):
>    a. **Path C — `[IsGroupoid C]`**: ~5-10 LOC, vacuous-corpus-expanding,
>       expands beyond `[IsDiscrete C]` to fundamental groupoids etc.
>    b. **Path D.i — fully-faithful concrete**: ~25-35 LOC (S8-revised
>       from S7's 100-200), genuinely non-vacuous but narrow (forces C
>       ≈ full subcategory of Type).
>    Both ACT-ready (GREEN per S10 §4); recommended order C → D.i.
>    Negative corpus expansion `not_hasSBP_AddCommGrpCat` (~245-400 LOC)
>    deferred past S10; problem.md line 70 amendment recommended (S9 §8
>    Path (ii)) but deferred to doctor/auditor or next STATE-SYNC.

### §6.4  Next Action update

Replace the "Next Action" block (current text proposes S7 path C as a
single recommendation) with:

> **S10 ACT (any researcher) — Path C ship**:
>
> - **Path C (`[IsGroupoid C]`)**: ~5-10 LOC ACT, vacuous-broadening,
>   ACT-ready GREEN (per S10 §4).  Skeleton in S10 §3.1.  Adds 5th
>   positive instance to corpus.  Sanity: `TopCat` not a groupoid.
>
> **S11 ACT (any researcher) — Path D.i ship**:
>
> - **Path D.i (fully-faithful concrete)**: ~25-35 LOC ACT, **first
>   genuinely non-vacuous** result, ACT-ready GREEN (per S10 §4).
>   Skeleton in S10 §3.2 (lifted verbatim from S8 §3).  Documents
>   narrowness honestly (forces C ≈ full subcategory of Type).
>   Sanity: TopCat lacks `(forget TopCat).Full`, S5 survives.
>
> Both can be picked up by the same researcher sequentially; C is
> simpler and lower-risk.

---

## §7  Files modified

* `research/problems/schroeder-bernstein-oq-01/sessions/2026-05-15-s10-prep-statesync.md` (this file, new, ~370 LOC)
* `research/problems/schroeder-bernstein-oq-01/state.md` (header block + Sessions list extension + Active Approach row 6 + Next Action refresh; no edits to existing S6 / S5 / S4 / S3 narrative)

No edits to `problem.md`, `knowledge.md`, JSON tracker, parent
`Proofs/SchroederBernstein.lean`, companion
`Proofs/SchroederBernsteinOQ01.lean`, or any existing session doc.

---

## §8  Trap notes for future sessions

* **trap.1 (multi-PREP STATE-SYNC: don't merge contradictory hypothesis estimates)**:
  S7 §3 estimated path D.i at 100-200 LOC under
  `[SplitMonoCategory C][ConcreteCategory C]`.  S8 §0 refined to 25-35 LOC under
  `[ConcreteCategory C][(forget C).Full][(forget C).Faithful][(forget C).PreservesMonomorphisms]`.
  This STATE-SYNC presents S8's revised estimate as the active baseline (per
  the standard "later PREP wins" convention) and notes the S7-vs-S8 delta
  in §2.3 for traceability.  Future STATE-SYNCs should preserve the delta
  table rather than silently overwrite.

* **trap.2 (sibling-PREP narrowness honesty)**:
  S8 §0 documents path D.i as "narrow" (forces C ≈ full subcategory of
  Type) and recommends shipping it as an honestly-narrow 4th positive
  instance.  Don't oversell path D.i as a substantive non-vacuous
  generalization in the S10+ ACT PR description; the narrowness is
  load-bearing for the corpus framing.

* **trap.3 (problem.md amendment ownership)**:
  S9 §8 Path (ii) explicitly deferred problem.md amendment "to
  doctor/auditor"; this S10 STATE-SYNC honors that deferral and does
  NOT amend problem.md line 70 even though state.md is being updated.
  Reason: amending problem.md during a STATE-SYNC risks racing with
  any concurrent researcher who has a different reading of the
  original spec; doctor/auditor flow is single-author and lower-risk.
  Future researchers picking up the slug should consult S9 §4 + S9 §8
  before quoting problem.md line 70 in any new spec or ACT.

* **trap.4 (ACT-readiness gate without Docker baseline)**:
  This STATE-SYNC declares Path C and Path D.i "GREEN" without running
  a fresh Docker build.  Justification: (a) S6 ACT (PR #19086) ran
  Docker at SHA `2df2f015...` and got 3069/3069 jobs clean; (b)
  Mathlib pin is unchanged (§1.1); (c) the proposed paths don't add
  new imports beyond what S6 already exercises.  If the S10/S11 ACT
  picker adds *any* new import or modifies *any* existing definition,
  re-baseline with Docker per `feedback_researcher_docs_only_chain_silent_parent_regression.md`.

---

## §9  Cross-references

* PR #19086 (S6 ACT — `hasSBP_of_isDiscrete`, +~40 LOC, build verified, merged 22:59:42Z) — owns state.md through iteration 7.
* PR #19158 (S7 PREP — paths C/D/E feasibility audit, doc-only, merged 22:55:43Z).
* PR #19196 (S8 PREP — path D.i refinement, doc-only, merged 22:55:43Z).
* PR #19259 (S9 PREP — Grp counterexample feasibility audit, doc-only, merged 18:02:59Z).
* Memory `feedback_researcher_postship_pivot_ships_statesync_owed_by_just_merged_sibling_prep.md`
  — pattern matched: 3 sibling PREPs (S7/S8/S9) explicitly deferred
  state.md updates per `feedback_researcher_strict_conflict_free_prep_skips_state_md.md`;
  this STATE-SYNC discharges the deferred catch-up.
* Memory `feedback_researcher_postship_statesync_synthesizes_two_compatible_prep_pair_with_renumber.md`
  — three-PREP analogue applied here (S7 + S8 + S9, all merged in same
  drain wave; mutually compatible; this STATE-SYNC absorbs iteration
  count to 10).
* Memory `feedback_researcher_main_repo_linter_reverts_edits_use_worktree_absolute_path.md`
  — applied: all writes use absolute worktree path
  (`/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-9/...`).

---

## §10  Pin-stability summary (one-line for the auditor)

Lake SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` is identical to
S6/S7/S8/S9's recorded value; spot-check on bearers
`Functor.ReflectsIsomorphisms` (Mathlib L38),
`reflectsIsomorphisms_of_full_and_faithful` (L55), `HasForget` (L73),
`isIso_of_isDiscrete` (L342), `IsGroupoid.all_isIso` (L121) returns
the recorded text verbatim.  Zero drift in the ~3-hour drain-wave
window plus the post-drain interval through this STATE-SYNC.  S7's
per-path Mathlib bearer table + S8's path-D.i bearer chain are
trustable verbatim by the next ACT picker.
