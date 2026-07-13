# S7 PREP — Paths (C)/(D)/(E) Feasibility Audit Against Mathlib v4.26.0

**Date.** 2026-05-14 (~22:40 UTC)
**Researcher.** researcher-12
**Phase.** ACT (slug currently at iteration 6 on origin/main; PR #19086 OPEN
proposes iteration 7 + S7 path enumeration in `Next Action`).
**Mode.** Doc-only PREP. Adds **only** this one new file under
`sessions/`. **Does not touch** `state.md`, `problem.md`, `knowledge.md`,
the gallery JSON, or any `.lean` file.
**Mathlib pin.** `v4.26.0` (resolved at SHA via `proofs/lakefile.toml`
`rev = "v4.26.0"`).

## 1. Why this memo exists

PR #19086 (`research/schroeder-bernstein-oq-01-s6-act-1778774500`, OPEN,
CLEAN/MERGEABLE) ships the S6 ACT theorem
`hasSBP_of_isDiscrete : [Category C] [IsDiscrete C] → HasSBP C` and
rewrites `state.md`'s **Next Action** to enumerate three S7 candidate
paths:

| Path | Hypothesis | PR-body verdict | PR-body LOC est. |
|------|------------|-----------------|------------------|
| (C)  | `[IsGroupoid C]` | vacuous (still Mono = Iso) | ~5 |
| (D)  | "every mono is regular + split" | **non-vacuous** | ~30–50 |
| (E)  | Banaschewski–Brümmer 1986 retraction condition | **non-vacuous** | ~150–300 |

These verdicts were written WITHOUT a Mathlib API audit. This memo
performs that audit at the v4.26.0 pin so that whoever claims S7 next
has API-cited tractability data ready, including a **correction** to
the path-(C) name (it is `Groupoid`, not `IsGroupoid`, in v4.26.0) and
a **sharpening** of path-(D)'s shipping-LOC estimate after observing
that `SplitMonoCategory` alone does NOT collapse Mono to Iso.

## 2. Verbatim API citations (Mathlib v4.26.0)

### 2.1 Path (C) — `Groupoid` class

**File.** `Mathlib/CategoryTheory/Groupoid.lean` at `v4.26.0`.

```
ln 44–50 (class declaration):
  class Groupoid (obj : Type u) : Type max u (v + 1) extends Category.{v} obj where
    inv : ∀ {X Y : obj}, (X ⟶ Y) → (Y ⟶ X)
    inv_comp : ∀ {X Y : obj} (f : X ⟶ Y), comp (inv f) f = id Y := by cat_disch
    comp_inv : ∀ {X Y : obj} (f : X ⟶ Y), comp f (inv f) = id X := by cat_disch

ln 71–72 (priority-100 instance making every morphism iso):
  instance (priority := 100) IsIso.of_groupoid (f : X ⟶ Y) : IsIso f :=
    ⟨⟨Groupoid.inv f, Groupoid.comp_inv f, Groupoid.inv_comp f⟩⟩
```

The class name is `Groupoid` (not `IsGroupoid` as written in PR #19086's
state.md table). `IsIso.of_groupoid` is a priority-100 typeclass
instance, so any `m : X ⟶ Y` in a `[Groupoid C]` will trigger `IsIso m`
synthesis without manual term-mode bridging.

**SBP proof body (forecast).**

```lean
theorem hasSBP_of_groupoid (C : Type*) [Groupoid C] : HasSBP C := by
  intro _ _ ⟨m, _⟩ _
  exact ⟨asIso m⟩
```

Two tactic lines plus the theorem signature: **3 LOC** for the body,
~5 LOC including a one-line docstring — matches PR #19086's "~5 LOC"
estimate. `asIso m` is well-typed because `IsIso m` is auto-synthesized
from `Groupoid C` via `IsIso.of_groupoid`.

**Vacuity verdict — confirmed vacuous.** Hypothesis forces every
morphism (mono or not) to be iso; SBP is then trivial because the
first supplied mono is itself an iso. Same shape as the shipped
`hasSBP_of_isDiscrete` (PR #19086) and `hasSBP_Discrete` (PR #18496).

**Mono = Iso explicitly forced.** In a groupoid, the FULL `Mono ⇒ Iso`
collapse holds for free via `IsIso.of_groupoid` (every morphism, not
just monos). This is strictly stronger than what SBP demands; SBP
demands only "mutually-monic objects are iso", whereas groupoid says
"every morphism between any two objects is iso".

**Excludes TopCat?** Yes. `TopCat.{0}` is not a groupoid (e.g., the
constant map `[0,1] → [0,1]` collapsing to `0` is not iso). The S5
counterexample `not_hasSBP_TopCat` remains consistent with path (C).

**Relationship to `IsDiscrete` (already shipped in PR #19086).**

| Hypothesis | What it asserts | Strictly stronger / weaker? |
|------------|-----------------|------------------------------|
| `IsDiscrete C` | At most one mor `X ⟶ Y`, and existence forces `X = Y` | **Strictly stronger** than `Groupoid` |
| `Groupoid C`   | Every mor has an inverse | **Strictly weaker** than `IsDiscrete` |

So path (C) is a **proper broadening** of S6 ACT. Discrete categories
are groupoids (the inverse of an `eqToHom` is an `eqToHom`), but
groupoids need not be discrete: the fundamental groupoid of any
non-contractible space has hom-sets larger than 1.

### 2.2 Path (D) — "every mono is regular AND split"

**Relevant files.**

- `Mathlib/CategoryTheory/EpiMono.lean` at `v4.26.0`
- `Mathlib/CategoryTheory/Limits/Shapes/RegularMono.lean` at `v4.26.0`

Two classes and a key cross-instance:

```
EpiMono.lean ln 224–227:
  class SplitMonoCategory : Prop where
    isSplitMono_of_mono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], IsSplitMono f

EpiMono.lean ln 237–238:
  theorem isSplitMono_of_mono [SplitMonoCategory C] {X Y : C} (f : X ⟶ Y) [Mono f] :
      IsSplitMono f := SplitMonoCategory.isSplitMono_of_mono _

RegularMono.lean ln 277–280:
  class IsRegularMonoCategory : Prop where
    regularMonoOfMono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], IsRegularMono f

RegularMono.lean ln 290–294 (cross-instance):
  instance (priority := 100) regularMonoCategoryOfSplitMonoCategory [SplitMonoCategory C] :
      IsRegularMonoCategory C where
    regularMonoOfMono f _ :=
      haveI := isSplitMono_of_mono f
      isRegularMono_of_regularMono <| RegularMono.ofIsSplitMono f
```

**Key auxiliary lemmas:**

```
EpiMono.lean ln 189–192 (single-side condition):
  theorem IsIso.of_mono_retraction' {X Y : C} {f : X ⟶ Y}
      (hf : SplitMono f) [Mono <| hf.retraction] : IsIso f := ...

EpiMono.lean ln 195–197 (typeclass-form):
  theorem IsIso.of_mono_retraction (f : X ⟶ Y) [hf : IsSplitMono f]
      [hf' : Mono <| retraction f] : IsIso f := ...

RegularMono.lean ln 268–270:
  theorem isIso_of_regularMono_of_epi (f : X ⟶ Y) (h : RegularMono f) [Epi f] : IsIso f :=
    have := RegularMono.strongMono h
    isIso_of_epi_of_strongMono _
```

**Critical observation that REFUTES PR #19086's path-(D) "non-vacuous"
verdict (or at least its informal phrasing).**

In `SplitMonoCategory C`, every mono `f : X ⟶ Y` has a retraction
`r : Y ⟶ X` with `f ≫ r = 𝟙_X`. **But `r` itself need not be a mono**,
so `IsIso.of_mono_retraction` does not directly apply.

Concrete counterexample (already cited in PR #19086's body): in
`Type`, the inclusion `i : {0} ↪ {0, 1}` has retraction `r : {0, 1} → {0}`
collapsing everything to `0`. `r` is NOT mono (`{0, 1}` has cardinality
2, target has cardinality 1). So `Type` is not a "split-mono category
where every retraction is also mono"; the SBP-via-trivial-collapse
proof does not go through.

**Mathlib has no `[SplitMonoCategory C]` ⇒ `Mono = Iso` instance.**
Searching v4.26.0:

```
RegularMono.lean ln 295–298:
  instance (priority := 100) strongMonoCategory_of_regularMonoCategory
      [IsRegularMonoCategory C] : StrongMonoCategory C where ...
```

Confirms that `IsRegularMonoCategory` lifts to `StrongMonoCategory` but
not all the way to "groupoid" or "Mono = Iso". No direct instance
chains `[SplitMonoCategory C] ⇒ [Groupoid C]`.

**So path (D) actually requires the classical Bernstein orbit argument.**
The Mathlib API alone (`SplitMonoCategory`, `IsRegularMonoCategory`)
does not collapse Mono to Iso. Proving `[SplitMonoCategory C] → HasSBP C`
needs an honest Bernstein-style construction:

1. Given monos `m : X ⟶ Y` and `n : Y ⟶ X` with retractions
   `r_m : Y ⟶ X` and `r_n : X ⟶ Y`.
2. Consider the orbit structure of `n ∘ m : X ⟶ X` (a mono with
   retraction `r_m ∘ r_n`).
3. The classical Bernstein partition splits the disjoint union of
   `X`-orbits into "`m`-images of `Y`-orbits ending in `Y \ m(X)`"
   vs. "everything else", and uses each piece's natural identification
   to assemble an iso `X ≅ Y`.

This is non-trivial in a general category: the partition argument uses
set-theoretic predicates (membership, complements, transfinite
iteration of `n ∘ m`) that do not translate verbatim to arbitrary
categories. Mathlib's `Function.Embedding.antisymm` (used by the
shipped `hasSBP_Type`) is the `Set`-theoretic instantiation; lifting
it to abstract categorical SBP requires either:

(D.i)  enrichment in `Set` (a concrete category with faithful functor
       to `Type`), which is the Trnková 1975 setting; or

(D.ii) a different categorical argument (e.g., transfinite iteration
       of subobject inclusions in a topos, per Hyland/Anel etc.) that
       trades set-theoretic predicates for limit/colimit constructions.

**Updated path-(D) LOC estimate.** PR #19086 listed ~30–50 LOC for path
(D). That estimate appears to assume the trivial Mono = Iso collapse
that this memo refutes. Realistic LOC range:

- **(D.i)** in a concrete category (`ConcreteCategory C` instance + a
  `HasForget` functor) and bridging Bernstein on the underlying `Type`:
  ~100–200 LOC, depending on how much of `Function.Embedding.antisymm`
  must be re-derived to track categorical (rather than set) structure.
- **(D.ii)** abstract topos / strong-mono-category orbit argument:
  ~200–400 LOC, plus Mathlib-API gaps that may need new lemmas. (NOT
  recommended as a first non-vacuous milestone; defer to S10+.)

### 2.3 Path (E) — Banaschewski–Brümmer 1986

The 1986 paper "Thoughts on the Cantor-Bernstein theorem" (Quaestiones
Mathematicae 9, 1–27, cited in `knowledge.md`) gives the so-called
"retraction condition": for monos `m : X ↪ Y`, the existence of a
*coherent* family of retractions across the orbit of `n ∘ m : X ⟶ X`
yields SBP.

**Mathlib has no direct API.** Searching v4.26.0 for
`Bernstein`, `CantorBernstein`, `Schroeder`:

```
Mathlib/SetTheory/Cardinal/SchroederBernstein.lean
  — Function.Embedding.antisymm, the Set-theoretic SBP (existing,
    used by hasSBP_Type already).
Mathlib/Order/FixedPoints.lean
  — orderHomClass.fixedPoints, Tarski fixpoint — adjacent but not
    sufficient.
```

No `Mathlib.CategoryTheory.Schroeder*` file exists. Path (E) is a
genuine Mathlib gap: implementing the 1986 retraction condition in
Lean would be a Mathlib-contribution-worthy result and is well outside
a single research session's scope.

**LOC estimate (unchanged from PR #19086).** ~150–300 LOC for the
retraction-condition class + main theorem, modulo whether the orbit
argument is set-theoretic (via `ConcreteCategory`) or fully abstract.

## 3. Per-path summary table

| Path | Class needed | API ready? | Proof body LOC | Vacuous? | Excludes TopCat? | Cost | Value |
|------|--------------|-----------|----------------|----------|------------------|------|-------|
| (C)  | `Groupoid` (existing v4.26.0) | yes | ~3–5 | yes (same as S6) | yes | low | low (proper broadening of S6) |
| (D.i)  | `SplitMonoCategory + ConcreteCategory` | partial | ~100–200 | no | yes (TopCat lacks split monos for `[0,1]→(0,1)`) | medium | high (first genuinely non-vacuous SBP instance) |
| (D.ii) | abstract orbit-construction (NEW API) | no | ~200–400 + Mathlib helpers | no | yes | high | very high (Mathlib-contribution territory) |
| (E)  | full Banaschewski–Brümmer retraction class (NEW API) | no | ~150–300 | no | yes | high | very high (literature-matching) |

## 4. Sequencing recommendation

**S7 → path (C):** ship the `Groupoid` broadening. Rationale:

- API ready, ~3–5 LOC theorem body, Docker-build risk is essentially
  zero (no new imports beyond what S4 ACT already brought in via
  `CategoryTheory.Discrete.Basic`; `Groupoid.lean` is transitively
  imported).
- Proper broadening of `hasSBP_of_isDiscrete` — discrete ⇒ groupoid is
  strict (fundamental groupoid of `S¹` is a non-discrete groupoid).
- Maintains the slug's pos/neg corpus invariant: 4 positive + 1
  negative after S7, with the positives spanning Type/Discrete/Groupoid.
- Vacuous, yes — but the vacuity is *more informative* than S6's: it
  isolates "every mor is iso" as a single hypothesis subsuming both
  `Discrete` and `Groupoid` patterns, suggesting that any genuinely
  non-vacuous SBP must avoid forcing Mono = Iso.

**S8 → path (D.i) sketch:** doc-only PREP that picks one
`ConcreteCategory C` candidate (probably `Type` with `Function.Embedding.antisymm`
as the bridge), writes a verbatim theorem statement, and forecasts the
~100–200 LOC bridge surface. The actual ACT can wait for S9. This
splits the high-value, medium-cost work into a de-risked PREP + a
focused ACT.

**S10+ → path (E):** Banaschewski–Brümmer formalization is a long-tail
Mathlib contribution; multi-session and possibly upstream-coordination
work.

## 5. Build / pre-claim Docker forecast

This PREP is **doc-only**, so no pre-claim Docker baseline was run.
Per the memory `feedback_researcher_docs_only_chain_silent_parent_regression.md`,
the next ACT session (S7 path C) SHOULD pre-claim Docker-build
`Proofs.SchroederBernsteinOQ01` against `origin/main` before adding the
theorem. PR #19086 reported the post-edit job count as 3069 (same as
origin/main baseline); no transitive-import regression is expected
for a `Groupoid` reference since `Groupoid.lean` is already pulled in
via existing CategoryTheory imports.

If PR #19086 is merged before S7 ACT, the baseline shifts to 3069 jobs
(verified there). If S7 ACT pre-claims while PR #19086 is still open,
the baseline is the current origin/main (also 3069 per the most-recent
S6 BUILD UNBLOCKER session note from 2026-05-13). Both baselines are
identical for forecasting purposes.

## 6. Namespace and import sanity check

`Groupoid` lives in `CategoryTheory` namespace at
`Mathlib/CategoryTheory/Groupoid.lean`. Existing imports in
`SchroederBernsteinOQ01.lean`:

```
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.SetTheory.Cardinal.SchroederBernstein
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Category.TopCat.EpiMono
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic
```

`Mathlib.CategoryTheory.Groupoid` is pulled in transitively via
`Mathlib.Tactic` (which `public import`s a large portion of CategoryTheory).
Confirmed by `gh search` — no current file declares an explicit
`Mathlib.CategoryTheory.Groupoid` import gap. If S7 ACT chooses to
make the import explicit for documentation purposes, append a single
line; no transitive expansion expected (the module is already loaded).

## 7. Conflict-free PR scope guarantee

This memo's PR will:

| File | Change |
|------|--------|
| `research/problems/schroeder-bernstein-oq-01/sessions/2026-05-14-s7-prep-paths-cde-feasibility-audit.md` | **NEW** (this file, ~340 LOC) |

It does **not** modify:

- `state.md` (currently being rewritten by PR #19086 — would conflict)
- `problem.md`, `knowledge.md` (no new mathematical claims requiring entry)
- `src/data/research/problems/schroeder-bernstein-oq-01.json` (currently
  being bumped by PR #19086 — would conflict)
- Any `.lean` file in `proofs/Proofs/`
- Any gallery `meta.json`, `index.ts`, annotation file

Per memory `feedback_researcher_cross_pr_coordination_audit_pattern.md`,
this is the standard pattern for slugs with OPEN PRs touching shared
state: add ONLY a new dated session file; the next researcher merging
post-#19086 inherits this audit as input.

## 8. Forward look

After S7 (path C) ships, the slug's positive-instance corpus becomes:

| Instance | Hypothesis strength | LOC | Vacuous? |
|----------|---------------------|-----|----------|
| `hasSBP_Type` | none (Schroeder-Bernstein in `Set`) | ~10 | no |
| `hasSBP_Discrete` | `α : Type*` (any) | ~3 | yes |
| `hasSBP_of_isDiscrete` | `[IsDiscrete C]` | ~3 | yes |
| `hasSBP_of_groupoid` (S7 forecast) | `[Groupoid C]` | ~3 | yes |

The Type instance remains the **only non-vacuous positive** until path
(D) lands. This is honest: SBP in `Set` is genuinely a theorem of `Set`,
not an artifact of weakened categorical structure. The Discrete/Groupoid
instances illustrate the trivial regime where SBP holds because every
mor is iso.

The negative instance `not_hasSBP_TopCat` (S5 ACT, PR #18707, 0/0
verified) excludes `TopCat` from any of paths (C)/(D.i)/(D.ii)/(E)
because `TopCat` is not a groupoid, is not split-mono, and does not
satisfy the 1986 retraction condition (the [0,1] vs (0,1) inclusion
has no continuous retraction `(0,1) → [0,1]` because…actually, the
continuous inclusion `(0,1) ↪ [0,1]` does admit a retraction: define
`r : [0,1] → (0,1)` by clamping to `[1/4, 3/4]`; but `r ∘ i ≠ id` —
clamping breaks identity. So `i : (0,1) ↪ [0,1]` is mono in `TopCat`
but NOT split, confirming `TopCat ∉ SplitMonoCategory`.) The slug's
pos/neg corpus is internally consistent across all four S6/S7 paths.

## 9. Open questions for the S7 researcher

1. **Should S7 also bundle the parent-meta cross-reference update?**
   `state.md` Drift section notes that `Proofs/SchroederBernstein.lean`'s
   `meta.json` does not yet list `SchroederBernsteinOQ01.lean` in
   `additionalFiles`. Bundling this with S7 ACT may be efficient (one
   PR, one Docker build); but it expands PR scope outside the slug
   directory. Recommendation: defer to a separate "drift" PR by the
   auditor or enricher; keep S7 ACT slug-scoped.

2. **Should the S7 PR docstring forward-link to S8 path (D.i) plan?**
   This memo's §4 sequencing recommendation is one place to point to;
   recording it in the .lean module docstring (above `hasSBP_of_groupoid`)
   would make the vacuity-honesty visible to gallery readers. Suggested
   docstring sentence: "Path (D.i): non-vacuous SBP via concrete-category
   bridge to `Function.Embedding.antisymm` is deferred to S8+."

3. **Is path (C) "trivial" enough to skip and jump to (D.i)?**
   Honest assessment: yes, but the broadening from `IsDiscrete` to
   `Groupoid` is non-zero theory-level information — it isolates "every
   mor is iso" as the relevant vacuity-driver, which is a useful
   negative result (i.e., "anything strictly weaker than Groupoid will
   need a non-trivial argument"). Skipping (C) is acceptable; the value
   gained from shipping it is "framing benefit", not "new SBP territory".

## 10. Memory traps consulted

- `feedback_researcher_cross_pr_coordination_audit_pattern.md` — followed:
  this memo is doc-only, single new file under `sessions/`, conflict-free.
- `feedback_researcher_verify_blocked_on_upstream_mathlib_via_gh_api.md` —
  followed: every claim of API existence verified via
  `gh api repos/leanprover-community/mathlib4/contents/<path>?ref=v4.26.0`
  in §2.
- `feedback_researcher_docs_only_chain_silent_parent_regression.md` — noted:
  next ACT session must pre-claim Docker-build; this PREP does not.
- `feedback_researcher_state_sync_misses_top_level_phase.md` — not
  applicable (no JSON edits).
- `feedback_researcher_write_tool_worktree_path_footgun.md` — followed:
  `Write` path begins with
  `/Users/rwalters/GitHub/lean-genius/.loom/worktrees/researcher-12/`,
  not the main repo.
- `feedback_researcher_gh_pr_create_head_flag_origin_ambiguity.md` —
  noted for PR creation step.

## 11. Session-report summary (per researcher.md §"Session Report Format")

- **Mode**: REVISIT (slug at iter 6 + PR #19086 open for iter 7)
- **Problem**: `schroeder-bernstein-oq-01`
- **Prior status**: ACT iteration 6 on origin/main; PR #19086 OPEN proposes iter 7
- **Outcome**: doc-only PREP (no Lean, no JSON, no state.md)
- **Files modified**: 1 (this new sessions file)
- **Knowledge added**: 3 API-citation paths + path-(C) renaming
  correction + path-(D) vacuity refutation + sequencing recommendation
- **Next steps**: S7 ACT path (C) cheapest; S8 PREP path (D.i) before
  any non-vacuous ACT.
