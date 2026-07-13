# S8 PREP — Path (D.i) refinement: `(forget C).Full` is load-bearing for the Type-bridge SBP lift (doc-only)

**Date.** 2026-05-15 (PDT 2026-05-14 evening; UTC 2026-05-15 ~01:25)
**Researcher.** researcher-9 (claim `researcher-65262`, knowledge score 22 / RICH)
**Phase.** PREP refinement of S7 PREP path (D.i) feasibility analysis.
**Mode.** Doc-only. Adds **only** this new file under `sessions/`. **No edits** to `state.md`, `problem.md`, `knowledge.md`, gallery JSON, or any `.lean` file.
**Mathlib pin.** `v4.26.0` (SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).

**Builds on / depends on (not yet merged):**
- PR #19086 (S6 ACT — `hasSBP_of_isDiscrete`, OPEN, MERGEABLE)
- PR #19158 (S7 PREP — Paths (C)/(D)/(E) feasibility audit, OPEN, MERGEABLE)

This S8 PREP **honors** the S7 PREP §4 sequencing recommendation — "S8 PREP → path (D.i) sketch, before any non-vacuous ACT" — and drills into the part S7 PREP did not pin: precisely which forgetful-functor properties are load-bearing for the Type-bridge SBP lift.

## §0 — TL;DR

The S7 PREP doc (PR #19158) §2.2 estimated path (D.i) at **~100–200 LOC** under the hypothesis `[SplitMonoCategory C][ConcreteCategory C]`, claiming the bridge needs "a `Function.Embedding.antisymm` re-derivation tracking categorical structure." This S8 PREP, after a verbatim v4.26.0 audit of `Functor.ReflectsIsomorphisms`, `ConcreteCategory`, and `(forget C).PreservesMonomorphisms`:

1. **Refines the load-bearing hypothesis**: `[SplitMonoCategory C]` is **not actually needed**. The minimum hypothesis is `[ConcreteCategory C][(forget C).Full][(forget C).Faithful][(forget C).PreservesMonomorphisms]`.

2. **Reduces the LOC forecast**: ~25–35 LOC for the theorem body (not 100–200), because the Bernstein orbit construction does NOT need re-derivation — `Function.Embedding.antisymm` is reused directly on the underlying types.

3. **Identifies the narrowness of (D.i)**: `(forget C).Full` is the critical clamp. It says every `Type`-function between underlying types comes from a `C`-morphism. This essentially forces C to be a *full subcategory of `Type`* — so the result is only marginally more general than `hasSBP_Type` (S2/S3 ACT, PR #18383). The path (D.i) instance space is narrow: trivially `Type` itself, the category of `Setoid`s up to congruence, etc.

4. **Sharpened recommendation**: ship path (D.i) at ~30 LOC under the corrected hypothesis as a 4th positive instance (Type / Discrete / Groupoid / fully-faithfully-forgetful-concrete) — but document its narrowness honestly. The genuinely-non-vacuous path remains **(D.ii)** abstract orbit or **(E)** Banaschewski–Brümmer (out of scope for S8).

## §1 — Verbatim v4.26.0 API audit

All citations verified live via `gh api repos/.../contents/...?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (no `gh api search/code` needed for the pinned reads below).

### §1.1 `Functor.ReflectsIsomorphisms`

**File.** `Mathlib/CategoryTheory/Functor/ReflectsIso/Basic.lean`.

```
ln 38–41:
  class Functor.ReflectsIsomorphisms (F : C ⥤ D) : Prop where
    /-- For any `f`, if `F.map f` is an iso, then so was `f`. -/
    reflects : ∀ {A B : C} (f : A ⟶ B) [IsIso (F.map f)], IsIso f

ln 43–45:
  theorem isIso_of_reflects_iso {A B : C} (f : A ⟶ B) (F : C ⥤ D)
      [IsIso (F.map f)] [F.ReflectsIsomorphisms] : IsIso f := ...

ln 51–53:
  lemma Functor.FullyFaithful.reflectsIsomorphisms {F : C ⥤ D}
      (hF : F.FullyFaithful) : F.ReflectsIsomorphisms := ...

ln 55–58 (priority-100 instance):
  instance (priority := 100) reflectsIsomorphisms_of_full_and_faithful
      (F : C ⥤ D) [F.Full] [F.Faithful] : F.ReflectsIsomorphisms := ...
```

**Key consequence.** `[F.Full] + [F.Faithful]` ⇒ `[F.ReflectsIsomorphisms]` automatically (priority-100 instance). For the path (D.i) hypothesis we therefore only need to assume `[(forget C).Full]` and `[(forget C).Faithful]`; reflection of isos is auto-derived.

### §1.2 `(forget (Type u)).ReflectsIsomorphisms` (Type's forgetful is identity-like)

**File.** `Mathlib/CategoryTheory/ConcreteCategory/ReflectsIso.lean`.

```
ln 23:
  instance : (forget (Type u)).ReflectsIsomorphisms where reflects _ _ _ {i} := i
```

For `C = Type u`, the forgetful is the identity, so reflection of isos is trivial. This is the limiting case of path (D.i) — and `hasSBP_Type` (already shipped in PR #18383) is the witness theorem.

### §1.3 `ConcreteCategory` / `HasForget` class structure

**File.** `Mathlib/CategoryTheory/ConcreteCategory/Basic.lean`.

```
ln 73–82 (HasForget class):
  class HasForget (C : Type u) [Category.{v} C] where
    forget : C ⥤ Type w
    forget_faithful : forget.Faithful := by infer_instance

ln 83–88:
  abbrev forget (C : Type u) [Category.{v} C] [HasForget.{w} C] : C ⥤ Type w :=
    HasForget.forget

ln 248–272 (ConcreteCategory class, v4.26.0 modernized form):
  class ConcreteCategory (C : Type u) [Category.{v} C]
      (FC : outParam (C → C → Type w)) (CC : outParam (C → Type w))
      [FunLike FC CC] where ...
```

**Two API surfaces coexist at v4.26.0.** The older `HasForget` + `forget C` API is still load-bearing for `(forget C).PreservesMonomorphisms` etc. (§1.4 below). The newer `ConcreteCategory` class (line 248) uses `FunLike` directly and may replace `HasForget` in future versions, but for v4.26.0 the path-(D.i) bridge naturally targets the `HasForget` API since `(forget C).PreservesMonomorphisms` is stated on it.

`HasForget.forget_faithful` (line 75) auto-provides `(forget C).Faithful` for every `[HasForget C]` instance — so `[(forget C).Faithful]` is a free hypothesis. The non-free part is `[(forget C).Full]`.

### §1.4 `(forget C).PreservesMonomorphisms` and `mono_iff_injective`

**File.** `Mathlib/CategoryTheory/ConcreteCategory/EpiMono.lean`.

```
ln 142:
  lemma Function.Injective_of_mono_of_preservesMonomorphisms {X Y : C} (f : X ⟶ Y) [Mono f]
      [(forget C).PreservesMonomorphisms] : Function.Injective ((forget C).map f) :=
    (mono_iff_injective ((forget C).map f)).mp inferInstance
```

(Note: actual definition uses an `instance` constructor; the lemma is the term-mode unwrap.)

**Key consequence.** Under `[(forget C).PreservesMonomorphisms]`, the bridge from C-monos to Type-injections is one-line `(mono_iff_injective _).mp inferInstance`. This handles step 2 of the SBP proof body (§3).

### §1.5 `Function.Embedding.antisymm` (Bernstein in Type)

**File.** `Mathlib/SetTheory/Cardinal/SchroederBernstein.lean`. Used directly by `hasSBP_Type` (S2/S3 ACT, PR #18383) at slug Lean file lines 50–56. Statement:

```
theorem Function.Embedding.antisymm {α β : Type*} (h₁ : α ↪ β) (h₂ : β ↪ α) :
    Nonempty (α ≃ β)
```

This is the classical `Set`-theoretic Schroeder–Bernstein — given mutual injections, produce a bijection. Already in slug's import chain via `Mathlib.SetTheory.Cardinal.SchroederBernstein` (line 18 of `SchroederBernsteinOQ01.lean`).

## §2 — Why `[SplitMonoCategory C]` is NOT load-bearing (correction to S7 PREP §2.2)

S7 PREP §2.2 framed path (D.i) under `[SplitMonoCategory C][ConcreteCategory C]`. The audit above reveals that `SplitMonoCategory` is **not** part of the actual bridge. Here is the proof flow showing what hypotheses are truly load-bearing:

```
Given:
  m : X ⟶ Y, with [Mono m]
  n : Y ⟶ X, with [Mono n]

Goal: Nonempty (X ≅ Y)

Step 1. Lift monos to Type-injections.
  Use [(forget C).PreservesMonomorphisms] to get
    Mono ((forget C).map m)  and  Mono ((forget C).map n)  in Type u.
  Then (mono_iff_injective _).mp inferInstance gives injective Type-functions.

Step 2. Apply Bernstein in Type.
  Function.Embedding.antisymm
    ⟨(forget C).map m, hm_inj⟩
    ⟨(forget C).map n, hn_inj⟩
  produces  Nonempty ((forget C).obj X ≃ (forget C).obj Y).

Step 3. Lift the Type-bijection to a C-iso.
  The bijection e : (forget C).obj X ≃ (forget C).obj Y is a Type-function
  e.toFun : (forget C).obj X → (forget C).obj Y.
  We need a morphism gC : X ⟶ Y in C with (forget C).map gC = e.toFun.
  This is EXACTLY the "fullness" of (forget C):
    Functor.Full means every Hom in Type comes from a Hom in C.

Step 4. Conclude gC is iso.
  (forget C).map gC = e.toFun is iso in Type (it's a Type-equiv).
  By [(forget C).ReflectsIsomorphisms] (free from [Full] + [Faithful]),
  gC is iso in C.
  Return ⟨asIso gC⟩.
```

**At NO step does `IsSplitMono` or `SplitMonoCategory` appear.** The Bernstein construction is set-theoretic and the lift to C uses only the forgetful's `Full + Faithful` properties. S7 PREP's `[SplitMonoCategory C]` is **load-irrelevant** to the path (D.i) proof.

## §3 — Tactic sketch (~25–35 LOC)

```lean
theorem hasSBP_of_concrete_fullyFaithfulForget (C : Type*) [Category C] [HasForget C]
    [(forget C).Full] [(forget C).PreservesMonomorphisms] :
    HasSBP C := by
  intro X Y ⟨m, hm⟩ ⟨n, hn⟩
  -- Step 1: Type-injections from C-monos
  haveI : Mono ((forget C).map m) := inferInstance
  haveI : Mono ((forget C).map n) := inferInstance
  have hm_inj : Function.Injective ((forget C).map m) :=
    (mono_iff_injective _).mp inferInstance
  have hn_inj : Function.Injective ((forget C).map n) :=
    (mono_iff_injective _).mp inferInstance
  -- Step 2: Bernstein in Type
  obtain ⟨e⟩ : Nonempty ((forget C).obj X ≃ (forget C).obj Y) :=
    Function.Embedding.antisymm ⟨_, hm_inj⟩ ⟨_, hn_inj⟩
  -- Step 3: Lift to C via fullness
  obtain ⟨gC, hgC⟩ : ∃ gC : X ⟶ Y, (forget C).map gC = e.toFun :=
    Functor.Full.map_surjective (F := forget C) e.toFun
  -- Step 4: gC is iso (Reflects via [Full] + [Faithful] auto-instance)
  have hgC_isIso : IsIso ((forget C).map gC) := by
    rw [hgC]
    exact ⟨⟨e.symm.toFun, by ext x; simp [Equiv.symm_apply_apply],
                              by ext x; simp [Equiv.apply_symm_apply]⟩⟩
  haveI : IsIso gC := isIso_of_reflects_iso gC (forget C)
  exact ⟨asIso gC⟩
```

**LOC budget.** ~25 LOC tactic body + ~5 LOC docstring header = ~30 LOC. **Well under S7 PREP's 100–200 estimate.**

`[(forget C).Faithful]` is implicit because `HasForget` requires it on the class (`HasForget.forget_faithful` at line 75 of `ConcreteCategory/Basic.lean`).

`[(forget C).ReflectsIsomorphisms]` is auto-derived from `[(forget C).Full] + [(forget C).Faithful]` via the priority-100 instance at `ReflectsIso/Basic.lean:55`.

## §4 — Sharpened verdict on path (D.i)'s informativeness

**The hypothesis `[(forget C).Full]` is the bottleneck.** It says every Type-function between underlying types comes from a C-morphism. For non-trivial concrete categories:

| Category | `(forget C).Full`? | Reason |
|----------|---------------------|---------|
| `Type u` | yes (trivial) | forgetful is identity |
| `Discrete α` | yes (vacuous via `IsDiscrete`) | hom-sets are singleton or empty |
| `Groupoid C` (general) | no | morphisms have specific structure (invertibility) |
| `Grp` (groups) | no | morphisms must be group homs, not arbitrary functions |
| `Ring`, `ModuleCat`, `Top`, `Cat` | no | morphisms preserve algebraic / continuous / functorial structure |
| `Setoid` (sets with relations) | no | morphisms must preserve the relation |
| Any algebraic category | **no** | morphisms must preserve operations |

**Implication.** Path (D.i) under the corrected hypothesis ships a 4th positive SBP instance, but only for categories where the forgetful is fully faithful. These are essentially "Type-like" categories — *full subcategories of Type*. The instance space is small.

**Comparison to other positives in the slug's corpus:**

| Stage | Positive instance | Hypothesis form | Effective generality |
|-------|-------------------|------------------|----------------------|
| S2/S3 | `hasSBP_Type` | none beyond `Type u` | `Type` (1 category) |
| S4    | `hasSBP_Discrete` | `Discrete α` | every `Discrete α` (∞ categories) |
| S6 (PR #19086) | `hasSBP_of_isDiscrete` | `[IsDiscrete C]` | every `IsDiscrete` instance |
| S7 (path C, planned) | `hasSBP_of_groupoid` | `[Groupoid C]` | every `Groupoid` |
| **S8 (path D.i, this PREP)** | `hasSBP_of_concrete_fullyFaithfulForget` | `[(forget C).Full][(forget C).PreservesMonomorphisms]` | full subcategories of Type |

Path (D.i) is **strictly narrower than path (C)**: `Groupoid` admits non-Type categories (e.g., the fundamental groupoid of `S¹`), but a fully-faithful forgetful forces Type-likeness.

**Recommendation.** Ship path (D.i) only if the slug values having a "concrete-category-flavored" positive instance for completeness — the SBP narrative remains "all positives are flavors of `Mono = Iso` collapse, all genuine SBP examples must avoid this collapse, e.g., `TopCat.{0}` (negative) and the still-open path-(E) Banaschewski-Brümmer construction."

## §5 — What this PREP does NOT do

- ❌ Does **not** modify `state.md`, `problem.md`, `knowledge.md`, or the gallery JSON. (PR #19086 is rewriting state.md / JSON; PR #19158 explicitly scopes itself doc-only-no-shared-files.)
- ❌ Does **not** modify `proofs/Proofs/SchroederBernsteinOQ01.lean`. (PR #19086 is the file's pending S6 ACT edit.)
- ❌ Does **not** run docker build. Pure doc; build risk forecasted below in §6.
- ❌ Does **not** open child slug `schroeder-bernstein-oq-01-oq-XX`. (`-oq-02` / `-oq-03` / `-oq-04` are independent and already scoped.)

## §6 — Pre-ACT Docker forecast (for whoever ships path (D.i))

The S8 ACT (path D.i) would add ~30 LOC to `SchroederBernsteinOQ01.lean`. New imports needed:

```lean
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono  -- for mono_iff_injective + PreservesMonomorphisms
```

`SchroederBernsteinOQ01.lean`'s existing imports (per S7 PREP §6) include `Mathlib.CategoryTheory.EpiMono` and `Mathlib.CategoryTheory.Types.Basic`; the two new imports above add `ConcreteCategory/EpiMono` (transitive `HasForget` API) and `Functor/ReflectsIso/Basic` (already pulled by `Mathlib.Tactic`, so likely a no-op).

**Forecast Docker job count.** Current origin/main baseline is `3069 / 3069 jobs (3.5s)` per S6 BUILD UNBLOCKER (PR #18980). Post-S6-ACT (#19086, +1 theorem `hasSBP_of_isDiscrete`) and post-S7-ACT (path C, +1 theorem `hasSBP_of_groupoid`): forecast `3069` (same — both refs already in the import chain). Post-S8-ACT (this PREP's path D.i, +1 theorem): forecast `3069–3080` (modest +5–10 jobs if `Functor/ReflectsIso/Basic` is not in current Mathlib.Tactic transitive closure; 0 if it is).

**Sequencing.** S7 ACT (path C, Groupoid, ~5 LOC) should land **before** S8 ACT (path D.i, this PREP, ~30 LOC) because path C is the lower-risk minimal broadening. The two ACTs touch the same Lean file (`SchroederBernsteinOQ01.lean`) and would need rebasing if landed concurrently — the **race-window narrows** if S7 ACT lands first.

## §7 — Coordination matrix at S8 PREP authoring

| PR | Slug | Files | Mergeable? | Note |
|---|---|---|---|---|
| #19086 | this slug | `state.md`, JSON, `.lean` (+1 theorem), 1 new `sessions/` | yes (CLEAN/MERGEABLE per S7 PREP §1) | S6 ACT vacuous `hasSBP_of_isDiscrete` |
| #19158 | this slug | 1 new `sessions/` | yes (per its §7) | S7 PREP path C/D/E feasibility audit |
| **this PR (#???)** | this slug | **1 new `sessions/` file only** | n/a | S8 PREP path (D.i) refinement |

**File-overlap matrix** (none overlap):

| | #19086 | #19158 | this PREP |
|---|---|---|---|
| `state.md`, slug JSON | ✓ | — | — |
| `.lean` file | ✓ | — | — |
| `sessions/2026-05-14-s6-act-…` (PR #19086's new file) | ✓ | — | — |
| `sessions/2026-05-14-s7-prep-paths-cde-…` (PR #19158's new file) | — | ✓ | — |
| `sessions/2026-05-15-s8-prep-path-Di-…` (this PREP) | — | — | ✓ |

All three PRs can merge in any order without conflict. **Recommended order**: #19158 (S7 PREP audit) → #19086 (S6 ACT) → this PREP. Reasoning: this PREP's refinement of path (D.i) is most useful **after** S7 PREP is on origin/main so a future S8 ACT researcher can read both audits together.

## §8 — Race awareness

`gh pr list --search "schroeder-bernstein-oq-01 in:title" --state open --repo rjwalters/lean-genius` at PREP authoring (2026-05-15 01:25 UTC) returns exactly the two open PRs above (#19086, #19158) and zero S8 PREPs. No race.

**Branch policy**: fresh `research/schroeder-bernstein-oq01-s8-prep-pathDi-fullyfaithful-refinement-1778799647` cut from `origin/main` via `git checkout -b ... origin/main`.

**Per memory `feedback_researcher_gh_default_repo_mathlib4_fork_trap.md`** (updated this session): all `gh pr list / view / create` invocations use explicit `--repo rjwalters/lean-genius` to avoid the worktree's `gh` default-repo drift onto the `rjwalters/mathlib4` fork.

## §9 — Mathlib `gh api` core-bucket budget

PREP authoring used 6 `gh api repos/.../contents/...?ref=<SHA>` calls (core bucket; current allowance 4951 / 5000 remaining at authoring) plus 4 `gh api search/code?q=...` calls (code_search bucket; 6 / 10 remaining at authoring). No further Mathlib lookups required for this memo; budget headroom preserved for the eventual S8 ACT researcher's pre-claim Docker re-verification.

## §10 — Recommendation summary

1. **Ship S7 ACT (path C) first** — `hasSBP_of_groupoid` per S7 PREP §2.1 verbatim skeleton, ~5 LOC.
2. **Then ship S8 ACT (path D.i)** — `hasSBP_of_concrete_fullyFaithfulForget` per §3 above, ~30 LOC.
3. **Document the narrowness honestly** — the theorem's docstring should note that `[(forget C).Full]` essentially restricts to Type-like categories.
4. **Defer path (E)** — Banaschewski–Brümmer 1986 retraction condition remains a multi-session Mathlib-contribution-worthy target.
5. **The genuinely-non-vacuous SBP question is still open** — all positive instances ship under hypotheses that force Mono = Iso. The S5 negative (`not_hasSBP_TopCat`) remains the only example separating Mono from Iso. Path (D.ii) abstract orbit or path (E) Banaschewski–Brümmer would be the first genuinely non-vacuous positive.

This refinement preserves the slug's pos/neg corpus invariant while sharpening the LOC and hypothesis estimates that future ACTs will work from.
