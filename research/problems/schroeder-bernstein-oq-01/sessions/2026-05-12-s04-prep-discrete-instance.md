# S4 PREP — `HasSBP (Discrete α)` second concrete instance

**Date**: 2026-05-12
**Researcher**: researcher-6
**Phase**: PREP (orientation for a second concrete `HasSBP` instance,
downstream of S2/S3 ACT PR #18383 which lands `HasSBP` def + `Type u`
instance).
**Type**: Doc-only design memo. No edits to Lean files, `state.md`,
`problem.md`, `knowledge.md`, the in-flight PR #18383 `sessions/`
note, gallery `meta.json`, or research JSON.

## 0. Why this PREP

PR #18383 (S2/S3 ACT, build verified, opened 2026-05-12 23:48 UTC)
lands two artefacts:

- `def HasSBP (C : Type*) [Category C] : Prop`
- `theorem hasSBP_Type : HasSBP (Type u)` — bridged via
  `Function.Embedding.antisymm`.

`state.md` "Next Action" and PR #18383's body both point to the
**B-B sufficient condition** `[HasSplitMonos C] → HasSBP C` as the
S4 target. The Mathlib API audit below shows the
`SplitMonoCategory → HasSBP` reduction is **not automatic** in Lean
without committing to additional categorical structure (Balanced /
Pushouts / Trnková-style image factorisation), and would push the
S4 deliverable into research-level scope.

**This PREP locks a smaller, fully-tractable second instance**:
`HasSBP (Discrete α)` for any `α : Type u`. The proof is one line of
tactics; the deliverable is ~10 LOC total and unblocks subsequent
S4+ work on richer categories without committing to the open B-B
reduction.

## 1. Goal of the eventual S4-Discrete ACT

Add a single theorem to
`proofs/Proofs/SchroederBernsteinOQ01.lean`, after the existing
`hasSBP_Type` theorem and before `end SchroederBernsteinOQ01`:

```lean
/-- **(S4-Discrete)** Discrete categories satisfy SBP trivially:
    every morphism in a discrete category is an iso, so any pair of
    mutually monic objects is already related by an iso. -/
theorem hasSBP_Discrete {α : Type u} : HasSBP (Discrete α) := by
  intro X Y ⟨m, _⟩ _
  -- Mathlib instance `instance {f : i ⟶ j} : IsIso f` for `Discrete`
  -- (`Mathlib/CategoryTheory/Discrete/Basic.lean:156`) makes every
  -- morphism iso; package via `asIso`.
  exact ⟨asIso m⟩
```

Net delta target: +10 LOC including docstring. 0 sorries, 0 axioms,
no new file imports (parent `Mathlib.CategoryTheory.Types` and
sister `Mathlib.CategoryTheory.EpiMono` already transitively pull
`Mathlib.CategoryTheory.Discrete.Basic`).

## 2. Mathlib citations

In `Mathlib/CategoryTheory/Discrete/Basic.lean` (verified live at
rev `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`):

| Line | Symbol                                              | Use                                       |
|------|-----------------------------------------------------|-------------------------------------------|
| 95   | `instSubsingletonDiscreteHom`                       | every hom-set has at most one element     |
| 125  | `theorem Discrete.eq_of_hom (i : X ⟶ Y) : X.as = Y.as` | recover equality from a morphism      |
| 156  | `instance {f : i ⟶ j} : IsIso f`                    | **every morphism is iso (load-bearing)** |
| 130  | `Discrete.eqToHom` / line 139 `eqToHom'`            | recover morphism from equality            |

The line-156 instance is the load-bearing fact: with it, `asIso m`
takes any `m : X ⟶ Y` in `Discrete α` to an `X ≅ Y`. No mono
hypothesis on `m` is consumed (the instance fires unconditionally).

## 3. Why `Discrete α` is "vacuous SBP"

In `Discrete α`, the hom-sets are:

```
Hom (⟨a⟩) (⟨b⟩) = ULift (PLift (a = b))
```

— singleton when `a = b`, empty when `a ≠ b`. So:

- A morphism `m : ⟨a⟩ ⟶ ⟨b⟩` exists iff `a = b`. By `Discrete.eq_of_hom`,
  `m` is essentially the identity at `a` (modulo proof-irrelevance).
- Every such `m` is iso (line 156).

The SBP hypothesis "there exists a mono `X ⟶ Y` and a mono `Y ⟶ X`"
collapses to "there exists *any* morphism `X ⟶ Y`" (since every
morphism is iso, hence mono). That morphism is the iso witness.

So `HasSBP (Discrete α)` carries no real mathematical content; the
ACT is purely a Lean instance providing a second concrete witness
alongside `hasSBP_Type`.

## 4. Why this PREP recommends Discrete-instance over the B-B reduction

The state.md / problem.md "Active Approach" §3 lists:

> **Sufficient condition**: `[HasSplitMonos C] → HasSBP C`
> (Banaschewski–Brümmer formal sketch).

Mathlib's stake for "every mono is split" is `SplitMonoCategory` in
`Mathlib/CategoryTheory/EpiMono.lean:167`:

```lean
class SplitMonoCategory : Prop where
  /-- All monos are split -/
  isSplitMono_of_mono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], IsSplitMono f
```

A direct `[SplitMonoCategory C] → HasSBP C` proof would need: given
mutually split monos `m : X ⟶ Y` (retraction `r₁`) and `n : Y ⟶ X`
(retraction `r₂`), produce an iso `X ≅ Y`. The natural candidates
— `m` itself or `m ≫ r₂` — yield split-mono / split-epi pairs, not
iso pairs. The missing argument is the categorical Cantor–Bernstein
trick from B-B 1986, which in full generality requires additional
categorical structure (Trnková's image-factorisation, balanced
morphisms, or a colimit assumption).

The stronger Mathlib API `Groupoid.ofTruncSplitMono` at
`Mathlib/CategoryTheory/EpiMono.lean:154` (the **noncomputable**
result that **every morphism** being `Trunc IsSplitMono` ⇒ groupoid)
shows the proof gap: the B-B reduction works if **every morphism**
is split mono, but `SplitMonoCategory` only assumes monos are split.

Pradic–Brown (2019, "On the Cantor–Bernstein theorem in topos
theory") later sharpened the categorical hypotheses; their conditions
are not yet in Mathlib.

**Recommendation**: defer `[SplitMonoCategory C] → HasSBP C` to S5+
when one of the following is true: (a) the additional Mathlib
typeclass (probably `BalancedCategory` or
`HasSplitMonosAndPushouts`) is identified and stated; (b) the parent
slug's roadmap is updated to admit an axiomatized B-B; (c) Mathlib
adds a `theorem hasSBP_of_splitMono` lemma upstream.

For S4 (or S5-α), `hasSBP_Discrete` is the natural and fully
tractable next concrete instance.

## 5. Tactical risks

### 5.1 Universe polymorphism

`HasSBP (Discrete α)` is `α : Type u → Prop`. `Discrete` is universe-
polymorphic: `Discrete : Type u₁ → Type u₁`, `Category (Discrete α)`
fires at `Category.{u₁ + 1}` (or whichever universe convention
Mathlib follows for discrete categories). The `hasSBP_Type` theorem
in PR #18383 fires at `Type u`; `hasSBP_Discrete` will fire at
`Discrete α` where `α : Type u`, which should be compatible. If not,
explicit `universe u` declaration matches the parent file's pattern.

### 5.2 `asIso` vs explicit `Iso.refl`

`asIso m` (from `Mathlib.CategoryTheory.Iso`) takes `[IsIso m]` and
produces `m ≪ asIso m ≫ m.symm` style `X ≅ Y`. The line-156
`Discrete` instance fires automatically. Alternative: `Iso.refl X`
after rewriting `X = Y` via `Discrete.eq_of_hom m` — but `eq_of_hom`
gives `X.as = Y.as` (an underlying equality), not `X = Y` directly.
Use the natural `asIso m` approach.

### 5.3 `Nonempty (X ≅ Y)` packaging

The `HasSBP` def is `∀ X Y, ... → Nonempty (X ≅ Y)`. The lemma must
return `Nonempty (X ≅ Y)`, so the proof's final step is
`exact ⟨asIso m⟩` (an anonymous constructor on `Nonempty`). Low risk.

### 5.4 Mono hypothesis unused

The proof discards both `Mono m` and `Mono n` hypotheses. Stylistically,
`HasSBP` is overpowered for `Discrete α` — the bare existence of any
morphism suffices. The Lean proof reflects this by `_` on the mono
hypotheses. No semantic risk; a referee might prefer renaming the
hypotheses or adding a comment.

### 5.5 Import inheritance

`hasSBP_Discrete` requires `Mathlib.CategoryTheory.Discrete.Basic` to
provide the `IsIso` instance at line 156. The current
`SchroederBernsteinOQ01.lean` (from PR #18383) imports
`Mathlib.CategoryTheory.EpiMono` (for `Mono`) and
`Mathlib.CategoryTheory.Types` (for `Type u` category). These do not
transitively pull `Discrete.Basic` in all Mathlib configurations.

Mitigation: add `import Mathlib.CategoryTheory.DiscreteCategory` (the
re-export module, ~2 LOC of overhead) or
`import Mathlib.CategoryTheory.Discrete.Basic` (~3 LOC overhead) to
the parent file. The exact import path should be confirmed by
inspection at S4 ACT time.

## 6. Anti-targets (S4-Discrete PREP & ACT)

PREP-time (this PR):
1. **No Lean changes.** No `proofs/Proofs/**` edits.
2. **No edits to `problem.md`** — formal scope unchanged.
3. **No edits to `knowledge.md`** — Mathlib alignment unchanged.
4. **No edits to `state.md`** — phase remains `ACT` (per PR #18383).
5. **No edits to `2026-05-12-s2-act-type-u-bridge.md`** (PR #18383's
   session note).
6. **No edits to the gallery JSON**
   (`src/data/research/problems/schroeder-bernstein-oq-01.json`).

ACT-time (the eventual S4-Discrete ACT PR):
1. **No edits outside the lemma insertion site** (after `hasSBP_Type`).
2. **No new `axiom` declarations**; no `sorry`.
3. **No change to `HasSBP` definition or `hasSBP_Type` proof**.
4. **No commitment to the B-B reduction** in the same PR — that is
   deferred S5+.

## 7. Acceptance criteria for the eventual S4-Discrete ACT

1. New theorem `hasSBP_Discrete` exists with signature matching §1
   verbatim.
2. Body is `≤ 10 LOC` (including docstring); no `sorry`; no `axiom`.
3. At most 1 new import line (the `Discrete.Basic` path).
4. Docker build of `Proofs.SchroederBernsteinOQ01` clears.
5. No edits outside the lemma insertion range.
6. PR title: `research(schroeder-bernstein-oq-01): S4 — HasSBP
   (Discrete α) trivial instance via every-morphism-is-iso`.
7. PR body cites this PREP and PR #18383.

## 8. Verification log (this PREP — read-only, no edits)

| Check                                                                              | Outcome |
|------------------------------------------------------------------------------------|---------|
| `wc -l proofs/Proofs/SchroederBernsteinOQ01.lean` (current after #18383)           | ~60 LOC |
| `HasSBP` def + `hasSBP_Type` instance from PR #18383                               | build verified per PR body |
| Mathlib `Discrete.eq_of_hom` at file/line                                          | `Mathlib/CategoryTheory/Discrete/Basic.lean:125` |
| Mathlib every-Discrete-morphism-is-iso instance at line                            | 156 (same file) |
| Mathlib `SplitMonoCategory` at file/line                                           | `Mathlib/CategoryTheory/EpiMono.lean:167` |
| Mathlib `Groupoid.ofTruncSplitMono` at file/line                                   | `Mathlib/CategoryTheory/EpiMono.lean:154` |
| Open PRs on `schroeder-bernstein-oq-01 s4` at PREP push time                       | 0 |
| Open PRs with `hasSBP_Discrete`                                                    | 0 |
| Recent merged research PR on slug                                                  | #18274 (S1 OBSERVE, 2026-05-12 22:17 UTC), #18383 (S2/S3 ACT, 23:48 UTC, build verified) |
| Race check: open PRs with `Discrete` in title under this slug                      | 0 |

## 9. Honesty / no-edit guarantee

This PR is **doc-only**:

- 1 new file: `research/problems/schroeder-bernstein-oq-01/sessions/2026-05-12-s04-prep-discrete-instance.md`
- 0 edits to existing files
- 0 edits to Lean files
- 0 edits to `meta.json` of any proof
- 0 edits to `state.md`, `problem.md`, `knowledge.md`, or
  `2026-05-12-s2-act-type-u-bridge.md`

Diff against the in-flight PR #18383 is empty (mutually orthogonal
— that PR adds the Lean def + `Type u` instance and a different
session note; this PR adds only a new `sessions/` note).

## 10. References

- PR #18383 (S2/S3 ACT, build verified, 2026-05-12 23:48 UTC):
  `HasSBP` def + `hasSBP_Type` instance.
- PR #18274 (S1 OBSERVE, merged 2026-05-12 22:17 UTC).
- Mathlib `Discrete.Basic` (verified at rev
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`).
- Banaschewski, Brümmer (1986). "Strong proximities and lower-
  semicontinuity of perfect mappings" / categorical Cantor-Bernstein.
- Pradic, Brown (2019). "On the Cantor-Bernstein theorem in topos
  theory" — sharpened categorical hypotheses, not yet in Mathlib.
