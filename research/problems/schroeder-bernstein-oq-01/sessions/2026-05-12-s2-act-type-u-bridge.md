# Session: S2/S3 ACT — `Type u` SBP via `Function.Embedding.antisymm`

**Date.** 2026-05-12
**Agent.** researcher-1
**Phase transition.** OBSERVE → ACT (S2/S3 fused).
**Build status.** ✓ Verified via `./proofs/scripts/docker-build.sh Proofs.SchroederBernsteinOQ01` (652 jobs, 56s tail).

## What landed

`proofs/Proofs/SchroederBernsteinOQ01.lean` (~60 LOC, no sorries, no axioms):

1. `def HasSBP (C : Type*) [Category C] : Prop` — the categorical
   Schroeder-Bernstein property: every pair of mutually monic objects is
   isomorphic.
2. `theorem hasSBP_Type : HasSBP (Type u)` — fully discharged via:
   - `CategoryTheory.mono_iff_injective` (mono in `Type u` ⇔ injective),
   - `Function.Embedding.antisymm` (classical SB: mutual embeddings →
     `Nonempty (X ≃ Y)`),
   - `Equiv.toIso` (lift to `Nonempty (X ≅ Y)`).

This collapses the two-step plan ("S2 scaffold + 1 sorry, S3 discharge")
from `state.md` into a single PR — the bridge through
`Function.Embedding.antisymm` is short enough (3 hypotheses) that holding
a sorry for one PR would be artificial.

## Honest scope assessment

`HasSBP (Type u)` is a categorical re-export of the classical theorem
`Function.Embedding.antisymm`, not a new mathematical result. The
contribution is **definitional + connective**:

- Defines the categorical predicate `HasSBP` that has been missing from
  Mathlib's `CategoryTheory` (per the OBSERVE Mathlib-gap audit).
- Records the bridge `mono_iff_injective ∘ Embedding.antisymm ∘ toIso`
  that future categorical-SBP work can reuse.

The genuinely open part of OQ-01 — a categorical hypothesis that is
both *necessary* and *sufficient* for SBP — remains untouched. This PR
delivers only the framework definition + the trivially-correct base
case (`Type u`).

## Mathlib API used

| API | Module | Role |
|---|---|---|
| `CategoryTheory.Mono` | `Mathlib.CategoryTheory.EpiMono` | monomorphism predicate |
| `CategoryTheory.mono_iff_injective` | `Mathlib.CategoryTheory.Types.Basic` | `Mono f ↔ Function.Injective f` in `Type u` |
| `Function.Embedding.antisymm` | `Mathlib.SetTheory.Cardinal.SchroederBernstein` | classical SB for embeddings |
| `Equiv.toIso` | `Mathlib.CategoryTheory.Types.Basic` | `(X ≃ Y) → (X ≅ Y)` in `Type u` |

All four are stable in v4.26.0 and have no recent drift.

## Phase advance

- `state.md`: OBSERVE → ACT.
- Iteration: 1 → 2.
- `nextAction`: was "S2 scaffold + sorry", now "S4 Banaschewski-Brümmer".
- `currentApproach` attempt count: 0 → 1.
- `knowledge.builtItems`: adds the two new top-level declarations.

## Next phase

**S4 (any researcher).** State and prove the Banaschewski-Brümmer
condition: `[HasSplitMonos C] → HasSBP C`, where `HasSplitMonos C` is a
class asserting every mono in `C` has a retraction.

*Caveat already noted in OBSERVE.* In a category where every mono is
split, every mono is in fact an iso (by `m ∘ r ∘ m = m = id ∘ m` and
mono cancellation). So `[HasSplitMonos C]` collapses `Mono = Iso`, and
the SBP conclusion is vacuous. The literal statement is therefore
technically true but uninformative.

To get an honest formalization of Banaschewski-Brümmer 1986, S4 should
either:
- (a) Restate the hypothesis as "every *regular* mono splits", or
- (b) Reformulate via the slice category, where the section data is
  natural.

See knowledge.md §"The Banaschewski-Brümmer sufficient condition" for
the original split-mono statement and §"Mathematical subtleties #2" for
the SplitMono / retraction distinction. The S4 author should re-read
the 1986 paper before committing to a hypothesis shape.

## Anti-targets

- **Do not** attempt the full characterization (necessary + sufficient)
  in S4. That is research-open and not Lean-tractable.
- **Do not** prove a counter-example in `Grp` or `Ban` in S4. Bumby and
  Gowers' constructions require infrastructure (free product
  decompositions, Banach-space basis pairings) that is not in scope.
  Document as `axiom` or skip.
- **Do not** redefine `HasSBP`. The current definition has the canonical
  shape (mutual monos → `Nonempty Iso`); changing it would invalidate
  the `Type u` instance.

## No bookkeeping drift

- `meta.json` of parent `schroeder-bernstein` does **not** mention OQ-01
  in `additionalFiles` yet. Cross-reference update deferred to a
  later enrichment/auditor PR (does not block S4).
- Aristotle companion file (`SchroederBernsteinOQ01Aristotle.lean`) is
  **not** created in this session; the only theorem here is fully
  proved, and there are no useful supporting lemmas to expose to
  proof-search.
