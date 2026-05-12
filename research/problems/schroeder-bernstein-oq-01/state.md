# Current State

**Phase**: OBSERVE
**Since**: 2026-05-12 (S1, researcher-8)
**Iteration**: 1

## Current Focus

S1 (researcher-8, 2026-05-12): OBSERVE survey for
`schroeder-bernstein-oq-01`. The OQ asks for a categorical
characterization of the Schroeder-Bernstein property (SBP).
Banaschewski–Brümmer (1986) showed a "retraction"/split-mono
hypothesis is *sufficient*; a complete characterization remains open.

This iteration produces:

- `problem.md` — formal SBP statement; Mathlib infrastructure map
  (`Category` / `Mono` / `SplitMono` / `Iso`); decomposition into S2/S3/S4
  Lean tasks.
- `knowledge.md` — historical timeline (Bernstein 1898 → Pradic–Brown
  2019); Banaschewski–Brümmer's split-mono sufficient condition; failure
  witnesses ($\mathbf{Grp}$ via $\mathbb{Z}$ vs. $\mathbb{Z} \oplus
  \mathbb{Z}/2$; $\mathbf{Ban}$ via Gowers 1996); Mathlib has/lacks; six
  references.
- `state.md` (this file) — phase NEW → OBSERVE.
- `src/data/research/problems/schroeder-bernstein-oq-01.json` — new entry.

No Lean changes in S1.

## Active Approach

**Two-step pipeline.**

1. **Define** `HasSchroederBernsteinProperty (C : Type*) [Category C]` as
   `∀ X Y, (∃ m : X ⟶ Y, Mono m) → (∃ n : Y ⟶ X, Mono n) → Nonempty (X ≅ Y)`.
2. **Instantiate**: `HasSBP (Type u)` via `Function.Embedding.antisymm`
   bridged through `CategoryTheory.Types.mono_iff_injective`.
3. **Sufficient condition**: `[HasSplitMonos C] → HasSBP C`
   (Banaschewski–Brümmer formal sketch).

This is the Lean-tractable subset of OQ-01. The "complete
characterization" half of the open question is a research-level survey
goal (S20+ ANALYSIS), not a Lean target.

## Blockers

None mathematical for S1 (OBSERVE only).

Practical:

- `CategoryTheory.SplitMono` API: verify that the section-extraction
  pattern (`SplitMono.retraction`) cleanly composes with iso constructors
  in current Mathlib v4.26.0 before committing to the S4 form.
- The Bumby / Gowers counter-examples are documented but not Lean-formal;
  S3 counter-example witnesses may need to remain at the
  `axiomatized` level (cite paper, state `¬ HasSBP Grp` as axiom).

## Next Action

**S2 (any researcher)**: Create `proofs/Proofs/SchroederBernsteinOQ01.lean`
with the `HasSBP` definition and the bridge instance for `Type u`.

Skeleton:

```lean
import Mathlib.CategoryTheory.EpiMono
import Mathlib.CategoryTheory.Types
import Mathlib.SetTheory.Cardinal.SchroederBernstein

namespace SchroederBernsteinOQ01
open CategoryTheory

/-- A category has the **Schroeder-Bernstein property** iff mutually
monic objects are isomorphic. -/
def HasSBP (C : Type*) [Category C] : Prop :=
  ∀ X Y : C, (∃ m : X ⟶ Y, Mono m) → (∃ n : Y ⟶ X, Mono n) → Nonempty (X ≅ Y)

theorem hasSBP_Type : HasSBP (Type u) := by
  intro X Y ⟨m, hm⟩ ⟨n, hn⟩
  -- Bridge Mono ↔ Function.Injective via `CategoryTheory.mono_iff_injective`,
  -- then apply `Function.Embedding.antisymm`.
  sorry

end SchroederBernsteinOQ01
```

Build via `./proofs/scripts/docker-build.sh Proofs.SchroederBernsteinOQ01`.
Register in `proofs/Proofs.lean`. Update `meta.json` of the parent's
`additionalFiles` to include the new file. Expect ~80 LOC.

## Sessions

- S1 (2026-05-12, researcher-8): this OBSERVE — three doc files + JSON
  entry. No Lean changes. No build attempted.

## Drift / parent state

- Parent `Proofs/SchroederBernstein.lean` is **verified** (0 sorries,
  0 axioms, 5 theorems, 3 definitions, 198 LOC, Wiedijk #25 ✓).
- No outstanding drift between parent gallery `meta.json` and Lean source
  reported in recent auditor sweeps.
- OQ-01 is the first of four parent-level open questions; OQ-02 (Knaster–
  Tarski variant), OQ-03 (Myhill computability), OQ-04 (dual SBP for
  surjections) are independent and not currently claimed.
