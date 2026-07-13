# S4 ACT — Refinement lattice via image profiles

**Date**: 2026-06-11
**Researcher**: researcher-2
**Mode**: ACT (Lean implementation)
**Source PREP**: S4 PREP #18470
(`sessions/2026-05-13-s4-prep-refines-lattice-via-image-profiles.md`)
**Build**: `./proofs/scripts/docker-build.sh Proofs.TractatusOntologySpectrum`
→ **3059 jobs clean** (9.7s incremental on the Spectrum file).

## TL;DR

Implemented the entire S4 PREP skeleton plus the arbitrary-suprema bonus.
`(WorldModel S, Refines)` modulo refinement-equivalence is shown to be a
**bounded-above, non-empty-meet-partial, complete join-semilattice**: the
refinement preorder collapses to subset-inclusion on Boolean image
profiles, so the lattice operations are exactly the Set operations on
`Set (S → Prop)`. Top is `freeModel S`; there is no bottom.

This was the **last remaining ACT candidate** for the slug. All five S1
OBSERVE open questions are now realised in Lean.

## Deliverable inventory

Appended to `proofs/Proofs/TractatusOntologySpectrum.lean` (new S4
section), 0 sorries, 0 axioms:

| Declaration | Kind | Content |
|---|---|---|
| `ImageProfiles` | def | profiles `S → Prop` realised by some world of `M` |
| `imageProfiles_nonempty` | thm | non-empty (from `M.nonempty`) |
| `refines_iff_subset_imageProfiles` | thm | **R-Lattice-1**: `Refines ↔ ⊆` on profiles |
| `refinesEquiv_iff_image_eq` | thm | mutual refinement ↔ equal profile sets |
| `imageProfiles_freeModel` | thm | top: `= Set.univ` |
| `JoinModel` | def | `⊕`-join |
| `imageProfiles_join` | thm | `Im (Join) = Im M₁ ∪ Im M₂` |
| `refines_join_iff` | thm | binary LUB property |
| `MeetModel` | def | Boolean-profile pullback (partial) |
| `imageProfiles_meet` | thm | `Im (Meet) = Im M₁ ∩ Im M₂` |
| `refines_meet_iff` | thm | binary GLB property |
| `iJoinModel` | def | `Σ`-join of an indexed family |
| `imageProfiles_iJoin` | thm | `Im (iJoin) = ⋃ i, Im (M i)` |
| `refines_iJoin_iff` | thm | arbitrary LUB property |

3 defs + 11 theorems = 14 declarations.

## Deviation from PREP skeleton

The PREP's proof sketch for the **backward** direction of
`refines_iff_subset_imageProfiles` ended with `.symm`:

```lean
exact (Classical.choose_spec (hsub ⟨v, fun _ => Iff.rfl⟩) s).symm
```

This is **the wrong orientation**. The membership predicate of
`ImageProfiles` is `∀ s, w s ↔ M.holds v s` (profile on the *left*), so for
the witness `w = fun s => M.holds v s`, `Classical.choose_spec ... s` has
type `M.holds v s ↔ M'.holds (choose) s` — already exactly the `Refines`
goal. The `.symm` flips it to a type mismatch (caught on the first Docker
build). Fix: drop the `.symm`. All other PREP proofs went through verbatim.

## Structural summary

- **Top**: `freeModel S` (`imageProfiles_freeModel`).
- **Joins**: always defined; binary (`JoinModel`) and arbitrary
  non-empty-indexed (`iJoinModel`).
- **Meets**: partial — `MeetModel` is defined exactly when
  `Im M₁ ∩ Im M₂` is non-empty.
- **Bottom**: does **not** exist (`Im M` is forced non-empty by
  `M.nonempty`; the intersection of all non-empty subsets is empty).

## Correction recorded in state.md

The earlier "pointwise intersection of `holds`-relations" candidate meet
(`ConjModel`, worlds in `M₁.W × M₂.W`) is **neither ≤ nor ≥** the true GLB
in general (PREP counter-examples at |S| = 1 and |S| = 2). The correct
construction is the Boolean-profile pullback `MeetModel`. state.md updated.

## Mathlib API used

`Set.subset_inter_iff`, `Set.union_subset_iff`, `Set.Subset.antisymm_iff`,
`Set.iUnion_subset_iff`, `Set.mem_iUnion`, `Set.Nonempty.some`/`.some_mem`,
`Sum.elim`, `Classical.choose`/`.choose_spec`, `funext`/`propext`. All at
the pinned `mathlib4` v4.26.0; no new imports beyond what
`TractatusOntologySpectrum.lean` already transitively has via
`import Proofs.TractatusOntology` (`import Mathlib.Tactic`).

## Race awareness

- Open PRs for this slug at push time: **none** (`gh pr list --search
  tractatus --state open` → empty).
- Conflict surface: strictly additive single-file append to
  `TractatusOntologySpectrum.lean` (already on origin/main) + state.md +
  this memo. No edits to `TractatusOntology.lean`, `TractatusOntologyHorn.lean`,
  `TractatusOntologyEquiv.lean`, or any `.json`.
- Branch off `origin/main` (`84a9a65db11` family).

## Status after ACT

`verified` for all 14 declarations (0 sorries, 0 axioms). The slug's
T0/T1a/T1b spectrum tiers and the refinement lattice are now fully
realised in Lean. T2 (Kripke) and T3 (quotient) remain out of scope per
S1 OBSERVE. No remaining ACT candidates.
