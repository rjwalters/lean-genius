# Knowledge: erdos-1090-incomplete-01 (Monochromatic Collinear Points)

## Problem
Erdős #1090: for `k ≥ 3`, does a finite `A ⊂ ℝ²` exist such that every 2-coloring of `A`
admits a line carrying `≥ k` points of `A`, all the same color? **Answer: YES** for all
`k ≥ 3` (Graham–Selfridge for `k=3`; Hunter via Hales–Jewett in general).

## State of the formalization
`proofs/Proofs/Erdos1090Problem.lean` was already a complete, **0-sorry / 0-axiom**
formalization: `erdos1090_construction` derives the answer from Mathlib's Hales–Jewett
(`Combinatorics.Line.exists_mono_in_high_dimension`) via a generic linear projection
`φ p = ∑ j, (p j : ℝ) • !₂[1, w j]` of the combinatorial cube `[k]^ι` into the plane
(first coordinate of the line direction `= |varying| ≥ 1 > 0`, so collinear and distinct).

## Contribution this session [VERIFIED, 0-axiom]
The file *defined* the r-coloring generalization `Erdos1090Generalized k r` but only
asserted it in a prose comment ("Generalized Version Holds"). Closed that gap, and
removed proof duplication, by **generalizing the core construction over the color
palette**:

- **`erdos1090_construction_general (κ : Type*) [Finite κ] (k) (hk : k ≥ 3)`** — for any
  *finite* color type `κ`, a single finite `A ⊂ ℝ²` forces `k` monochromatic collinear
  points under every `κ`-coloring. The geometry is palette-independent; only the
  Hales–Jewett color argument changes from `Bool` to `κ`. This now *holds the full proof*.
- **`erdos1090_construction`** (the original 2-color statement) is now a 4-line corollary
  = the `κ = Bool` instance (re-shaping the `∀ p ∈ S, ∀ q ∈ S` monochromatic binder into
  `MonochromaticKCollinear`'s `∀ p q, p ∈ S → q ∈ S`). No behavioural change; ~90 lines of
  duplication eliminated.
- **`erdos1090_generalized_holds (k r)`** — proves the previously-unproven
  `Erdos1090Generalized k r` outright, as the `κ = Fin r` instance. (`r ≥ 2` is only for
  non-degeneracy; the construction works for any `r`.)

All four (`_general`, `_construction`, `_generalized_holds`, `erdos_1090`) compiled clean
and `#print axioms` = `[propext, Classical.choice, Quot.sound]` only.

GOTCHA: Hales–Jewett's `exists_mono_in_high_dimension (Fin k) κ` needs only `[Finite κ]`
on the color type — `Bool` and `Fin r` both qualify, so the generalization is "free" once
the geometry is abstracted from the palette. The only proof-text change versus the 2-color
original is the final monochromatic binder shape (`intro p hp q hq` for `∀ p ∈ S, ∀ q ∈ S`
vs `intro p q hp hq` for the curried `MonochromaticKCollinear`).

Verified via host `lake env lean` (docker daemon down): `cd proofs && bin/lake env lean
Proofs/Erdos1090Problem.lean` (wrapper passes `lake env`; worktree `.lake` symlinks main
cache).

### Next steps
- The r-coloring generalization could be promoted into the `erdos_1090_summary` bundle.
- `Erdos1090HigherDim` (planes in ℝ^d) remains a bare `Prop` with a `True` placeholder —
  a genuine open target: a generic projection of `[k]^ι` into ℝ^d landing varying
  coordinates on a common hyperplane.
