# napoleons-theorem-oq-03 — Spectral Complementarity and Shape Annihilation

**Status:** COMPLETED (0 axioms / 0 sorries, machine-verified)
**Lean file:** `proofs/Proofs/NapoleonsTheoremOQ03.lean` (171 lines, 12 theorems)
**Parent:** napoleons-theorem (base construction) · sibling napoleons-theorem-oq-02 (DFT picture)

## Problem

OQ-02 established that the outer and inner Napoleon constructions act as
**complementary spectral filters** on the 3-point DFT of the vertices:

- outer: `(X₀, X₁, X₂) ↦ (X₀, -X₁, 0)` — zeroes frequency-2, negates frequency-1
- inner: `(X₀, X₁, X₂) ↦ (X₀, 0, -X₂)` — zeroes frequency-1, negates frequency-2

It states each filter separately. The open follow-up: **compose them.**

## Result

Composing the two filters (in either order) annihilates *both* non-DC
frequencies:

- outer ∘ inner: `X₁ ↦ 0 ↦ 0`, `X₂ ↦ -X₂ ↦ 0` ⟹ `(X₀, 0, 0)`
- inner ∘ outer: `X₁ ↦ -X₁ ↦ 0`, `X₂ ↦ 0 ↦ 0` ⟹ `(X₀, 0, 0)`

A spectrum `(X₀, 0, 0)` is the **constant triangle**: all three vertices coincide
at `X₀/3 = (z₁+z₂+z₃)/3`, the centroid of the original triangle. So performing
both Napoleon constructions destroys the triangle's shape entirely, leaving only
the centroid — the sharp structural statement of the complementarity.

## Key insights

- Each Napoleon vertex map is **ℂ-affine** in the input vertices, so every composed
  vertex is a polynomial identity over ℂ — no real/imaginary case-splitting needed.
- The *only* non-ring fact is the displacement-square identity
  `a² = (i√3/6)² = -1/12` (`disp_sq`, from `Complex.I_sq` and `sqrt3_sq`).
- Each collapse reduces to `coeff · (a² + 1/12)` with
  `coeff ∈ {2z₁-z₂-z₃, -z₁+2z₂-z₃, -z₁-z₂+2z₃}`, closed by a single deterministic
  `linear_combination coeff * disp_sq`. This is far more robust than the
  `Complex.ext`/`nlinarith` idiom used in the parent/OQ-02 (one tactic, no
  numerical search).
- outer∘inner and inner∘outer give the **same** composed vertex maps
  (`outer_inner_eq_inner_outer`): the two constructions commute on shape.
- `doubled_napoleon_is_centroid` sharpens `napoleon_centroid_eq_original`: not only
  is the centroid preserved, *everything else is destroyed*.

## Builtitems

- `disp_sq` — `(i√3/6)² = -1/12`
- `outer_inner_G₁/₂/₃`, `inner_outer_G₁/₂/₃` — six per-vertex collapses to centroid
- `outer_of_inner_collapses`, `inner_of_outer_collapses` — packaged annihilation
- `outer_inner_eq_inner_outer` — the two orders agree
- `outer_of_inner_degenerate` — vertices pairwise equal (degeneracy certificate)
- `doubled_napoleon_is_centroid` — sharpening of centroid preservation

## Possible follow-ups (not pursued)

- Iterating a *single* construction (outer ∘ outer): `X₁ ↦ -X₁ ↦ X₁`, `X₂ ↦ 0`,
  so the doubly-outer triangle preserves frequency-1 and stays equilateral.
- n-gon generalization (Petr–Douglas–Neumann): the n-point analogue annihilates
  all but one frequency per construction; composing the n−1 constructions collapses
  any n-gon to its centroid. Heavy (needs n-point DFT infrastructure).

## Session log

### 2026-06-18 (S1, FRESH) — COMPLETED
Designed and proved the spectral-complementarity / shape-annihilation theorems.
Verified the `linear_combination` coefficients by hand for all six composed
vertices before building. New file, registered in `Proofs.lean`.
