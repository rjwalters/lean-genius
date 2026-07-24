# S18 ACT (researcher-1, 2026-07-24): headline iff PROVEN — file 0 sorries, 0 axioms

## What happened

The S17-era single sorry — the headline criterion
`concyclicityDet_eq_zero_iff_concyclic` — is discharged. The file
`Proofs/ProductOfSegmentsOfChordsOQ03.lean` grows 265 → 525 LOC and now has
**0 sorries, 0 axioms**.

Two things beyond a plain "paste the Cramer proof" were required:

1. **The statement itself had to change.** The S2 stub carried
   `(hNonCollinear : True)` as a placeholder. With that placeholder the (⟹)
   direction is *false*: four distinct collinear points have Δ = 0 (the
   `(x, y, 1)` columns are already dependent) but lie on no common circle of
   positive radius. S18 installs the genuine hypothesis
   `¬ Collinear ℝ ({P₁, P₂, P₃} : Set Vec2)` — the affine-geometry notion, not
   a bare determinant inequality — and proves the bridge to the algebraic form.
2. **The declaration moved to the end of the file** (new Part 12) because its
   proof consumes Parts 5–11; Part 4 now holds a pointer note. Any tooling
   anchored to line 119 should re-anchor.

## New material (Parts 9–12)

- Part 9 — `collinearityDetCoords` / `collinearityDet` (= 2·signed triangle
  area, also the bottom cofactor M₄ of the concyclicity matrix) and
  `collinear_of_collinearityDet_eq_zero`: vanishing determinant ⟹
  `Collinear ℝ`, via `collinear_iff_of_mem` with direction `P₂ - P₁`
  (or `P₃ - P₁` in the degenerate `P₂ = P₁` case); the scalar for `P₃` is the
  coordinate ratio, with `field_simp` + `linear_combination h` supplying the
  determinant-driven second coordinate. Contrapositive wrapper
  `collinearityDet_ne_zero_of_not_collinear`.
- Part 10 — `circumcenter_spec` (private, pure coordinates): explicit Cramer
  solution of the two perpendicular-bisector equations; both equal-radius
  facts close by `field_simp [hd]; ring`. `exists_circumcircle` lifts it to
  `Vec2` (center built with `WithLp.toLp 2 ![O₀, O₁]`; coordinate projections
  are `rfl`), converts squared-distance equalities to norm equalities via
  `pow_left_inj₀`, and gets `0 < r` because `r = 0` would force `P₂ = P₁`
  and hence a vanishing collinearity determinant.
- Part 11 — `concyclicityDetCoords_circle_decomp`: the exact polynomial
  identity `Δ = e₁M₁ - e₂M₂ + e₃M₃ - e₄M₄` (eᵢ = circle defect of Pᵢ, Mᵢ =
  3×3 minor of the (x,y,1) columns omitting row i; M₄ = collinearityDet).
  Proof: the S7b det-expansion simp set + `ring`; hand-verified numerically
  on two (O, r) instances before shipping. `fourth_point_on_circle` then
  collapses the identity to `e₄ · M₄ = 0` by `linear_combination` with the
  three explicit minor coefficients and forces `e₄ = 0`.
- Part 12 — the assembled iff; (⟸) is the S17-era
  `concyclic_implies_concyclicityDet_zero`, unchanged.

## Verification

- Baseline docker build at origin/main HEAD first (v4.31 drift check): GREEN,
  only the expected line-119 sorry warning, 3034 jobs.
- Post-change docker build: see PR (expected GREEN, 0 warnings).

## What the next session owes

The S1 decomposition's remaining steps, unchanged in scope:

- **S5 bridge**: signed chord-product hypothesis ⟹ Δ = 0, using
  `signed_inner_product_to_scalar_coord` + `coord_of_smul_diff` (Parts 6-7,
  already merged) + the S12-§3.2 closed-form witness.
- **S6 parent integration**: replace
  `converse_product_implies_concyclic_axiom` in
  `Proofs/ProductOfSegmentsOfChords.lean` (line ~468) by a theorem derived
  from Part 12 + the S5 bridge, then parent gallery meta
  axiomatized → verified. Note the parent axiom's hypothesis must be the
  *signed* product (S9 PREP counterexample kills the unsigned form) and a
  non-collinearity side condition now provably enters.

No gallery entry exists for oq-03 itself (never created; integration is the
parent's, at S6).
