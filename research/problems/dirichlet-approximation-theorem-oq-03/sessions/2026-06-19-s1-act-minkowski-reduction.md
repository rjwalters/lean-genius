# Session 2026-06-19 (Session 1) — ACT: Minkowski convex-body reduction

**Mode:** FRESH · **Outcome:** progress (verified reduction; volume crux remains open)

## What I did

- Surveyed both routes the open problem names:
  - **Minkowski / geometry of numbers.** Mathlib has the convex-body theorem
    `MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure` (compact,
    area-`= 2ⁿ` variant — the one we need, since our body has area exactly `4 = 2²·covol(ℤ²)`),
    plus the lattice fundamental-domain API `ZSpan.isAddFundamentalDomain` /
    `ZSpan.volume_fundamentalDomain` (covolume `1` for the standard basis) and the linear-image
    volume law `MeasureTheory.Measure.addHaar_image_linearMap`.
  - **Continued fractions.** Mathlib's `abs_sub_convergents_le'` gives
    `|v - Aₙ/Bₙ| ≤ 1/(bₙ·Bₙ·Bₙ)` and `abs_sub_convs_le` gives the sharper `1/(Bₙ·Bₙ₊₁)`;
    selecting the convergent with `Bₙ ≤ N < Bₙ₊₁` would yield Dirichlet, but assembling the
    index existence + denominator monotonicity + the rational-termination edge case is itself
    multi-lemma work (and only re-proves what pigeonhole already gives).

- Built (sorry-free, axiom-free) `Proofs/DirichletApproximationOQ03.lean` developing the Minkowski
  route up to the single remaining measure-theory crux:
  - `body α N` — the symmetric convex body `K = {v : ℝ² | |v 0| ≤ N ∧ |α·v 0 - v 1| ≤ 1/N}`.
  - `body_symm` — `K` is symmetric about the origin.
  - `body_convex` — `K` is convex (intersection of two linear slabs; `Convex.linear_preimage`).
  - `body_isClosed` — `K` is closed (preimages of closed `Icc` under continuous functionals).
  - `dirichlet_of_lattice_point` — **the arithmetic bridge**: for `N ≥ 2`, a nonzero integer point
    `(q₀, p₀)` of `K` is a Dirichlet approximation. Handles the sign normalisation to `1 ≤ q ≤ N`
    and proves the degenerate `q = 0` boundary point `(0, ±1)` cannot occur (it lies in `K` only
    when `N = 1`).
  - `dirichlet_via_convex_body` — Dirichlet's bound `|qα - p| ≤ 1/N`, conditional on the Minkowski
    conclusion (existence of a nonzero **integer** point of `K`).

## Key findings

- The **entire open content** of the Minkowski re-derivation collapses to one measure computation:
  `volume (body α N) = 4`. Every geometric hypothesis Minkowski consumes (symmetry, convexity,
  closedness) and the whole arithmetic back-end (lattice point ⇒ Dirichlet, with sign + boundary
  handling) is now machine-checked. This mirrors the structure of a clean Minkowski textbook proof:
  "area is 4, so there is a lattice point, so Dirichlet."

- The natural Minkowski output is the **non-strict** bound `|qα - p| ≤ 1/N`: the closed body has
  area exactly `4`, so only the `≤`-variant (`..._le_measure`) applies. The strict `< 1/N` of the
  pigeonhole entry needs the open-boundary refinement; the `≤` form is the honest geometry-of-numbers
  result.

- The `q = 0` boundary subtlety is real and is dispatched by requiring `N ≥ 2`: for `N ≥ 2` the only
  integer points with first coordinate `0` that could lie in `K` are `(0, ±1)`, excluded because
  `1 > 1/N`. `N = 1` is the trivial case of Dirichlet (`q = 1`, `p = round α`).

## Infrastructure assessment

**Needed to finish:** `volume (body α N) = 4`. The body is the image of the box
`[-N,N] × [-1/N,1/N]` (volume `4`) under the shear `(x,y) ↦ (x, αx - y)`, a linear map of
determinant `-1`; `addHaar_image_linearMap` gives the volume, but the bookkeeping (defining the
`LinearMap` on `Fin 2 → ℝ`, its `LinearMap.det` via `Matrix.det_fin_two`, the box volume via
`volume_pi`/`Real.volume_Icc`, and the `body = T '' box` set equality) is a self-contained
multi-lemma effort. Then feed `exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure` with
`L = Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin 2)))` and extract integer coordinates
(lattice-membership ⇒ integer coords) to discharge the `hMink` hypothesis of
`dirichlet_via_convex_body`.

**Size estimate:** the remaining volume + lattice glue is ~150–250 lines of measure-theory
bookkeeping (no missing Mathlib theory — purely assembly).

## Files modified

- `proofs/Proofs/DirichletApproximationOQ03.lean` (new, verified reduction)
- `proofs/Proofs.lean` (import)
- `src/data/research/problems/dirichlet-approximation-theorem-oq-03.json` (knowledge)
- `research/problems/dirichlet-approximation-theorem-oq-03/{problem,knowledge}.md` (re-persisted)

## Next steps

- Discharge `volume (body α N) = 4` via the shear change-of-variables, then assemble the
  unconditional `dirichlet_via_minkowski` from Mathlib's convex-body theorem.
- (Optional) settle the **subsumption** question by assembling the continued-fraction convergent
  selection, or record a literature note that pigeonhole/Minkowski/CF give the same `1/N` strength.
