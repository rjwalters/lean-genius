# S10 ACT — integral-basis bricks toward `discr Q(√2) = 8`

**Date**: 2026-07-24
**Agent**: researcher-2
**Mode**: REVISIT (RICH, score 22; same-day continuation of S9)
**Outcome**: 4 build-verified bricks on the critical path of the sole
remaining sorry (`Q_sqrt2_discr_eq_eight`); sorry count unchanged (1).

## What was proved (new S10 section, ~120 LOC)

1. `root_sq` — `root² = 2` internally (no embedding), factored out of
   `embedding_root_sq`'s proof.
2. `root_isIntegral` — `root` is an algebraic integer (monic `X² − 2`);
   the easy inclusion `ℤ[root] ⊆ 𝓞`.
3. `rat_int_of_sq_int` — a rational whose square is an integer is an
   integer: monic-quadratic integrality + `IsIntegrallyClosed.isIntegral_iff`
   (ℤ integrally closed, ℚ its fraction field).
4. `int_pair_of_double_and_norm` — **the arithmetic crux of
   `𝓞 ⊆ ℤ[√2]`**: `2a ∈ ℤ` (trace) and `a² − 2b² ∈ ℤ` (norm) force
   `a, b ∈ ℤ`. Chain: `(4b)² = 2(u² − 4N) ∈ ℤ` → `4b ∈ ℤ` (brick 3) →
   `4b` even (square even) → `v := 2b ∈ ℤ` → mod-4 obstruction:
   `4N = u² − 2v²` with `v` odd gives `u² = 2` in `ZMod 4`, killed by
   `∀ x : ZMod 4, x² ≠ 2 := by decide` → `b ∈ ℤ` → `a² = N + 2b² ∈ ℤ` →
   `a ∈ ℤ` (brick 3 again).

## Lean recipe notes

- All the rational bookkeeping is `push_cast` + `linear_combination` with
  hand-computed coefficients (e.g. goal `(4b)² = 2(u²−4N)` from
  `hu : u = 2a`, `hN : N = a²−2b²` is
  `linear_combination (-2(u+2a))·hu + 8·hN`). No `Rat.den` internals
  anywhere — integrality of rationals is routed through
  `IsIntegrallyClosed.isIntegral_iff` instead.
- The mod-4 case analysis is one `by_contra` + `Int.not_even_iff_odd` +
  `ZMod 4` cast; `congrArg (fun t : ℤ => (t : ZMod 4))` + `push_cast`
  transports the integer identity; `(4 : ZMod 4) = 0 := by decide` feeds
  `linear_combination` to collapse `(2j+1)² = 1`.
- `Even w` from `Even (w²)` via `Int.even_pow`.

## S11 roadmap (consume the bricks)

1. Trace/norm formulas on the power basis: `trace ℚ (a + b·root) = 2a`,
   `norm ℚ (a + b·root) = a² − 2b²` (via `PowerBasis.trace_eq_...` /
   `Algebra.norm_eq_matrix_det` or the two-embeddings product — the
   totally-real machinery from S9 gives both embeddings).
2. `𝓞 = ℤ[root]`: for `x = a + b·root` integral, trace and norm are
   integers (`IsIntegral.trace_mem`? — check exact bearer: minpoly of
   integral element has ℤ coefficients via
   `minpoly.isIntegrallyClosed_eq_field_fractions`), feed brick 4.
3. `Basis (Fin 2) ℤ (𝓞)` from `{1, ⟨root, root_isIntegral⟩}` (span from
   step 2, linear independence from the ℚ power basis).
4. `NumberField.discr_eq_discr` + trace-form determinant
   `[[2, 0], [0, 4]] → 8`.

Estimate: 1 full session (the trace/norm formulas are the main risk).
