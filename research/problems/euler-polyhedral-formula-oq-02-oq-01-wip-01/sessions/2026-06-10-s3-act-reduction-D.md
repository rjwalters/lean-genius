# Session 3 — 2026-06-10 — ACT: Reduction D (operationalize `VectorFieldOnSurface.noZeros`)

**Researcher**: researcher-1
**Problem**: euler-polyhedral-formula-oq-02-oq-01-wip-01
**Status before session**: ORIENT, iteration 2 (S2 produced a per-field assumption inventory + cost-ordered reduction plan: D > B > C > skip A)
**Mode**: ACT (executes the priority recommendation of S2)
**Outcome**: Lean code change, Docker-verified. Parent meta.json `axiomCount: 10 → 9`.

## What was attempted

Reduction D, as specified in `sessions/2026-06-09-s2-orient-assumption-inventory.md`:

> *Currently `noZeros : Prop` is an abstract placeholder. Replace with a concrete predicate (e.g., the vector field has no critical points, expressed as some `∀ p, V p ≠ 0`). Then `nonvanishing_index` is `noZeros → totalIndex = 0` which is the trivial "sum over empty set of zeros is 0" — derivable from `Finset.sum_empty`.*

The S2 plan flagged a risk: the existing `VectorFieldOnSurface` carries `totalIndex : ℤ` as a free field and `noZeros : Prop` with zero semantic content. To make `nonvanishing_index` derivable, we need *some* concrete representation of the zero set so that "no zeros" maps to "empty zero set" maps to `Finset.sum_empty`.

The cheapest such representation that doesn't add new deep assumptions is to record the zero set explicitly as a `Finset ℕ` of index labels, with the per-zero index value carried as a separate function `indexAt : ℕ → ℤ`. The total index then becomes a definitional sum, and `noZeros` is the proposition that the zero set is empty.

## The change

**Before** (5 structure fields, 3 of them assumption-bearing):
```lean
structure VectorFieldOnSurface where
  surface : CompactRiemannianSurface
  totalIndex : ℤ
  noZeros : Prop
  poincare_hopf : totalIndex = surface.chi
  nonvanishing_index : noZeros → totalIndex = 0
```

**After** (4 structure fields, 1 of them assumption-bearing; the discharged assumption is now a derived theorem):
```lean
structure VectorFieldOnSurface where
  surface : CompactRiemannianSurface
  zeros : Finset ℕ        -- index labels for isolated zeros
  indexAt : ℕ → ℤ          -- index value at each labelled zero
  poincare_hopf : (∑ i ∈ zeros, indexAt i) = surface.chi

namespace VectorFieldOnSurface
def totalIndex (V : VectorFieldOnSurface) : ℤ := ∑ i ∈ V.zeros, V.indexAt i
def noZeros    (V : VectorFieldOnSurface) : Prop := V.zeros = ∅

theorem nonvanishing_index (V : VectorFieldOnSurface) (h : V.noZeros) :
    V.totalIndex = 0 := by
  show (∑ i ∈ V.zeros, V.indexAt i) = 0
  rw [show V.zeros = ∅ from h]
  exact Finset.sum_empty
end VectorFieldOnSurface
```

The downstream `hairy_ball` was updated only to pin the elaborator on the unfolded form of `totalIndex` for `omega`:
```lean
theorem hairy_ball (V : VectorFieldOnSurface) (h : V.noZeros) :
    V.surface.chi = 0 := by
  have h1 := V.poincare_hopf
  have h2 : (∑ i ∈ V.zeros, V.indexAt i) = 0 := V.nonvanishing_index h
  omega
```

The four other downstream consumers (`sphere_no_nonvanishing_field`, `positive_chi_has_zeros`, `negative_chi_has_zeros`, `nonvanishing_iff_chi_zero`) call `hairy_ball` and use `V.noZeros` only as a hypothesis — they required no edits.

## Why this is an honest reduction (axiom integrity check)

Per the project's axiom integrity policy: structure fields that encode mathematical assumptions count as axioms, regardless of whether `axiom` keyword is used. The relevant question is whether removing `nonvanishing_index` from the field list and proving it instead actually reduces the assumption count, or whether the assumption "leaks" into the new structure shape.

The answer: **the reduction is real**, for two reasons:

1. The old `nonvanishing_index : noZeros → totalIndex = 0` was a *free* implication. With `noZeros : Prop` abstract and `totalIndex : ℤ` free, the implication carried information that the assumption-pool cannot otherwise derive. Removing it as a field and providing it as a theorem requires that the theorem actually be provable — which it is, from the new concrete representation.

2. The new structure does not introduce a new deep assumption. The Poincaré-Hopf field stays — it just gets rephrased from `totalIndex = surface.chi` to `(∑ i ∈ zeros, indexAt i) = surface.chi`. These are the same mathematical claim (one is the def-equal form of the other after the `totalIndex := ∑ ...` definition is supplied). No new content is added; no content is hidden behind the def.

The `zeros : Finset ℕ` and `indexAt : ℕ → ℤ` fields are *data*, not assumptions. They can be inhabited arbitrarily; the only constraint comes from `poincare_hopf`.

Net effect on the axiom integrity audit:
- Removed field: `nonvanishing_index` (was counted as 1 of 10 assumptions).
- Added/changed fields: `zeros`, `indexAt` (data), `totalIndex` and `noZeros` defs (derived), `nonvanishing_index` theorem (derived).
- Restated field: `poincare_hopf` (now phrased on `∑` rather than on `totalIndex`, but same content).

`axiomCount: 10 → 9`.

## Docker verification

```
$ LEAN_BUILD_TIMEOUT=20m ./proofs/scripts/docker-build.sh Proofs.EulerPolyhedralOQ02OQ01
…
✔ [7743/7743] Built Proofs.EulerPolyhedralOQ02OQ01 (88s)
Build completed successfully (7743 jobs).
=== Build succeeded ===
```

No new sorries, no new top-level `axiom` declarations, all downstream consumers compile.

## What S4 should do

S4 ACT should attempt **Reduction B** as planned: derive `GeodesicPolygon.gauss_bonnet_polygon` from `CompactSurfaceWithBoundary.gauss_bonnet_boundary` via a `toBoundary` coercion. The sketch is in `sessions/2026-06-09-s2-orient-assumption-inventory.md` §Reduction B. Expected: `axiomCount: 9 → 8`.

Risk per S2: identifying `boundaryGeodCurv` with `exteriorAngleSum` is a non-trivial discrete identity. For *geodesic* arcs the smooth boundary contributions are zero and only vertex angles contribute — which matches the polygon's `exteriorAngleSum`. The identity is encodable inside the `toBoundary` constructor.

## Files modified

- `proofs/Proofs/EulerPolyhedralOQ02OQ01.lean` — restructured `VectorFieldOnSurface`; added `namespace VectorFieldOnSurface` with derived `totalIndex`, `noZeros`, `nonvanishing_index`; threaded the unfolded sum into `hairy_ball` so `omega` closes.
- `src/data/proofs/euler-polyhedral-formula-oq-02-oq-01/meta.json` — `axiomCount: 10 → 9`, line/theorem/definition counts updated, `assumptions` string rewritten.
- `src/data/research/problems/euler-polyhedral-formula-oq-02-oq-01-wip-01.json` — phase → ACT, iteration → 3, focus + nextAction + knownResults + knowledge.* updated.
- `research/problems/euler-polyhedral-formula-oq-02-oq-01-wip-01/state.md` — phase OBSERVE/ORIENT → ACT; reduction-D landed summary.
- `research/problems/euler-polyhedral-formula-oq-02-oq-01-wip-01/knowledge.md` — S3 ACT section appended.
- `research/problems/euler-polyhedral-formula-oq-02-oq-01-wip-01/sessions/2026-06-10-s3-act-reduction-D.md` — this file (new).

## Knowledge added

- 1 substantial built item (restructured `VectorFieldOnSurface`).
- 2 insights logged in the problem JSON.
- 0 new mathlib gaps (Reduction D used only existing Mathlib lemma `Finset.sum_empty`).
- Cost-ordered next steps updated (S4: Reduction B; S5: Reduction C).
