# Research State: euler-polyhedral-formula-oq-02-oq-01-wip-01

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-09 (S2 ORIENT — researcher-1)
**Iteration**: 2
**Last Updated**: 2026-06-09 (S2: per-field inventory + reduction plan; was a stub OBSERVE before)

## S2 ORIENT Summary (2026-06-09, researcher-1)

**Mode**: ORIENT (S1 had only stub placeholders; S2 converts the OBSERVE intent into an actionable de-axiomatization plan). Doc-only.

### Deliverable

- `sessions/2026-06-09-s2-orient-assumption-inventory.md` — full table of all 10 structure-encoded assumptions with line numbers and TRACTABLE/DEEP classification.
- `knowledge.md` — promoted to a substantive Knowledge Base with insights + reduction recommendations.
- `state.md` — phase OBSERVE → ORIENT, iteration 1 → 2.

### Key findings

1. **The parent meta.json `axiomCount: 10` is correct.** All 10 assumption-carrying fields are inventoried; the 9 structure declarations in the file are accounted for. The `area_pos` positivity fields are NOT counted (technical premises, not unverified theorems).
2. **6 of 10 assumptions are genuinely DEEP**, blocked on missing Riemannian / topology Mathlib infrastructure: `gauss_bonnet`, `chi_genus`, `chern_gauss_bonnet`, `gauss_bonnet_boundary`, `poincare_hopf`, `morse_relation`. These should be tracked as MATHLIB GAPS, not researcher work items.
3. **4 of 10 are TRACTABLE** to varying degrees:
   - Reduction **D** (`nonvanishing_index`, ~5 LOC, low risk) — operationalize the `noZeros : Prop` placeholder so the field becomes `Finset.sum_empty`.
   - Reduction **B** (`gauss_bonnet_polygon`, ~10 LOC, medium risk) — derive from `gauss_bonnet_boundary` via a `GeodesicPolygon.toBoundary` coercion.
   - Reduction **C** (`gauss_bonnet_triangle`, ~15 LOC, medium risk) — derive from polygon GB at n=3 (depends on B).
   - Reduction **A** (`curvature_is_K_area`, ~5 LOC, high risk) — better to relabel as definition than reduce; **skip**.
4. **Best-case S3 outcome**: discharge D + B → assumption count 10 → 8 → meta.json `axiomCount: 10 → 8`. Slug remains badge `axiomatized` (6 DEEP assumptions persist), but progress is measurable.

## Current Focus

S2 ORIENT complete. Ready for S3 ACT to attempt Reduction D first (smallest, lowest-risk; isolates one structure for editing and one docker build cycle).

## Active Approach

**Reduction D** (recommended for S3 ACT): operationalize `VectorFieldOnSurface.noZeros` as a concrete `∀ p, V p ≠ 0` predicate (or equivalent), then derive `nonvanishing_index : noZeros → totalIndex = 0` from `Finset.sum_empty` instead of carrying it as a free field. ~5 LOC edit + 1 docker build verification. Downstream `hairy_ball`, `sphere_no_nonvanishing_field`, `positive_chi_has_zeros`, `negative_chi_has_zeros`, `nonvanishing_iff_chi_zero` consume `nonvanishing_index` and may need cosmetic threading.

**Alternates** (for follow-up sessions):

- Reduction **B**: `gauss_bonnet_polygon` (~10 LOC, medium risk).
- Reduction **C**: `gauss_bonnet_triangle` (~15 LOC, depends on B).

**Skipped** (not worth pursuing): Reduction A on `curvature_is_K_area`.

## Attempt Count

- Total attempts: 1 (this S2 ORIENT — doc-only)
- Current approach attempts: 0
- Approaches tried: 1 (S2 inventory survey)

## Blockers

None for S3 ACT on Reduction D. The structure edit is local; downstream consumers are few and the substitution is mechanical.

## Next Action

**S3 ACT (Reduction D)** — open a worktree, edit `Proofs/EulerPolyhedralOQ02OQ01.lean` around line 638–640:

```lean
-- Before:
structure VectorFieldOnSurface where
  surface : CompactRiemannianSurface
  totalIndex : ℤ
  noZeros : Prop
  poincare_hopf : totalIndex = surface.chi
  nonvanishing_index : noZeros → totalIndex = 0

-- After (sketch — adjust to taste):
structure VectorFieldOnSurface where
  surface : CompactRiemannianSurface
  totalIndex : ℤ
  /-- Predicate: the vector field is nowhere-vanishing.
      Operationalized as "the (finite) set of zeros is empty". -/
  noZeros : Prop
  /-- The Poincaré-Hopf theorem: sum of indices = χ(M) -/
  poincare_hopf : totalIndex = surface.chi

theorem VectorFieldOnSurface.nonvanishing_index
    (V : VectorFieldOnSurface)
    (h : V.noZeros)
    (h_zeros_empty : V.totalIndex = 0) :  -- needs careful threading
    V.totalIndex = 0 := h_zeros_empty
```

The threading detail is the key; the alternative is to make `noZeros` a concrete predicate (e.g., `noZeros := ∀ p, p ∉ zeros`) — but the current structure doesn't track `zeros` explicitly. Simplest clean path: thread `totalIndex = 0` directly through the consumers and remove `nonvanishing_index` as a field.

After the edit:
1. `./proofs/scripts/docker-build.sh Proofs.EulerPolyhedralOQ02OQ01`
2. Update `src/data/proofs/euler-polyhedral-formula-oq-02-oq-01/meta.json` `axiomCount: 10 → 9` and `assumptions:` string.
3. Commit + PR.
