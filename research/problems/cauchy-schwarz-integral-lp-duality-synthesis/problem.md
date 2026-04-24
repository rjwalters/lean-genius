# Problem: Synthesis — Eliminate `riesz_lp_surjective` Axiom for Full Lp Duality

**Slug**: cauchy-schwarz-integral-lp-duality-synthesis
**Created**: 2026-04-24T09:53:59+02:00
**Status**: Active
**Source**: lean-synthesis agent (2026-04-23)
**Type**: synthesis / axiom-elimination

## Problem Statement

### Formal Statement

The axiom in `CauchySchwarzIntegralOQ01OQ01OQ02.lean`:
```lean
axiom riesz_lp_surjective (p : ℝ) (hp : 1 ≤ p) (μ : Measure ℝ) :
  Function.Surjective (riesz_lp_map p μ)
```
has been independently proved as `riesz_lp_surjective_from_rn` in
`CauchySchwarzIntegralOQ01OQ01OQ02OQ01.lean` (0 sorries, 0 axioms).

**Goal**: Replace the axiom with the theorem, upgrading the parent proof from
`axiomatized` to `verified` (0 axioms).

### Plain Language

A companion proof file already proved exactly the statement that the parent proof
was treating as an axiom. This synthesis task wires them together: import the
companion file, replace `axiom riesz_lp_surjective` with a theorem delegating to
the proved version, build, and update gallery metadata.

### Why This Matters

This completes the full Lp duality chain with zero axioms:
```
Young → Hölder (eLpNorm form)
     → isometric embedding Lq ↪ (Lp)*
     → surjectivity via Radon-Nikodým
     → Full (Lp)* ≅ Lq  [fully verified, 0 axioms]
```

## Known Results

### What's Already Proven

- `riesz_lp_surjective_from_rn` in `CauchySchwarzIntegralOQ01OQ01OQ02OQ01.lean`
  — proves surjectivity of the Riesz Lp map (0 sorries, 0 axioms)
- Full Lp isometric embedding in `CauchySchwarzIntegralOQ01OQ01OQ02.lean`

### What's Still Open

- The axiom `riesz_lp_surjective` in the parent file must still be replaced

### Our Goal

1. Wire the proved lemma into the parent proof
2. Build with 0 axioms, 0 sorries
3. Update `src/data/proofs/cauchy-schwarz-integral-oq-01-oq-01-oq-02/meta.json`:
   - `axiomCount`: 1 → 0
   - `status`: `"axiomatized"` → `"verified"`
   - `badge`: `"axiom"` → `"original"`

## Concrete First Steps

1. Open `proofs/Proofs/CauchySchwarzIntegralOQ01OQ01OQ02.lean`
2. Add import: `import Proofs.CauchySchwarzIntegralOQ01OQ01OQ02OQ01`
3. Replace the axiom with: `theorem riesz_lp_surjective := riesz_lp_surjective_from_rn`
4. Build: `./proofs/scripts/docker-build.sh Proofs.CauchySchwarzIntegralOQ01OQ01OQ02`
5. Update meta.json (axiomCount 1→0, status axiomatized→verified, badge axiom→original)

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `cauchy-schwarz-integral-oq-01-oq-01-oq-02` | Parent proof (has axiom to replace) | Riesz representation, Lp spaces |
| `cauchy-schwarz-integral-oq-01-oq-01-oq-02-oq-01` | Child proof (has theorem) | Radon-Nikodým, surjectivity |
| `cauchy-schwarz-integral` | Root Cauchy-Schwarz formalization | Integral Cauchy-Schwarz |

## Tractability Assessment

**Difficulty**: Very Low (synthesis / wire-up task)

**Justification**:
- Both proof files already exist and build successfully
- Task is purely structural: add an import, replace one declaration
- No new mathematics required
- Build validates correctness automatically

**Estimated Effort**:
- Exploration: 15 minutes (read both Lean files to confirm interface match)
- Implementation: 30–60 minutes (import + replace + build + meta update)

## Metadata

```yaml
tags:
  - synthesis
  - functional-analysis
  - lp-spaces
  - axiom-elimination
  - riesz-representation
related_proofs:
  - cauchy-schwarz-integral-oq-01-oq-01-oq-02
  - cauchy-schwarz-integral-oq-01-oq-01-oq-02-oq-01
difficulty: very-low
tractability: 9
significance: 8
tier: A
source: lean-synthesis
created: 2026-04-24T09:53:59+02:00
```
