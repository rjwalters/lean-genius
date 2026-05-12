# ehrhart-cube-proven-oq-03: Knowledge Base

## Problem Summary

Add a NEW gallery entry on **Barvinok's polynomial-time lattice-point
counting algorithm** for rational polytopes in fixed dimension.  Sister
to the existing `ehrhart-cube-proven*` family (which addresses
identity-type Ehrhart questions), focusing instead on the
**generating-function / algorithmic** angle.

**Status (S1 OBSERVE)**: workspace + survey only; no Lean changes.

## Existing Gallery Inventory

Pulled from `find src/data/proofs -maxdepth 1 -type d -name 'ehrhart*'`.

| Directory                            | Status     | Lean file path                     | Focus                                              |
|--------------------------------------|------------|------------------------------------|----------------------------------------------------|
| `ehrhart-cube-proven`                | verified   | `Proofs/EhrhartCubeProven.lean`    | First-principles `(n+1)ᵈ`, 26 theorems, 0 axioms.  |
| `ehrhart-cube-proven-oq-01`          | varies     | (see meta.json — not surveyed S1)  | Sibling                                            |
| `ehrhart-cube-proven-oq-02`          | COMPLETED  | (see workspace `ehrhart-cube-proven-oq-02.json`) | "Ehrhart polynomials without general existence theorem" |
| `ehrhart-cube-proven-oq-04`          | PROVED     | `Proofs/EhrhartCubeProvenOQ04.lean` | Eulerian h*-vector + Worpitzky + palindrome.       |

**Gap**: no Barvinok-style algorithmic / generating-function entry.

## Mathlib v4.26.0 Survey (training knowledge — S2 to probe)

Pinned at `proofs/lakefile.toml` line 8: `rev = "v4.26.0"`.

### Confirmed available (used by `EhrhartCubeProven.lean`)

- `Fintype.card_fun` — `Mathlib.Data.Fintype.Basic`.
- `Finset.sum_geometric_two_add_one` and related — geometric series.
- `Mathlib.Combinatorics.Polytope.*` — exists.
- `Mathlib.Combinatorics.Polytope.Ehrhart` — exists (used by other
  ehrhart-cube-proven entries).

### Plausibly available (S2 to verify)

- `Polynomial.geom_series` — `(1 − x^{n+1}) / (1 − x)` identities.
- `MvPolynomial.aeval` — for multi-variable generating functions.
- `RatFunc` — rational functions over a field, including the
  field-of-fractions construction.
- `MvPowerSeries` — multivariate formal power series.
- `LinearProgramming` infrastructure? Likely sparse; Mathlib's
  polytope theory is mostly geometric, not algorithmic.

### Almost-certainly absent (the gap Barvinok fills)

- **Signed simplicial-cone decomposition** of an arbitrary rational
  cone (Barvinok's signed-decomposition algorithm).
- **Short rational generating function** form
  `f(P; x) = ∑ᵢ ε_i · x^{u_i} / ∏ⱼ (1 − x^{v_{i,j}})` with
  bounded `i`, `ε_i ∈ {±1}`.
- **Polynomial-time complexity** statements (Mathlib has no formal
  complexity class library; would have to be axiomatised).

## Proof Strategy (proposed for S2)

### Tier 1 (minimum viable gallery entry, S2)

`proofs/Proofs/EhrhartCubeProvenOQ03.lean` — 200–350 lines:

- Define a **short rational generating function**: a finite formal
  expression `∑ᵢ ε_i · x^{u_i} / ∏ⱼ (1 − x^{v_{i,j}})` with
  `ε_i ∈ {±1}`, `u_i, v_{i,j} ∈ ℤᵈ`.
- State **Brion's theorem**: for a rational polytope `P`,
  `f(P; x) = ∑ᵥ f(tangentCone v P; x)` where the sum is over vertices
  `v` of `P`.
- State **Barvinok's theorem** (the polytime algorithm) as an axiom
  with the polytime complexity claim itself axiomatised (since
  Mathlib has no formal complexity-class library).
- **Corollary**: short generating function for `[0, n]ᵈ` cube:
  `f([0,n]ᵈ; x) = ∏ᵢ (1 − xᵢⁿ⁺¹) / (1 − xᵢ)`.  This is a
  *first-principles* lemma that can be PROVED (not axiomatised) via
  Mathlib's geometric series + factorisation.

### Tier 2 (stretch, S3)

- Implement the 2-D Barvinok signed decomposition: every 2-D rational
  cone is a signed sum of unimodular cones, with the unimodular
  decomposition produced via continued-fraction-style descent.
  ~300–500 Lean lines.

### Tier 3 (long-term)

- Higher-dimensional signed decomposition (Barvinok's general
  algorithm).  Out of scope for any single PR; future OQ.

## Cross-Reference Plan

The new gallery entry should `import Proofs.EhrhartCubeProven` to
reuse the `(n+1)ᵈ` identity as a sanity check.  The relation:

```
(n+1)ᵈ      = #([0,n]ᵈ ∩ ℤᵈ)
            = lim_{x → 1} ∏ᵢ (1 - xᵢⁿ⁺¹) / (1 - xᵢ)
            = lim_{x → 1} f([0,n]ᵈ; x)
```

is the *bridge* lemma between OQ-03 and the parent.

## Recent Gallery Standards

- New gallery files use `theorem`/`lemma`/`axiom` mix; total `axiom`
  count goes in `meta.json -> axiomCount`.
- Sibling files (OQ-01/02/04) all live in `Proofs/EhrhartCubeProven*.lean`;
  OQ-03 should follow the same naming.
- Status mapping: `verified` if 0 axioms 0 sorries; `axiomatized` if
  ≥1 axiom; `formalized` if ≥1 sorry.

## Mathlib API Probes (deferred to S2)

S2.1 — Probe file `Proofs/EhrhartCubeProvenOQ03Probe.lean`:

```lean
import Mathlib.Combinatorics.Polytope.Ehrhart
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic

-- Confirm presence of these (best-guess names):
#check @MvPolynomial
#check @RatFunc
#check @MvPowerSeries
#check @Polynomial.geom_series_def
```

If `Polynomial.geom_series_def` exists, the corollary
`f([0,n]ᵈ; x) = ∏ᵢ (1 − xᵢⁿ⁺¹) / (1 − xᵢ)` reduces to a single-line
proof per dimension + `Finset.prod_pi_apply` or analogous.

## Next Action

Land S1 OBSERVE doc-only PR (this commit), then claim S2 ACT to
implement Tier 1.

## References

- Barvinok 1994 (canonical algorithm paper).
- Beck & Robins (2015) ch. 11.
- Mathlib4 `Mathlib.Combinatorics.Polytope.Ehrhart`.
- Lean Genius `Proofs/EhrhartCubeProven.lean` (verified parent).
