# Problem: Prove borsuk_ulam_general from degree theory in Mathlib

**Slug**: borsuk-ulam-oq-03-oq-05
**Created**: 2026-05-03T04:43:18+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The axiom in `BorsukUlamOQ03.lean` (line 295):

```lean
axiom borsuk_ulam_general (n : ℕ) (hn : 1 ≤ n)
    (f : (Fin (n+1) → ℝ) → (Fin n → ℝ))
    (hf : Continuous f) :
    ∃ x : NSphere n, f x.1 = f (fun i => -x.1 i)
```

**Goal**: Replace this `axiom` declaration with a `theorem` proved using
`Mathlib.Topology.BorsukUlam` or homology-based machinery.

$$
\forall n \geq 1,\ \forall f : S^n \to \mathbb{R}^n \text{ continuous},\
\exists x \in S^n,\ f(x) = f(-x)
$$

### Plain Language

Any continuous map from the n-sphere to n-dimensional Euclidean space must
map some antipodal pair of points to the same value. Equivalently, no
continuous map S^n → ℝ^n is "antipodally injective."

### Why This Matters

`borsuk_ulam_general` is the **core axiom** of the entire `borsuk-ulam-oq-03`
chain (~3600 lines). Proving it from Mathlib would:
1. Reduce the axiom count from 3 to 2 (or possibly 0) for BorsukUlamOQ03
2. Establish a canonical bridge between `NSphere n` and Mathlib's sphere types
3. Demonstrate that Mathlib's algebraic topology library is production-ready
   for this level of application

## Known Results

### What's Already Proven

- `Mathlib.Topology.BorsukUlam` — Mathlib ships the Borsuk-Ulam theorem;
  exact generality (n=1 only vs all n) must be verified against current version
- `NSphere` type is defined in `BorsukUlam.lean` (the root gallery file) as a
  subset of `Fin (n+1) → ℝ` with unit L2 norm
- `BorsukUlamOQ03OQ01.lean` proves Tucker's Lemma as a combinatorial
  alternative; this does not eliminate the n-dimensional axiom

### What's Still Open

- Whether Mathlib's BorsukUlam covers arbitrary n or only n=2 (S¹ → ℝ)
- Whether `NSphere n` can be identified with `Metric.sphere 0 1` in the
  Mathlib sense with a compatible norm
- Whether the n-dimensional proof requires `Mathlib.AlgebraicTopology` homology
  or can use simpler degree-theory tools

### Our Goal

Replace `axiom borsuk_ulam_general` with a `theorem` in a companion file
`BorsukUlamOQ03OQ05.lean` that imports the parent and derives the axiom from
Mathlib. If the type bridge is non-trivial, establish intermediate coercion
lemmas as part of the contribution.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| borsuk-ulam-oq-03 | Parent — uses the axiom throughout | Degree theory axioms |
| borsuk-ulam-oq-03-oq-01 | Tucker's Lemma (combinatorial BU) | Discrete IVT |
| borsuk-ulam-oq-03-oq-02 | Brouwer degree formalization (sibling) | Homology |
| borsuk-ulam | Root entry with NSphere type definition | Type infrastructure |

## Initial Thoughts

### Potential Approaches

1. **Direct Mathlib bridge**: Import `Mathlib.Topology.BorsukUlam` and apply
   the main theorem, coercing `NSphere n` ↔ `Metric.sphere 0 1 (E := Fin (n+1) → ℝ)`.
   - Why it might work: Mathlib proof handles the hard part; only glue needed
   - Risk: Type universe mismatch or Mathlib only covers n=1 (S¹)

2. **Degree-theory reconstruction**: Use `Mathlib.Topology.Algebra.Module.Basic`
   and the Brouwer fixed-point theorem to derive BU via no-retraction.
   - Why it might work: No-retraction → BFP → BU is classical; oq-03 already
     has `no_retraction` results; could close the loop
   - Risk: Mathlib's no-retraction machinery may not yet exist in full generality

3. **Via `BorsukUlamOQ03OQ02`**: If oq-03-oq-02 (Brouwer degree) completes
   its proof, import it and derive `borsuk_ulam_general` from degree-theoretic
   machinery there.
   - Why it might work: avoids dependency on Mathlib internals
   - Risk: oq-03-oq-02 is also axiomatized; circular

### Key Difficulties

- `NSphere n` in the gallery is `{x : Fin (n+1) → ℝ // ‖x‖ = 1}` using the
  sup norm or L2 norm — must verify which and whether it matches Mathlib's sphere
- Mathlib's BorsukUlam may be formulated for `EuclideanSpace ℝ (Fin n)` rather
  than `Fin n → ℝ`
- The `hn : 1 ≤ n` hypothesis needs careful handling for inductive arguments

### What Would a Proof Need?

- Key lemma 1: `NSphere n ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n+1))) 1`
- Key lemma 2: Continuous equiv between `Fin n → ℝ` and `EuclideanSpace ℝ (Fin n)`
- Technical: Identify which Mathlib BU theorem to use and its exact hypotheses

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Mathlib ships `Mathlib.Topology.BorsukUlam` (confirmed present as of 2024)
- The hard mathematics is done; this is primarily type-theoretic glue
- Similar NSphere ↔ Mathlib sphere bridges have been done in the BU chain before
- Risk is Mathlib only proves the n=2 case (S¹ → ℝ); if so, full proof requires homology

**Estimated Effort**:
- Exploration: 1-2 sessions (verify Mathlib coverage)
- If tractable: 1-3 sessions (write coercion + proof)
- If hard: escalate to separate homology-based oq

## References

### Mathlib
- `Mathlib.Topology.BorsukUlam` — main theorem; verify generality
- `Mathlib.Analysis.InnerProductSpace.PiL2` — EuclideanSpace for Fin n
- `Mathlib.Topology.MetricSpace.Basic` — Metric.sphere

## Metadata

```yaml
tags:
  - topology
  - algebraic-topology
  - borsuk-ulam
  - axiom-elimination
  - mathlib-bridge
related_proofs:
  - borsuk-ulam-oq-03
  - borsuk-ulam-oq-03-oq-01
  - borsuk-ulam-oq-03-oq-02
  - borsuk-ulam
difficulty: medium
source: gallery-gap
created: 2026-05-03T04:43:18+02:00
```
