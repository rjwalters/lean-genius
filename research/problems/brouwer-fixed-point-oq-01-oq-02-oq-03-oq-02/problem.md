# Problem: Eliminating `singular_homology_retraction_split` from BrouwerFixedPointOQ01OQ02

Slug: `brouwer-fixed-point-oq-01-oq-02-oq-03-oq-02`
Parent: `brouwer-fixed-point-oq-01-oq-02-oq-03`
Tier: B · Significance 6/10 · Tractability 5/10

## Background

`proofs/Proofs/BrouwerFixedPointOQ01OQ02.lean` proves the no-retraction theorem
(no continuous `r : B^n → S^{n-1}` retracting the closed ball to its boundary)
via **singular homology**, replacing the opaque `no_retraction_axiom` of
`BrouwerFixedPoint.lean` with a more informative axiom:

```lean
axiom singular_homology_retraction_split (n : ℕ) (hn : n ≥ 1)
    (r : Retraction n) :
    ∃ (φ : ℤ →+ Unit) (ψ : Unit →+ ℤ), ψ.comp φ = AddMonoidHom.id ℤ
```

This packages three classical singular-homology facts into one statement:

1. **Sphere homology**: `H_{n-1}(S^{n-1}) ≅ ℤ` for `n ≥ 1`.
2. **Ball homology**: `H_{n-1}(B^n) = 0` (B^n is contractible).
3. **Functoriality of singular homology**: the retraction identity
   `r ∘ ι = id` induces `r_* ∘ ι_* = id` on `H_{n-1}`, producing the
   split `ψ ∘ φ = id : ℤ →+ Unit →+ ℤ`.

The pure-algebra contradiction (`id : ℤ →+ ℤ` cannot factor through `Unit`)
is already proved in Part II of `BrouwerFixedPointOQ01OQ02.lean` (0 sorries).

## Open Question

**Eliminate `singular_homology_retraction_split` as a Lean axiom**, replacing it
with a theorem whose proof discharges to Mathlib lemmas. The result should
reduce the gallery's axiom count for the singular-homology-based Brouwer chain.

## Required Mathlib Infrastructure

Step | Statement | Mathlib status @ v4.26.0
-----|-----------|--------------------------
S0   | Singular chain complex / singular homology functors on `TopCat` | **Present** — `Mathlib.AlgebraicTopology.SingularHomology.Basic`
S1   | Chain-homotopy invariance of homology | **Present** — `Homotopy.homologyMap_eq` in `Mathlib.Algebra.Homology.Homotopy`
S2   | Topological homotopy → chain homotopy (prism operator) | **Missing**
S3   | `H_n(point) = 0` for `n ≥ 1` (special case of totally-disconnected) | Present (specialization)
S4   | `Convex.contractibleSpace` (closed ball is contractible) | **Present** — `Mathlib.Analysis.Convex.Contractible`
S5   | `H_n(B^n) = 0` via S2 + S4 + S3 | Derivable once S2 exists
S6   | A nonzero class in `H_{n-1}(S^{n-1})` for `n ≥ 1` | **Missing**

## Why This Matters

1. **Real axiom elimination.** Removing this axiom converts a "homologically-flavoured"
   placeholder into actual Mathlib-checked homology. It substantively strengthens
   one of the marquee gallery formalizations (Brouwer via singular homology).
2. **Stepping stone to Mathlib contribution.** S2 (prism operator for singular
   homology) is a self-contained, well-known construction that would be a useful
   contribution to `Mathlib.AlgebraicTopology.SingularHomology`.
3. **Sharpens the gap picture.** Replacing the all-in-one axiom with three
   smaller, classically-known facts makes the remaining honest dependency on
   unproved infrastructure transparent.

## Related Gallery Proofs

| Slug | File | Relation |
|------|------|----------|
| `brouwer-fixed-point` | `BrouwerFixedPoint.lean` | Uses `no_retraction_axiom` (opaque) |
| `brouwer-fixed-point-oq-01-oq-02` | `BrouwerFixedPointOQ01OQ02.lean` | **Declares this axiom** |
| `brouwer-fixed-point-oq-01-oq-02-oq-03` | `BrouwerFixedPointOQ01OQ02OQ03.lean` | Derives BFP from the axiom |
| `brouwer-fixed-point-oq-01-oq-02-oq-03-oq-01` | `BrouwerFixedPointOQ01OQ02OQ03OQ01.lean` | Proves `retraction_construction` (geometric ray) |
