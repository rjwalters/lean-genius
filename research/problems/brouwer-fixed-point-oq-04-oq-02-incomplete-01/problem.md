# Problem: Complete Nash Equilibrium Existence via Nash's Brouwer Argument

**Slug**: brouwer-fixed-point-oq-04-oq-02-incomplete-01
**Created**: 2026-04-22T12:00:00+02:00
**Status**: Active
**Source**: gallery-incomplete

## Problem Statement

### Formal Statement

The gallery proof `brouwer-fixed-point-oq-04-oq-02` proves Nash equilibrium existence
for finite N-player multilinear games but relies on one axiom:

```lean
axiom brouwer_product_simplex {N : ℕ} (G : MultilinearGame N)
    (f : MixedProfile N G → MixedProfile N G)
    (hf_maps : ∀ σ ∈ ProductSimplex G, f σ ∈ ProductSimplex G)
    (hf_cont : Continuous f) :
    ∃ σ ∈ ProductSimplex G, f σ = σ
```

The task is to **prove this axiom as a theorem**, eliminating the sole remaining
assumption and making the Nash existence proof fully axiom-free.

### Plain Language

The `ProductSimplex G` for an N-player game is the set of all mixed strategy
profiles: `∏ᵢ Δᵢ` where `Δᵢ` is the probability simplex over player i's finite
strategy set. This is a compact, convex subset of a finite-dimensional Euclidean space.

The axiom says that any continuous self-map of this set has a fixed point — which
is exactly Brouwer's Fixed Point Theorem applied to the product simplex.

### Proof Sketch (from parent proof comments)

> Full proof: embed ∏ᵢ Δᵢ into Fin(Σᵢ strategies i) → ℝ via concatenation,
> which gives a homeomorphism preserving compactness and convexity. Then apply
> Brouwer FPT. The embedding is routine topology but requires `Fin.appendEquiv`
> and `IsHomeomorph` machinery.

### Key Challenge

The `ProductSimplex G` is defined as a product of probability simplices over
`Fin (G.strategies i)` sets. These are compact convex subsets of finite-dimensional
normed spaces. The challenge is to:

1. Show `ProductSimplex G` is compact and convex in the ambient type
2. Connect to Mathlib's Brouwer FPT (which works on `EuclideanSpace` or
   finite-dimensional convex compact sets)
3. Handle the dependent type structure (`MixedProfile N G` and `ProductSimplex G`)

## Why This Matters

- **Removes last axiom**: Nash existence would become fully machine-verified
- **Landmark result**: Nash equilibrium existence (Nobel Prize 1994) fully formal
- **Mathlib bridge**: Tests Mathlib's Brouwer FPT machinery on product structures

## Key Definitions (from `BrouwerFixedPointOQ04OQ02.lean`)

```lean
-- Mixed strategy: probability distribution over finite strategies
-- MixedStrategy n = { p : Fin n → ℝ | (∀ k, 0 ≤ p k) ∧ ∑ k, p k = 1 }

-- Mixed profile: all players' mixed strategies
-- MixedProfile N G = (i : Fin N) → MixedStrategy (G.strategies i)

-- Product simplex: valid mixed strategy profiles
def ProductSimplex {N : ℕ} (G : MultilinearGame N) : Set (MixedProfile N G) :=
  { σ | ∀ i k, 0 ≤ σ i k } ∩ { σ | ∀ i, ∑ k, σ i k = 1 }
```

## Relevant Files

- **Parent proof**: `proofs/Proofs/BrouwerFixedPointOQ04OQ02.lean` (494 lines)
- **Parent gallery**: `src/data/proofs/brouwer-fixed-point-oq-04-oq-02/`
- **Base Brouwer**: `proofs/Proofs/BrouwerFixedPoint.lean` — Brouwer FPT base proof
- **Companion file**: Consider `BrouwerFixedPointOQ04OQ02Aristotle.lean`

## Mathlib Entry Points

- `Mathlib.Topology.Algebra.Module.FiniteDimension` — finite-dimensional topology
- `Mathlib.Analysis.Convex.Basic` — convex sets
- `Mathlib.Topology.Compactness.Compact` — compactness
- `Mathlib.Analysis.InnerProductSpace.PiL2` — product of normed spaces
- Look for: Brouwer FPT for compact convex sets in Mathlib (search `brouwer`)
