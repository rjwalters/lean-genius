# Problem: Erdős #224: Obtuse Angles in Point Sets — Define `hypercubeVertices`

**Slug**: erdos-224-incomplete-01
**Created**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

**Lean file**: `proofs/Proofs/Erdos224Problem.lean`

The sorry is in the definition `hypercubeVertices`:
```lean
def hypercubeVertices (d : ℕ) : Finset (EuclideanPoint d) :=
  sorry  -- The set {0,1}^d
```

This is a **definition sorry** — need to construct the Finset `{0,1}^d` in `EuclideanPoint d = Fin d → ℝ`.

## Key Approach

The hypercube `{0,1}^d` can be constructed as:
```lean
def hypercubeVertices (d : ℕ) : Finset (EuclideanPoint d) :=
  Finset.univ.image (fun (b : Fin d → Fin 2) => fun i => (b i : ℝ))
```

Or using `Fintype.piFinset` or `Finset.pi`.

**Alternative**: Model as `Fin d → Bool` and cast to `ℝ`.

## Mathlib Tools
- `Finset.pi`: Cartesian product of finsets
- `Matrix.of`: for constructing matrices/vectors
- `EuclideanSpace ℝ (Fin d)` is `Fin d → ℝ`

## Note: Definition Sorry
Aristotle cannot prove this. Researcher must write the definition.

## Tractability: MEDIUM
