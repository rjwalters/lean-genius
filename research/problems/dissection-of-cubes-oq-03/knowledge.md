# Dissection of Cubes OQ-03: Connections to Packing Problems

## Problem
What are the connections between the impossibility of dissecting a cube
into cubes of all different sizes (Wiedijk #82) and packing problems?

## Status: COMPLETED (0 sorries, 3 axioms)

## Key Results

### The Dissection-Packing Bridge
- Every dissection is a packing (CubeDissection.toPacking)
- A packing relaxes the coverage requirement (no gaps allowed in dissection)
- **Main theorem**: No packing of cubes of all distinct sizes can achieve
  volume fraction 1 — the dissection impossibility forces gaps

### Volume Bounds
- Packing: total volume ≤ 1 (axiom, needs measure theory)
- Dissection: total volume = 1 (axiom, no gaps)
- Distinct-size packing: total volume < 1 (proved from bridge)

### de Bruijn's Theorem (1969)
- A box can be tiled by copies of a brick iff divisibility condition holds
- Provides algebraic criterion for brick tilings (contrasts with distinct-size case)
- Axiomatized (proof needs harmonic analysis)

### Dimension Contrast
| Dim | Perfect distinct-size dissection? | Packing density |
|-----|----------------------------------|-----------------|
| 1D  | NO                               | < 1             |
| 2D  | YES (squared squares)            | = 1 possible    |
| 3D  | NO (Wiedijk #82)                 | < 1             |
| n≥3 | NO (same argument)               | < 1             |

## Proof File
`proofs/Proofs/DissectionOfCubesOQ03.lean`

## Axioms Used
1. `packing_volume_bound` — total packing volume ≤ 1 (needs measure theory)
2. `dissection_volume_exact` — dissection volume = 1 (needs measure theory)
3. `debruijn_brick_tiling` — de Bruijn's algebraic tiling criterion

## Approaches Explored

### Packing-dissection bridge
**Status**: succeeded
Define packing as relaxation of dissection, prove that dissection impossibility implies packing density < 1 for distinct sizes.
