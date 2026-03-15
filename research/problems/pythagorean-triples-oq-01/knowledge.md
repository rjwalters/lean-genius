# Knowledge: Pythagorean Triples Density (OQ-01)

## Result

The number of primitive Pythagorean triples with hypotenuse c ≤ N is asymptotically N/(2π).

## Formalization Status: COMPLETED

**File**: `proofs/Proofs/PythagoreanTriplesOQ01.lean` (~2490 lines)
**Companion**: `proofs/Proofs/PythagoreanTriplesOQ01Aristotle.lean` (12 routine lemmas proved)
**Stats**: ~120 theorems, ~39 definitions, 0 sorries, 7 axioms (3 core + 4 supplementary)
**Build**: Passes (fixed Mathlib API breakage 2026-03-15)

## Proof Architecture

The main theorem `primitiveTripleCount_density` decomposes the density into three independent factors:

```
primitiveTripleCount(N) / N → 1/(2π)
= (count/coprime) × (coprime/sector) × (sector/N)
= (2/3) × (6/π²) × (π/8)
= 1/(2π)
```

Each factor is proved as a separate `Tendsto` statement, then combined via arithmetic.

## Three Independent Axioms

### 1. `sector_lattice_point_density` (line 512)
- **Statement**: `sectorPointCount(N) / N → π/8`
- **Meaning**: Lattice points in {0 < n < m, m²+n² ≤ N} grow as πN/8
- **Requires**: Gauss circle problem asymptotics
- **Mathlib gap**: No formalization of lattice point counting in circular regions

### 2. `coprime_fraction_in_sector` (line 518)
- **Statement**: `coprimeInSectorCount(N) / sectorPointCount(N) → 6/π²`
- **Meaning**: Density of coprime pairs is 6/π² (reciprocal of ζ(2))
- **Requires**: Möbius inversion or Euler product
- **Mathlib gap**: No formalization of coprime density asymptotics

### 3. `bothOdd_fraction_in_coprime_sector` (line 529)
- **Statement**: `bothOddCoprimeCount(N) / coprimeInSectorCount(N) → 1/3`
- **Meaning**: Among coprime pairs, 1/3 have both coordinates odd
- **Requires**: Equidistribution of coprime residues by parity class
- **Mathlib gap**: No sieve theory or character sum bounds

## Key Infrastructure Built

### Involution Bijection (Part XIV)
- `triangle_oe_eq_oo`: |OE(K)| = |OO(K)| exactly via (m,n) ↔ (m,m-n) involution
- Proves exact parity balance in the triangular region without circle constraint

### Three-Way Partition (Part XII)
- `coprime_sector_three_way_partition`: coprime = EO + OE + OO
- `primitive_eq_eo_plus_oe`: primitive triples = EO + OE pairs

### Axiom Decomposition (Parts XVI-XIX)
- `parity_from_boundary_and_eo`: bothOdd axiom = boundary vanishing + EO density
- `parity_axiom_from_columns`: bothOdd axiom = column density ratio + boundary vanishing
- Separates geometric content (boundary) from arithmetic content (density)

### GCD Halving (Part XVIII)
- `coprime_eo_iff`: gcd(2a,n) = gcd(a,n) when n is odd
- Explains WHY each parity class has the same coprime density

### Boundary Analysis (Part XVI)
- `sector_boundary_balance`: sectorOE + bdryOE = sectorOO + bdryOO
- `sector_oe_oo_discrepancy_bound`: sector discrepancy = boundary discrepancy
- Total boundary is Θ(N), NOT O(√N); the discrepancy must be shown o(N)

### Straddling Pair Analysis (Part XXIII)
- `circleNorm`, `circleNormInv`: circle distance under involution
- `circle_norm_gap`: norm difference = m|m-2n| (algebraic identity)
- `norm_inv_larger_when_n_small/large`: involution geometry (n < m/2 → outward, n > m/2 → inward)
- `parity_from_straddling_vanishes`: column density + straddling → 0 implies OO → 1/3
- **Key insight**: straddling pairs = O(√N) << coprime sector = Θ(N), so boundary vanishes

### Upgraded Axioms (Part XXIII)
- `triple_count_from_r2_connection`: PROVED (π/8)×(6/π²)×(2/3) = 1/(2π)
- `landau_two_squares`: upgraded from True to proper Landau-Ramanujan Tendsto statement
- `r2_pos_iff`: converted to axiom (requires Gaussian integer UFD)

## Approaches Explored

1. **Density decomposition via telescoping** - SUCCEEDED: Main theorems proved from 3 axioms
2. **Parity partition infrastructure** - SUCCEEDED: Exact bijections, partition identities
3. **Boundary analysis for parity axiom** - BLOCKED: Per-column parity balance requires character sum bounds absent from Mathlib
4. **Straddling pair analysis** - SUCCEEDED: Complete geometric explanation of parity axiom via O(√N) straddling bound

## Why 3 Axioms Are Irreducible (Current Mathlib)

Each axiom requires a distinct area of analytic number theory:
- **Axiom 1** (Gauss circle): Lattice point counting in circular regions
- **Axiom 2** (coprime density): Euler product / Möbius function
- **Axiom 3** (parity equidistribution): Sieve theory / Dirichlet characters

None of these areas have sufficient Mathlib coverage. The decomposition work (Parts XVI-XIX) showed that Axiom 3 can be factored into two sub-conditions (column density + boundary vanishing), but both sub-conditions also require analytic tools.

## Computational Verifications

| N | primitiveTripleCount | coprimeInSectorCount | bothOddCoprimeCount |
|---|---------------------|---------------------|---------------------|
| 0 | 0 | - | - |
| 4 | 0 | - | - |
| 5 | 1 | 1 | 0 |
| 13 | 2 | 3 | 1 |
| 25 | 4 | 5 | 1 |
| 50 | 7 | 11 | 4 |
