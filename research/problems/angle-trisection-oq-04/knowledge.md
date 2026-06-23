# Angle Trisection OQ-04: Constructions with Additional Tools

## Problem
Are there natural generalizations to constructions with additional tools
(e.g., compass-only, straightedge-only, marked ruler, origami)?

## Status: COMPLETED (0 sorries, 0 axioms)

## Key Results

### The Five-Level Tool Hierarchy
```
straightedge-only ⊊ straightedge+circle = compass-only = compass+straightedge ⊊ marked ruler ⊆ origami
```

Each level is characterized algebraically by the degrees of minimal polynomials
of constructible numbers:

| Tool | Constructible Degrees | Algebraic Condition |
|------|----------------------|-------------------|
| Straightedge only | {1} | Rational points only |
| Straightedge + circle | {d : d \| 2^n} | Poncelet-Steiner (1833) |
| Compass only | {d : d \| 2^n} | Mohr-Mascheroni (1672/1797) |
| Compass + straightedge | {d : d \| 2^n} | Wantzel (1837) |
| Marked ruler (neusis) | {d : d \| 2^a·3^b} | Gleason (1988) |
| Origami | ⊇ {d : d \| 2^a·3^b} | Huzita-Justin axioms |

### Classical Impossibilities Resolved by Neusis
- cos(20°) has degree 3 = 2^0·3^1: neusis-constructible, compass-impossible
- ∛2 has degree 3 = 2^0·3^1: neusis-constructible, compass-impossible

### Regular Polygon Classification
- 7-gon: NOT compass (7 not Fermat), IS neusis (7 is Pierpont: 2^1·3^1+1)
- 9-gon: NOT compass (9 not power of 2), IS neusis (9 = 3^2)
- 11-gon: NOT neusis either (11 is not Pierpont prime, not 2-3 number)

### Pierpont Primes Verified
2, 3, 5, 7, 13, 17, 19, 37

## Proof File
`proofs/Proofs/AngleTrisectionOQ04.lean`

## Session Notes
- Extended existing proof (which had Parts 1-11) with Parts 12-14
- Part 12: Poncelet-Steiner theorem and straightedge hierarchy
- Part 13: Extended tool hierarchy (5 levels)
- Part 14: Regular polygon neusis-constructibility classification
- All additions proved without axioms or sorries

## Approaches Explored

### Algebraic degree characterization
**Status**: succeeded
Model each tool via the set of degrees of minimal polynomials it can construct. Prove containment/equality/strict-containment between these degree sets.
