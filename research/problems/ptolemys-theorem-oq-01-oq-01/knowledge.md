# Knowledge: ptolemys-theorem-oq-01-oq-01

## Key Facts

### Ptolemy's Theorem (Parent)
- For four points on a circle in CCW order $A, B, C, D$: $|AC| \cdot |BD| = |AB| \cdot |CD| + |AD| \cdot |BC|$
- Parent proof `ptolemys-theorem-oq-01` establishes: unit circle points in CCW order → equality. (0 sorries, verified)
- Complex number approach: uses $|z_a - z_c| \cdot |z_b - z_d| = |z_a - z_b| \cdot |z_c - z_d| + |z_a - z_d| \cdot |z_b - z_c|$ for CCW ordered unit circle points.

### The Converse Direction
- **Goal**: Ptolemy equality → CCW order (or CW order)
- Equivalently: if equality holds, points are in cyclic order on a common circle
- Key fact: Ptolemy equality is equivalent to the cross-ratio $(A,B;C,D)$ being real and positive

### Cross-Ratio Characterization
- The cross-ratio of four complex numbers $z_1, z_2, z_3, z_4$ is $(z_1 - z_3)(z_2 - z_4)/((z_1 - z_4)(z_2 - z_3))$
- Four points are concyclic or collinear ↔ cross-ratio is real
- Ptolemy equality ↔ cross-ratio is a positive real (for unit circle points)

### Ptolemy Inequality (Strict)
- For four points NOT in cyclic order on the circle: strict inequality holds
- This is the heart of the converse: equality forces cyclic order

## Open Questions
- Is `Complex.crossRatio` available in Mathlib?
- What's the Lean name for cross-ratio in complex analysis?
- Does the parent proof use any specific ordering lemmas for `Complex.arg`?

## References
- Parent proof: `proofs/Proofs/PtolemysTheoremOQ01.lean`
- `Mathlib.Analysis.SpecialFunctions.Complex.Circle` — circle in ℂ
- `Complex.abs` — complex distance
