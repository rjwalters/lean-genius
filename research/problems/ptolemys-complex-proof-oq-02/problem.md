# Problem: Ptolemy Theorem — Sine Addition Formula via Chord Tables

**Slug**: ptolemys-complex-proof-oq-02
**Created**: 2026-04-22
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Can the historical derivation of the sine addition formula from Ptolemy's theorem be
formalized in Lean 4? Specifically:

$$\sin(\alpha + \beta) = \sin \alpha \cos \beta + \cos \alpha \sin \beta$$

can be derived by applying Ptolemy's theorem to a specific cyclic quadrilateral inscribed
in a unit circle, where the four vertices are chosen so that the theorem's terms reduce to
sine and cosine values.

### Plain Language

Ptolemy originally used his theorem to build chord tables (ancient analogs of sine tables).
The key historical derivation: inscribe a quadrilateral ABCD in a unit circle where the
arcs AB, BC, CD correspond to angles β, α-β, and 90°-α. Then Ptolemy's equality

$$AC \cdot BD = AB \cdot CD + AD \cdot BC$$

becomes the sine addition formula `sin(α+β) = sin(α)cos(β) + cos(α)sin(β)`.

Can we formalize this derivation — showing explicitly how Ptolemy's theorem implies the
sine addition formula?

### Why This Matters

- **Historical completeness**: This would close the circle between Ptolemy's original
  motivation and modern trigonometry, making the historical connection machine-verified.
- **Proof technique**: Demonstrates how classical geometric theorems generate algebraic
  identities — a recurring theme in formal mathematics.
- **Mathlib integration**: The sine addition formula is in Mathlib; a geometric proof
  would provide an independent verification pathway.

## Known Results

### What's Already Proven

- `ptolemys-complex-proof`: Ptolemy's inequality in ℂ via cross-ratio (verified, 0 sorries)
- `ptolemys-theorem-oq-01`: Ptolemy with concyclicity characterization (verified, 0 sorries)
- `Real.sin_add`: sine addition formula is in Mathlib (proof: algebra)
- Ptolemy equality holds for concyclic points (from `ptolemys-theorem-oq-01`)

### What's Still Open

- Formal derivation of `sin(α+β)` from Ptolemy's geometric theorem
- Connecting chord lengths on the unit circle to sine/cosine values
- The specific cyclic quadrilateral construction in Lean

### Our Goal

Prove `sin(α+β) = sin(α)cos(β) + cos(α)sin(β)` via Ptolemy's theorem by:
1. Constructing the relevant cyclic quadrilateral on the unit circle
2. Computing the four side lengths and diagonals as sine/cosine values
3. Applying Ptolemy's equality from the gallery proof

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| ptolemys-complex-proof | Primary: Ptolemy inequality in ℂ | Complex cross-ratio |
| ptolemys-theorem-oq-01 | Equality case (concyclicity) | Concyclicity characterization |
| ptolemys-complex-proof-oq-01 | SameRay connection | Ray geometry |

## Initial Thoughts

### Potential Approaches

1. **Direct construction**: Define the four points as `exp(i*θ)` for specific angles,
   compute distances explicitly as `|exp(i*α) - exp(i*β)| = 2*sin((α-β)/2)` (chord length),
   and apply Ptolemy's equality.
   - Why it might work: Very direct, all computations are explicit
   - Risk: Requires connecting `|z - w|` to sin/cos, which involves some trig manipulation

2. **Abstract approach via dot products**: Use the unit circle structure, express chord
   lengths via inner products `⟨u, v⟩ = cos(angle)`, and derive the formula.
   - Why it might work: May reuse existing Mathlib trig lemmas
   - Risk: More abstract, may need more Mathlib infrastructure

### Key Difficulties

- The equality case of Ptolemy requires the four points to be concyclic in correct order
- Computing `|exp(i*α) - exp(i*β)|` = `2*|sin((α-β)/2)|` requires careful manipulation
- The angle ordering (ensuring the quadrilateral is convex/non-self-intersecting)

### What Would a Proof Need?

- Chord length formula: `‖Complex.exp (I*α) - Complex.exp (I*β)‖ = 2*|sin((α-β)/2)|`
- Ptolemy equality applied to four points on unit circle
- Algebraic simplification showing the resulting equation is `sin(α+β) = ...`

## Tractability Assessment

**Difficulty**: Medium (Challenging but concrete)

**Justification**:
- The mathematical argument is completely clear
- All ingredients are available (Ptolemy proof, complex exponential, trig identities)
- Main challenge is connecting the geometric Ptolemy equality to trig identities

**Estimated Effort**:
- Exploration: 1-2 days (find the right Mathlib lemmas for chord length)
- If tractable: 3-5 days (the proof is straightforward once setup is in place)

## References

### Papers
- Ptolemy, *Almagest* — original chord table construction
- Toomer, G.J., *Ptolemy's Almagest* (translation, 1984)

### Mathlib
- `Complex.exp_mul_I` — `exp(i*θ) = cos(θ) + i*sin(θ)`
- `Real.sin_add` — sine addition formula (goal to re-derive geometrically)
- `Complex.abs_exp_ofReal_mul_I` — `|exp(i*θ)| = 1`
- Ptolemy equality from `ptolemys-theorem-oq-01` in gallery

## Metadata

```yaml
tags:
  - geometry
  - trigonometry
  - ptolemy
  - complex-analysis
  - historical
  - sine-addition-formula
related_proofs:
  - ptolemys-complex-proof
  - ptolemys-theorem-oq-01
difficulty: challenging
source: gallery-gap
created: 2026-04-22
```

**Significance**: 7/10
**Tractability**: 6/10
