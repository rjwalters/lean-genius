# Annotation TODO List

This document tracks proofs that need annotations added. Annotations explain the mathematical concepts, proof techniques, and key insights for each proof.

**Total: 73 proofs need annotations**

---

## Priority 1: Wiedijk's 100 Famous Theorems (Top 20)

These are among the most famous theorems in mathematics. High visibility, high impact.

| # | Proof | Wiedijk # | Status |
|---|-------|-----------|--------|
| [x] | [prime-number-theorem](src/data/proofs/prime-number-theorem) | #5 | axiom-based |
| [x] | [area-of-circle](src/data/proofs/area-of-circle) | #9 | mathlib |
| [x] | [euler-totient](src/data/proofs/euler-totient) | #10 | mathlib |
| [x] | [parallel-postulate-independence](src/data/proofs/parallel-postulate-independence) | #12 | axiom-based |
| [x] | [euler-polyhedral-formula](src/data/proofs/euler-polyhedral-formula) | #13 | pedagogical |
| [x] | [de-moivre](src/data/proofs/de-moivre) | #17 | mathlib |
| [x] | [liouville-theorem](src/data/proofs/liouville-theorem) | #18 | mathlib |

---

## Priority 2: Hilbert's 23 Problems

These define the major open problems of 20th century mathematics.

| # | Proof | Hilbert # | Status |
|---|-------|-----------|--------|
| [x] | [hilbert-3](src/data/proofs/hilbert-3) | #3 Scissors Congruence | original |
| [x] | [hilbert-4](src/data/proofs/hilbert-4) | #4 Shortest Distance | original |
| [x] | [hilbert-5](src/data/proofs/hilbert-5) | #5 Lie Groups | original |
| [x] | [gelfond-schneider](src/data/proofs/gelfond-schneider) | #7 | original |
| [x] | [hilbert-11](src/data/proofs/hilbert-11) | #11 Quadratic Forms | original |
| [x] | [kroneckers-jugendtraum](src/data/proofs/kroneckers-jugendtraum) | #12 | original |
| [x] | [hilbert-13](src/data/proofs/hilbert-13) | #13 Superposition | original |
| [x] | [hilbert-15](src/data/proofs/hilbert-15) | #15 Schubert Calculus | original |
| [x] | [hilbert-16](src/data/proofs/hilbert-16) | #16 Limit Cycles | original |
| [x] | [hilbert-17](src/data/proofs/hilbert-17) | #17 Sum of Squares | original |
| [x] | [kepler-conjecture](src/data/proofs/kepler-conjecture) | #18 Sphere Packing | original |
| [x] | [hilbert-21](src/data/proofs/hilbert-21) | #21 Riemann-Hilbert | original |

---

## Priority 3: Millennium Prize Problems

The Clay Mathematics Institute's $1M problems.

| # | Proof | Problem | Status |
|---|-------|---------|--------|
| [x] | [p-vs-np](src/data/proofs/p-vs-np) | P vs NP | original |
| [x] | [hodge-conjecture](src/data/proofs/hodge-conjecture) | Hodge Conjecture | original |
| [x] | [yang-mills](src/data/proofs/yang-mills) | Yang-Mills Mass Gap | original |
| [x] | [birch-swinnerton-dyer](src/data/proofs/birch-swinnerton-dyer) | BSD Conjecture | original |

---

## Priority 4: Wiedijk's 100 (Remaining)

Classic theorems from the Wiedijk list.

### Calculus & Analysis
| # | Proof | Wiedijk # | Status |
|---|-------|-----------|--------|
| [x] | [greens-theorem](src/data/proofs/greens-theorem) | #21 | axiom-based |
| [x] | [leibniz-pi](src/data/proofs/leibniz-pi) | #26 | mathlib |
| [x] | [taylor-theorem](src/data/proofs/taylor-theorem) | #35 | mathlib |
| [x] | [mean-value-theorem](src/data/proofs/mean-value-theorem) | #75 | mathlib |
| [x] | [fourier-series](src/data/proofs/fourier-series) | #76 | axiom-based |
| [x] | [stirling-formula](src/data/proofs/stirling-formula) | #90 | mathlib |

### Number Theory
| # | Proof | Wiedijk # | Status |
|---|-------|-----------|--------|
| [x] | [pythagorean-triples](src/data/proofs/pythagorean-triples) | #23 | mathlib |
| [x] | [amgm-inequality](src/data/proofs/amgm-inequality) | #38 | mathlib |
| [x] | [pell-equation](src/data/proofs/pell-equation) | #39 | mathlib |
| [x] | [partition-theorem](src/data/proofs/partition-theorem) | #45 | axiom-based |
| [x] | [pi-transcendental](src/data/proofs/pi-transcendental) | #53 | axiom-based |
| [x] | [hermite-lindemann](src/data/proofs/hermite-lindemann) | #56 | axiom-based |
| [x] | [e-transcendental](src/data/proofs/e-transcendental) | #67 | axiom-based |
| [x] | [sum-of-kth-powers](src/data/proofs/sum-of-kth-powers) | #77 | original |
| [x] | [fundamental-arithmetic](src/data/proofs/fundamental-arithmetic) | #80 | mathlib |
| [x] | [prime-reciprocal-divergence](src/data/proofs/prime-reciprocal-divergence) | #81 | mathlib |

### Algebra
| # | Proof | Wiedijk # | Status |
|---|-------|-----------|--------|
| [x] | [solution-of-cubic](src/data/proofs/solution-of-cubic) | #37 | axiom-based |
| [x] | [minkowski-theorem](src/data/proofs/minkowski-theorem) | #40 | axiom-based |
| [x] | [puiseux-theorem](src/data/proofs/puiseux-theorem) | #41 | axiom-based |
| [x] | [binomial-theorem](src/data/proofs/binomial-theorem) | #44 | mathlib |
| [x] | [general-quartic](src/data/proofs/general-quartic) | #46 | wip |
| [x] | [bezout-identity](src/data/proofs/bezout-identity) | #60 | mathlib |
| [x] | [lagrange-theorem](src/data/proofs/lagrange-theorem) | #71 | mathlib |
| [x] | [sylow-theorems](src/data/proofs/sylow-theorems) | #72 | mathlib |
| [x] | [cauchy-schwarz](src/data/proofs/cauchy-schwarz) | #78 | mathlib |

### Geometry
| # | Proof | Wiedijk # | Status |
|---|-------|-----------|--------|
| [x] | [triangle-angle-sum](src/data/proofs/triangle-angle-sum) | #27 | mathlib |
| [x] | [pascals-hexagon](src/data/proofs/pascals-hexagon) | #28 | axiom-based |
| [x] | [feuerbachs-theorem](src/data/proofs/feuerbachs-theorem) | #29 | axiom-based |
| [x] | [triangular-reciprocals](src/data/proofs/triangular-reciprocals) | #42 | mathlib |
| [x] | [isoperimetric-theorem](src/data/proofs/isoperimetric-theorem) | #43 | axiom-based |
| [x] | [platonic-solids](src/data/proofs/platonic-solids) | #50 | complete |
| [x] | [herons-formula](src/data/proofs/herons-formula) | #57 | mathlib |
| [x] | [isosceles-triangle](src/data/proofs/isosceles-triangle) | #65 | mathlib |
| [x] | [dissection-of-cubes](src/data/proofs/dissection-of-cubes) | #82 | original |
| [x] | [morleys-theorem](src/data/proofs/morleys-theorem) | #84 | axiom-based |
| [x] | [lebesgue-measure](src/data/proofs/lebesgue-measure) | #86 | mathlib |
| [x] | [desargues-theorem](src/data/proofs/desargues-theorem) | #87 | verified |
| [x] | [picks-theorem](src/data/proofs/picks-theorem) | #92 | axiom-based |
| [x] | [ptolemys-theorem](src/data/proofs/ptolemys-theorem) | #95 | mathlib |
| [x] | [descartes-rule-of-signs](src/data/proofs/descartes-rule-of-signs) | #100 | wip |

### Combinatorics & Probability
| # | Proof | Wiedijk # | Status |
|---|-------|-----------|--------|
| [x] | [ballot-problem](src/data/proofs/ballot-problem) | #30 | mathlib |
| [x] | [combinations-formula](src/data/proofs/combinations-formula) | #58 | mathlib |
| [x] | [fair-games-theorem](src/data/proofs/fair-games-theorem) | #62 | axiom-based |
| [x] | [erdos-szekeres](src/data/proofs/erdos-szekeres) | #73 | wip |
| [x] | [derangements](src/data/proofs/derangements) | #88 | mathlib |
| [x] | [factor-remainder-theorem](src/data/proofs/factor-remainder-theorem) | #89 | mathlib |
| [x] | [cramers-rule](src/data/proofs/cramers-rule) | #97 | mathlib |
| [x] | [buffons-needle](src/data/proofs/buffons-needle) | #99 | original |

---

## Priority 5: Pedagogical Examples

Educational proofs that demonstrate Lean concepts.

| # | Proof | Description |
|---|-------|-------------|
| [x] | [sqrt2-examples](src/data/proofs/sqrt2-examples) | Basic Lean syntax examples |
| [x] | [sqrt2-from-axioms](src/data/proofs/sqrt2-from-axioms) | Building from first principles |

---

## How to Add Annotations

1. Read the Lean source file in `proofs/Proofs/<Name>.lean`
2. Identify key concepts, definitions, theorems, and proof steps
3. Create annotations in `src/data/proofs/<slug>/annotations.json`
4. Each annotation should have:
   - `id`: Unique identifier (e.g., `ann-intro`, `ann-main-theorem`)
   - `proofId`: The proof slug
   - `range`: `{ startLine, endLine }`
   - `type`: `concept`, `definition`, `theorem`, `tactic`, `note`
   - `title`: Short descriptive title
   - `content`: Markdown explanation (supports LaTeX with `$$...$$`)
   - `significance`: `critical`, `major`, `minor`
   - `relatedConcepts`: Array of related topics

5. Run `npx tsx scripts/annotations/build.ts` to validate and rebuild listings

### Example Annotation

```json
{
  "id": "ann-main-theorem",
  "proofId": "example-proof",
  "range": { "startLine": 42, "endLine": 50 },
  "type": "theorem",
  "title": "Main Theorem",
  "content": "**Theorem**: For all $n$, we have $P(n)$.\n\nThis follows from...",
  "mathContext": "$\\forall n, P(n)$",
  "significance": "critical",
  "relatedConcepts": ["induction", "recursion"]
}
```

---

## Progress Tracking

- **Completed**: 73/73
- **Last Updated**: 2025-12-30

When you complete a proof, change `[ ]` to `[x]` and update the count above.
