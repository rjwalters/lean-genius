# Proof Roadmap

A curated list of proofs to add to Lean Genius, selected for educational value, historical significance, and variety across mathematical domains.

## Current Proofs

| Proof | Domain | Status | Difficulty |
|-------|--------|--------|------------|
| Infinitude of Primes | Number Theory | Verified | Beginner |
| Irrationality of √2 | Number Theory | Pending | Beginner |
| Navier-Stokes Regularity | PDEs | Pending | Advanced |
| Russell's 1+1=2 | Foundations | Verified | Beginner |
| Cantor's Diagonalization | Set Theory | Verified | Intermediate |
| Fundamental Theorem of Calculus | Analysis | Verified | Intermediate |
| Gödel's First Incompleteness | Mathematical Logic | Pending | Advanced |

---

## Proposed Additions

### 1. Gödel's First Incompleteness Theorem

**Domain:** Mathematical Logic
**Difficulty:** Advanced
**Priority:** High

> Any consistent formal system capable of expressing basic arithmetic contains statements that are true but unprovable within the system.

**Why it's perfect for Lean Genius:**
- Meta-mathematical: a formal proof *about* formal proofs
- Philosophically profound - shattered Hilbert's program
- Rich annotation potential: Gödel numbering, diagonalization, self-reference
- Historical weight: 1931, Vienna Circle, changed mathematics forever

**Existing formalizations:** Paulson's Isabelle formalization; various Lean/Coq versions exist

---

### 2. Russell's 1+1=2 (Peano Arithmetic)

**Domain:** Foundations
**Difficulty:** Beginner
**Priority:** High

> From the Peano axioms, prove that the successor of 1 equals 2.

**Why it's perfect for Lean Genius:**
- Famous meme: "362 pages in Principia Mathematica to prove 1+1=2"
- Accessible hook for general audience
- Shows how formal systems build from first principles
- Demonstrates why type theory makes this trivial today

**Approach:** Build Peano naturals from scratch, define addition, prove `succ 1 = 2`

---

### 3. Cantor's Diagonalization

**Domain:** Set Theory
**Difficulty:** Intermediate
**Priority:** High

> The real numbers are uncountable - there is no bijection between ℕ and ℝ.

**Why it's perfect for Lean Genius:**
- Elegant proof technique (diagonalization appears everywhere)
- Counterintuitive result that sparks discussion
- Gateway to understanding cardinalities and infinity
- Short proof, rich in insight

**Existing formalizations:** Standard in Mathlib

---

### 4. Fundamental Theorem of Calculus

**Domain:** Analysis
**Difficulty:** Intermediate
**Priority:** Medium

> Differentiation and integration are inverse operations.

**Why it's perfect for Lean Genius:**
- Universally taught, universally important
- Bridges two major branches of calculus
- Shows how formalization handles limits rigorously
- Newton vs. Leibniz historical drama

**Existing formalizations:** Well-developed in Mathlib's analysis library

---

### 5. Pythagorean Theorem

**Domain:** Geometry
**Difficulty:** Beginner
**Priority:** Medium

> In a right triangle, a² + b² = c².

**Why it's perfect for Lean Genius:**
- Most recognized theorem in mathematics
- 300+ known proofs (algebraic, geometric, visual)
- Could showcase multiple proof styles
- Accessible to everyone

**Approach:** Formalize in Lean's geometry library or via inner product spaces

---

### 6. Fundamental Theorem of Algebra

**Domain:** Algebra/Analysis
**Difficulty:** Intermediate
**Priority:** Medium

> Every non-constant polynomial with complex coefficients has at least one complex root.

**Why it's perfect for Lean Genius:**
- Surprisingly hard to prove purely algebraically
- Multiple proof approaches: analysis, topology, algebra
- Connects different mathematical domains
- Named "fundamental" for good reason

**Existing formalizations:** In Mathlib, uses topological arguments

---

### 7. Undecidability of the Halting Problem

**Domain:** Computability Theory
**Difficulty:** Intermediate
**Priority:** High

> No algorithm can determine whether an arbitrary program will halt or run forever.

**Why it's perfect for Lean Genius:**
- Computer science crossover appeal
- Proof by diagonalization (connects to Cantor, Gödel)
- Practically relevant: limits of static analysis
- Accessible to programmers without heavy math background

**Approach:** Formalize Turing machines or use lambda calculus

---

### 8. Four Color Theorem

**Domain:** Graph Theory
**Difficulty:** Advanced
**Priority:** Low

> Every planar map can be colored with at most four colors such that no adjacent regions share a color.

**Why it's perfect for Lean Genius:**
- First major theorem proved by computer (1976)
- Controversial at the time - "is this really a proof?"
- Perfect for discussing computer-verified proofs
- Beautiful visual examples

**Existing formalizations:** Georges Gonthier's Coq proof (2005) - landmark formalization

---

### 9. Euler's Identity

**Domain:** Complex Analysis
**Difficulty:** Intermediate
**Priority:** Medium

> e^(iπ) + 1 = 0

**Why it's perfect for Lean Genius:**
- "Most beautiful equation in mathematics"
- Connects five fundamental constants: e, i, π, 1, 0
- Requires formalizing complex exponentials
- Short statement, deep meaning

**Approach:** Derive from Taylor series or complex exponential definition

---

### 10. Brouwer Fixed Point Theorem

**Domain:** Topology
**Difficulty:** Advanced
**Priority:** Low

> Every continuous function from a closed ball to itself has at least one fixed point.

**Why it's perfect for Lean Genius:**
- Intuitive statement: "stir coffee, one point stays put"
- Deep topological machinery (homology, degree theory)
- Applications: economics (Nash equilibrium), differential equations
- Gateway to algebraic topology

**Existing formalizations:** Various approaches in Lean/Coq using different proof methods

---

## Suggested Implementation Order

### Phase 1: Foundational Variety
1. **Russell's 1+1=2** - Accessible entry point
2. **Cantor's Diagonalization** - Elegant, intermediate
3. **Halting Problem** - CS appeal, connects themes

### Phase 2: Expand Domains
4. **Gödel's Incompleteness** - The crown jewel
5. **Pythagorean Theorem** - Universal recognition
6. **Euler's Identity** - Beauty and elegance

### Phase 3: Depth
7. **Fundamental Theorem of Calculus** - Educational cornerstone
8. **Fundamental Theorem of Algebra** - Cross-domain connections
9. **Brouwer Fixed Point** - Topological depth
10. **Four Color Theorem** - Computer-assisted proof history

---

## Selection Criteria

Each proof was evaluated on:

- **Educational Value:** Rich annotation potential, teachable moments
- **Historical Significance:** Impact on mathematics, interesting stories
- **Accessibility:** Range from beginner to advanced
- **Formalization Availability:** Existing Lean/Mathlib proofs to reference
- **Domain Diversity:** Cover logic, algebra, analysis, geometry, CS, topology
- **Discussion Potential:** Sparks interesting comments and debates

---

## Notes

- Difficulty ratings assume familiarity with Lean basics
- "Priority" reflects balance of impact vs. implementation effort
- Some proofs (Gödel, Four Color) are substantial undertakings
- Consider community contributions for complex proofs
