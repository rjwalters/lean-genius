# Creativity Strategies Reference

Quick reference for mathematical proof ideation strategies.

---

## Strategy Catalog

### 1. Analogical Transfer

**What**: Map the problem to a similar solved problem, transfer the solution technique.

**When to use**:
- Problem structure feels familiar
- Related proofs exist in the gallery
- Domain has well-developed techniques

**How**:
1. Identify structural features (types, relations, constraints)
2. Search for proofs with similar features
3. Extract the core technique
4. Adapt to current context

**Example**:
- "Irrationality of √2 uses contradiction + descent"
- "Can we use contradiction + descent for √3?"

---

### 2. Constraint Relaxation

**What**: Prove a weaker/simpler version first.

**When to use**:
- Full problem seems intractable
- Special cases are known
- Need to build intuition

**How**:
1. Identify constraints in the statement
2. Relax one or more constraints
3. Prove the weakened version
4. Strengthen incrementally

**Relaxation types**:
- Bound relaxation: "for n > N" instead of "for all n"
- Object restriction: "for primes of form 4k+1" instead of "all primes"
- Condition addition: "assuming GRH"
- Existential weakening: "there exists" instead of "for all"

---

### 3. Constraint Tightening

**What**: Prove something stronger that implies the target.

**When to use**:
- Target seems "almost provable"
- Stronger statements have more structure
- Induction needs stronger hypothesis

**How**:
1. Identify what "more" could be proven
2. Check if the stronger statement is known
3. Attempt the stronger statement
4. Weaker target follows as corollary

**Tightening types**:
- Quantitative: "infinitely many" → "density > 0"
- Constructive: "exists" → "here's how to find it"
- Uniform: "for each n" → "for all n simultaneously"

---

### 4. Representation Shift

**What**: Reformulate the problem in a different mathematical language.

**When to use**:
- Current formulation seems awkward
- Other domains have better tools
- Cross-domain connections exist

**How**:
1. Identify the core mathematical objects
2. Find equivalent representations in other areas
3. Reformulate the statement
4. Apply techniques from new domain
5. Translate result back

**Domain shifts**:
- Number theory → Algebraic (ring theory, ideals)
- Discrete → Continuous (generating functions, analysis)
- Local → Global (topology, sheaves)
- Concrete → Abstract (categories, functors)

---

### 5. Decomposition

**What**: Break the problem into independent sub-problems.

**When to use**:
- Problem has multiple conditions
- Natural phases or cases exist
- Divide and conquer is possible

**How**:
1. Identify logical structure (A ∧ B, A → B, ∀x.∃y, etc.)
2. Separate into independent components
3. Solve each component
4. Combine for full result

**Decomposition types**:
- By cases: "either A or B; prove both"
- By structure: "first prove lemma, then main theorem"
- By layer: "base case + inductive step"
- By condition: "under assumption X... under assumption ¬X..."

---

### 6. Proof by Contradiction

**What**: Assume the negation, derive absurdity.

**When to use**:
- Direct proof seems blocked
- Negation gives useful structure
- Minimal counterexample arguments

**How**:
1. Assume statement is false
2. Derive consequences of the negation
3. Find a contradiction
4. Conclude original statement is true

**Contradiction types**:
- Logical: derive P ∧ ¬P
- Structural: "would need infinitely many, but finite exist"
- Counting: "more pigeons than holes"
- Well-ordering: "minimal element that shouldn't exist"

---

### 7. Induction

**What**: Prove base case + step, conclude for all.

**When to use**:
- Statement involves natural numbers
- Recursive structure is present
- "Smallest counterexample" arguments

**Induction types**:
- Simple: P(0) ∧ (P(n) → P(n+1))
- Strong: (∀k<n. P(k)) → P(n)
- Structural: on syntax, trees, formulas
- Well-founded: on any well-founded relation
- Transfinite: for ordinals

---

### 8. Construction / Existence

**What**: Build an explicit witness.

**When to use**:
- Statement claims something exists
- Want constructive proof
- Witness illuminates structure

**How**:
1. Understand what properties witness needs
2. Build candidate step by step
3. Verify all properties
4. Package as existence proof

**Construction methods**:
- Direct: "here's the object"
- Iterative: "keep refining until done"
- Limiting: "take the limit of approximations"
- Selecting: "choose from available options"

---

### 9. Counting Arguments

**What**: Count in two ways, derive equality or bound.

**When to use**:
- Combinatorial structure present
- Finite sets involved
- Pigeonhole situations

**How**:
1. Identify what to count
2. Count in first way
3. Count in second way
4. Compare counts

**Counting techniques**:
- Bijection: |A| = |B|
- Injection: |A| ≤ |B|
- Pigeonhole: if |A| > k|B|, some hole has > k pigeons
- Inclusion-exclusion: |A ∪ B| = |A| + |B| - |A ∩ B|
- Double counting: same set, two perspectives

---

### 10. Probabilistic Method

**What**: Show existence by showing positive probability.

**When to use**:
- Want to show something exists
- Random objects often work
- Counting exact objects is hard

**How**:
1. Define random experiment
2. Define "bad" events
3. Show P(all bad) < 1
4. Therefore "good" object exists

**Probabilistic techniques**:
- Union bound: P(∃ bad) ≤ Σ P(bad_i)
- Expectation: E[X] > 0 → X > 0 sometimes
- Lovász Local Lemma: dependent events
- Concentration: random values near expectation

---

### 11. Symmetry / Group Actions

**What**: Exploit symmetry to simplify.

**When to use**:
- Objects have natural symmetries
- Group theory applies
- Want to quotient out equivalences

**How**:
1. Identify symmetry group
2. Study group action
3. Work with orbits/quotients
4. Lift results back

**Symmetry applications**:
- Reduce to canonical form
- Count up to isomorphism
- Use representation theory
- Burnside/Polya counting

---

### 12. Limiting Arguments

**What**: Take limits to extend finite results.

**When to use**:
- Finite cases are known
- Compactness arguments possible
- Want to pass from approx to exact

**Limiting types**:
- Density: prove for density 1 set
- Subsequential: extract convergent subsequence
- Compactness: every open cover has finite subcover
- Continuity: limits preserve properties

---

## Combination Matrix

Which strategies combine well?

| + | Analogy | Relax | Tighten | Repr | Decomp | Contrad | Induct | Construct | Count | Prob | Symm | Limit |
|---|---------|-------|---------|------|--------|---------|--------|-----------|-------|------|------|-------|
| **Analogy** | — | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| **Relax** | ✓ | — | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| **Tighten** | ✓ | ✓ | — | ✓ | ✓ | | ✓ | | | | | |
| **Repr** | ✓ | ✓ | ✓ | — | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| **Decomp** | ✓ | ✓ | ✓ | ✓ | — | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ |
| **Contrad** | ✓ | ✓ | | ✓ | ✓ | — | ✓ | | ✓ | | | |
| **Induct** | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | — | ✓ | ✓ | ✓ | | ✓ |
| **Construct** | ✓ | ✓ | | ✓ | ✓ | | ✓ | — | ✓ | ✓ | ✓ | ✓ |
| **Count** | ✓ | ✓ | | ✓ | ✓ | ✓ | ✓ | ✓ | — | ✓ | ✓ | |
| **Prob** | ✓ | ✓ | | ✓ | ✓ | | ✓ | ✓ | ✓ | — | ✓ | ✓ |
| **Symm** | ✓ | ✓ | | ✓ | ✓ | | | ✓ | ✓ | ✓ | — | |
| **Limit** | ✓ | ✓ | | ✓ | ✓ | | ✓ | ✓ | | ✓ | | — |

**Powerful combinations**:
- Contradiction + Counting = "too many/too few" arguments
- Induction + Tightening = strong induction hypotheses
- Representation + Analogy = cross-domain techniques
- Probabilistic + Counting = Lovász Local Lemma style
- Decomposition + Limit = approximate then pass to limit

---

## Quick Decision Guide

```
What's blocking progress?

├── "Can't start the proof"
│   ├── Try: Decomposition (what lemmas would help?)
│   ├── Try: Representation Shift (different language?)
│   └── Try: Analogy (how were similar problems solved?)
│
├── "Stuck in the middle"
│   ├── Try: Constraint Relaxation (weaker version?)
│   ├── Try: Contradiction (assume false, find absurdity?)
│   └── Try: Cases (split into subcases?)
│
├── "Can't finish / last step fails"
│   ├── Try: Constraint Tightening (prove more to get what you need?)
│   ├── Try: Different Construction (try building a different witness?)
│   └── Try: Limit Argument (approximate and pass to limit?)
│
└── "No idea what to try"
    ├── Try: Analogical Search (find similar solved problems)
    ├── Try: Wild Card Brainstorm (crazy ideas from divergent.md)
    └── Try: Cross-Domain View (how would a physicist see this?)
```
