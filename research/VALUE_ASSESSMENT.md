# Value Assessment Framework

**Purpose**: Ensure we work on problems that matter, not stamp collecting.

## The Fundamental Question

Before starting any research, ask:

> "If we solve this, would anyone outside this repository care?"

If the answer is "no" or "only slightly," we should not work on it.

## Problem Tiers

### Tier S: Millennium Prize Problems
- P vs NP, Riemann Hypothesis, Navier-Stokes, Hodge, BSD, Yang-Mills
- **Success probability**: <0.01%
- **Value if solved**: Transformative (literally $1M prizes)
- **Our role**: Explore sub-problems, document approaches, understand barriers

### Tier A: Famous Open Conjectures
- Twin Prime, Goldbach, Collatz, Legendre, Cramér
- ABC Conjecture consequences, prime gap improvements
- **Success probability**: <1%
- **Value if solved**: Major mathematical achievement
- **Our role**: Prove special cases, improve bounds, find connections

### Tier B: Research-Level Open Problems
- Open problems from recent papers
- Improvements to known bounds
- Connections between areas not yet established
- Lemmas needed for bigger results
- **Success probability**: 1-10%
- **Value if solved**: Publishable result
- **Our role**: Genuine research attempts

### Tier C: Formalization Gaps
- Important theorems proven on paper but not in Lean/Mathlib
- Classical results missing from formal libraries
- **Success probability**: 50-90%
- **Value if solved**: Advances formal mathematics
- **Our role**: Careful formalization with educational value

### Tier D: Stamp Collecting (AVOID)
- ∛7 is irrational (trivial corollary)
- √2 + √3 is irrational (known for millennia)
- Obvious variations of existing proofs
- **Success probability**: 95%+
- **Value if solved**: Near zero
- **Our role**: DO NOT WORK ON THESE

## Time Budget Allocation

| Tier | Time Allocation | Rationale |
|------|-----------------|-----------|
| S | 20% | High risk, transformative reward |
| A | 30% | Hard but meaningful progress possible |
| B | 30% | Best risk/reward balance |
| C | 15% | Genuine contribution to formal math |
| D | 0% | Never |
| Learning | 5% | Understanding problem landscapes |

## Value Assessment Rubric

### 1. Significance (0-10)

*"If solved, what's the mathematical impact?"*

| Score | Criterion |
|-------|-----------|
| 10 | Millennium Prize level, reshapes a field |
| 8-9 | Named conjecture, would be major news |
| 6-7 | Would appear in good research journals |
| 4-5 | Interesting to specialists in the area |
| 2-3 | Useful lemma or modest result |
| 1 | Textbook exercise, already well-known |
| 0 | Trivial corollary of existing work |

### 2. Novelty (0-10)

*"Is this actually unknown to mathematics?"*

| Score | Criterion |
|-------|-----------|
| 10 | Truth value unknown, active research area |
| 8-9 | Open problem, less famous but genuine |
| 6-7 | Known result, novel formalization approach |
| 4-5 | Known, formalized elsewhere but not in Lean |
| 2-3 | Variation of well-trodden ground |
| 1 | Direct corollary of library theorem |
| 0 | Already in our gallery or Mathlib |

### 3. Tractability (0-10)

*"What's the realistic probability of progress?"*

| Score | Criterion |
|-------|-----------|
| 10 | Straightforward with known techniques |
| 8-9 | Challenging but clear path forward |
| 6-7 | Hard, will require ingenuity |
| 4-5 | Very hard, partial progress feasible |
| 2-3 | Extremely hard, worth attempting anyway |
| 1 | Near-impossible with current methods |
| 0 | Proven impossible or requires new math |

### 4. Strategic Value (0-10)

*"Does this unlock other problems or develop techniques?"*

| Score | Criterion |
|-------|-----------|
| 10 | Gateway to entire family of results |
| 8-9 | Develops technique applicable widely |
| 6-7 | Useful lemmas for related problems |
| 4-5 | Some downstream applications |
| 2-3 | Mostly standalone result |
| 1 | Dead end, no extensions |
| 0 | Actively misleading (wrong approach) |

## Expected Value Calculation

```
Expected_Value = Significance × (Novelty + Strategic) × Tractability_Factor

Where:
  Tractability_Factor = 0.3 + 0.7 × (Tractability / 10)
```

The tractability factor ensures:
- Completely intractable problems (T=0) still get 30% weight
- Easy problems (T=10) get full weight
- We don't over-weight easy but meaningless problems

### Decision Thresholds

| Expected Value | Decision |
|----------------|----------|
| > 100 | PURSUE IMMEDIATELY |
| 50-100 | STRONG CANDIDATE |
| 20-50 | WORTH CONSIDERING |
| 10-20 | LOW PRIORITY |
| < 10 | SKIP (likely stamp collecting) |

## Examples

### Example 1: Twin Prime - Bounded Gaps Improvement

- **Significance**: 9 (famous conjecture, any progress notable)
- **Novelty**: 9 (improving best known bound is novel)
- **Tractability**: 2 (extremely hard, Zhang/Polymath took years)
- **Strategic**: 8 (develops sieve methods, connects to RH)

```
EV = 9 × (9 + 8) × (0.3 + 0.7 × 0.2) = 9 × 17 × 0.44 = 67.3
```
**Decision**: STRONG CANDIDATE (despite low tractability)

### Example 2: ∛7 is Irrational

- **Significance**: 0 (trivial, known forever)
- **Novelty**: 0 (direct corollary of general theorem)
- **Tractability**: 10 (we have a template)
- **Strategic**: 0 (dead end, teaches nothing)

```
EV = 0 × (0 + 0) × 1.0 = 0
```
**Decision**: SKIP (stamp collecting)

### Example 3: Formalize Szemerédi's Theorem

- **Significance**: 7 (major result in combinatorics)
- **Novelty**: 6 (proven but not in Lean, would be notable)
- **Tractability**: 4 (hard formalization, long proof)
- **Strategic**: 7 (develops techniques for additive combinatorics)

```
EV = 7 × (6 + 7) × (0.3 + 0.7 × 0.4) = 7 × 13 × 0.58 = 52.8
```
**Decision**: WORTH CONSIDERING

### Example 4: Riemann Hypothesis - Explicit Zero-Free Region

- **Significance**: 10 (any RH progress is huge)
- **Novelty**: 10 (improving zero-free region is open)
- **Tractability**: 1 (extremely hard, may be impossible)
- **Strategic**: 10 (central to analytic number theory)

```
EV = 10 × (10 + 10) × (0.3 + 0.7 × 0.1) = 10 × 20 × 0.37 = 74
```
**Decision**: STRONG CANDIDATE (even with T=1!)

## Partial Progress Definition

For Tier S/A/B problems, define success broadly:

1. **Full solution**: Problem completely resolved
2. **Major progress**: Proven for infinite subfamily of cases
3. **Bound improvement**: Improved best known constant
4. **Special case**: Proven for specific interesting case
5. **Technique development**: New approach that might work
6. **Barrier identification**: Proved why certain approaches fail
7. **Formalization**: First Lean formalization of known partial results
8. **Connection**: Linked problem to another area

**All of these count as valuable outcomes for hard problems.**

## What We Should Actually Work On

### High-Value Candidates in Our Domain

1. **Prime Gaps**: Any improvement to bounded gaps results
2. **Goldbach Verification**: Extend computational verification, prove for classes
3. **Collatz Structure**: Prove for specific sequences, identify invariants
4. **Missing Mathlib Lemmas**: Genuinely needed results, not trivia
5. **Novel Connections**: Link areas in ways not previously formalized

### How to Find High-Value Problems

1. Check open issues in Mathlib for needed lemmas
2. Look at "future work" sections of recent papers
3. Check Clay Institute, AIM, MSRI problem lists
4. Look for problems where Lean formalization adds value
5. Find bounds that are believed non-optimal

## Anti-Patterns to Avoid

1. **Parameter Sweeping**: Proving ∛n for n=2,3,4,5,6... adds no value after first
2. **Obvious Corollaries**: If it follows in one line from existing theorem, skip
3. **Comfort Zone**: Choosing easy problems because success feels good
4. **Completion Bias**: Working on something just because we started it
5. **Gallery Padding**: Adding proofs just to increase count

## Integration with Research Workflow

### Before OBSERVE Phase

1. Complete Value Assessment Template (below)
2. Calculate Expected Value
3. If EV < 20, STOP and choose different problem
4. If Tier D, STOP immediately

### During Research

- Reframe "failure" as "barrier identification"
- Document all attempted approaches
- Partial progress is success for hard problems

### After Research

- Capture insights regardless of outcome
- Update knowledge base with what we learned
- If problem is Tier S/A, even documented failures are valuable
