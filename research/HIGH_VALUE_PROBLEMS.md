# High-Value Research Candidates

Problems worth our time, ranked by expected value.

---

## Tier S: Millennium Prize Sub-Problems

These won't be solved, but any progress is historically significant.

### Riemann Hypothesis - Related Results

| Problem | What We Could Do | EV |
|---------|------------------|-----|
| Explicit zero-free regions | Formalize current best bounds | 60+ |
| Consequences assuming RH | Prove theorems conditional on RH | 50+ |
| Li's criterion | Formalize and explore | 45+ |

### P vs NP - Barrier Results

| Problem | What We Could Do | EV |
|---------|------------------|-----|
| Relativization barriers | Formalize Baker-Gill-Solovay | 55+ |
| Natural proofs barrier | Formalize Razborov-Rudich | 55+ |
| Known NP-complete reductions | Complete the formalization | 40+ |

### Navier-Stokes

| Problem | What We Could Do | EV |
|---------|------------------|-----|
| 2D existence/uniqueness | This IS known - formalize it | 50+ |
| Specific solution classes | Formalize what's known | 45+ |

---

## Tier A: Famous Open Conjectures

### Twin Prime Conjecture

**Current state**: Zhang (2013) proved bounded gaps; Polymath8 improved to 246.

| Problem | What We Could Do | EV |
|---------|------------------|-----|
| Formalize bounded gaps theorem | First Lean formalization | 65 |
| Improve bound in specific cases | Novel mathematical contribution | 70+ |
| Prove for structured primes | E.g., primes in arithmetic progressions | 55 |

### Goldbach Conjecture

**Current state**: Verified up to 4×10^18. Weak Goldbach proved (Helfgott 2013).

| Problem | What We Could Do | EV |
|---------|------------------|-----|
| Formalize weak Goldbach | Major formalization achievement | 60 |
| Prove for specific residue classes | Novel partial result | 55 |
| Improve verification bounds | Extend computational results | 40 |

### Collatz Conjecture

**Current state**: Verified up to ~10^20. Tao (2019) proved "almost all" result.

| Problem | What We Could Do | EV |
|---------|------------------|-----|
| Formalize Tao's result | Significant formalization | 55 |
| Prove for specific forms | E.g., 2^n - 1, 3^n, etc. | 50 |
| Stopping time bounds | Improve known bounds | 45 |

### Legendre's Conjecture

**Prime between n² and (n+1)²**

| Problem | What We Could Do | EV |
|---------|------------------|-----|
| Prove for specific n ranges | Novel partial result | 55 |
| Connect to Bertrand's postulate | Generalization results | 45 |

---

## Tier B: Research-Level Problems

### Prime Gap Improvements

| Problem | What We Could Do | EV |
|---------|------------------|-----|
| Cramér's conjecture partial | Any progress is notable | 50 |
| Explicit prime bounds | Improve Dusart-type results | 45 |
| Gaps in arithmetic progressions | Less studied, more tractable | 40 |

### Additive Combinatorics

| Problem | What We Could Do | EV |
|---------|------------------|-----|
| Szemerédi's theorem formalization | Not yet in Lean | 55 |
| Green-Tao partial results | Primes in AP formalization | 50 |
| Roth's theorem improvements | 3-AP density bounds | 45 |

### Transcendence Theory

| Problem | What We Could Do | EV |
|---------|------------------|-----|
| Schanuel's conjecture cases | Novel partial results | 50 |
| Baker's theorem applications | Linear forms in logarithms | 45 |
| New transcendence proofs | Beyond e, π | 40 |

---

## Tier C: Valuable Formalizations

### Missing from Mathlib

| Result | Why It Matters | EV |
|--------|----------------|-----|
| Class field theory | Foundation for many results | 50 |
| Weil conjectures (Deligne) | Major 20th century result | 55 |
| Modularity theorem (partial) | Fermat's Last Theorem ingredient | 50 |

### Classical Results Not Formalized

| Result | Why It Matters | EV |
|--------|----------------|-----|
| Full Dirichlet theorem | Primes in AP, with error terms | 40 |
| Explicit Chebotarev | Number field applications | 35 |

---

## Anti-Recommendations (Tier D - Avoid)

**DO NOT work on:**

- More nth root irrationality (we have the pattern)
- More sums/products of known irrationals
- Variations of √2 proofs
- Textbook exercises
- "Complete the collection" problems
- Anything where the only novelty is "in Lean 4"

---

## Selection Criteria Summary

**PURSUE if:**
- Genuinely unknown result OR first Lean formalization of major theorem
- Would be publishable or notable in math community
- EV > 50

**CONSIDER if:**
- Important formalization gap
- Develops techniques for harder problems
- EV 30-50

**REJECT if:**
- Parameter variation of existing work
- Known for centuries with no new insight
- EV < 20

---

## Next Steps

1. Pick ONE problem from Tier A or high Tier B
2. Complete full value assessment
3. Define partial progress milestones
4. Accept that success probability is low
5. Document everything—failures are valuable
