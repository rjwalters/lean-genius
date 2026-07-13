# Problem: Computational Complexity of Cardano's Formula vs Numerical Cubic Root-Finding

**Slug**: solution-of-cubic-oq-04
**Created**: 2026-07-04
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
\text{Compare } T_{\text{Cardano}}(\varepsilon) \text{ and } T_{\text{Newton}}(\varepsilon):\ \text{arithmetic-operation cost of solving } x^3 + px + q = 0 \text{ to accuracy } \varepsilon.
$$

Cardano's closed form uses a fixed number of field operations plus square and cube roots; Newton iteration uses $O(\log\log(1/\varepsilon))$ iterations of $O(1)$ operations under quadratic convergence.

### Plain Language

The depressed cubic $x^3 + px + q = 0$ has the exact solution
$x = \sqrt[3]{-q/2 + \sqrt{q^2/4 + p^3/27}} + \sqrt[3]{-q/2 - \sqrt{q^2/4 + p^3/27}}$ (Cardano). Alternatively one can find a root numerically by Newton's method. We formalize a precise operation-count model and compare the two: Cardano is $O(1)$ arithmetic operations *plus two radical evaluations*, while Newton reaches accuracy $\varepsilon$ in $O(\log\log(1/\varepsilon))$ steps once inside the quadratic-convergence basin.

### Why This Matters

It makes rigorous the folklore claim that closed forms are not automatically "faster" — the cost hides in the radical (itself computed iteratively). This is a clean, self-contained case study in cost models for exact vs numerical algebra, and a good vehicle for formalizing a convergence-rate theorem (Newton) alongside an operation-count bound.

## Known Results

### What's Already Proven

- Cardano's formula: gallery parent `solution-of-cubic` and siblings — exact solvability by radicals.
- Newton's method quadratic convergence for functions with $f' \ne 0$ at the root and Lipschitz $f'$ — classical; partially in Mathlib (`Mathlib.Analysis.SpecialFunctions`, contraction-mapping tools).

### What's Still Open

- A fully formal, model-precise complexity comparison in Lean.
- Formal treatment of the cost of the radical evaluations inside Cardano (i.e. Cardano is *not* $O(1)$ if radicals are counted at accuracy $\varepsilon$).

### Our Goal

Define an abstract arithmetic-cost model (count of $+,-,\times,\div$ and root operations), state and prove: (i) Cardano evaluates in a constant number of field operations *given* radical oracles; (ii) Newton on $x^3+px+q$ converges quadratically from a suitable start, giving $O(\log\log(1/\varepsilon))$ iterations; (iii) conclude the comparison, honestly accounting for radical cost.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| solution-of-cubic | Cardano's exact formula | field radicals, casus irreducibilis |
| solution-of-cubic-oq-03 | Sibling: numerical/structural extensions | root-finding |
| solution-of-cubic-oq-05 | Sibling: further cubic-formula variations | radicals |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Abstract cost monad / operation counter**: Model a computation as a term counting arithmetic operations; prove Cardano's op-count is a fixed constant and Newton's is iteration-count times per-step cost.
   - Why it might work: keeps it combinatorial, avoids real-analysis subtleties for the counting part.
   - Risk: capturing radical cost fairly requires a cost model for `Real.sqrt`/cube root.

2. **Approach B — Convergence-rate theorem in ℝ**: Prove Newton's quadratic convergence for the specific cubic and extract the iteration count, using Mathlib analysis.
   - Why it might work: Mathlib has MVT, derivatives, and fixed-point tooling.
   - Risk: basin-of-attraction hypotheses must be stated carefully.

### Key Difficulties

- Defining a fair, non-circular cost model where radicals are not "free".
- Newton convergence needs an explicit starting-point hypothesis to guarantee the quadratic regime.

### What Would a Proof Need?

- Key lemma 1: quadratic convergence $|x_{n+1} - r| \le C |x_n - r|^2$ for $f(x)=x^3+px+q$ near a simple root $r$.
- Key lemma 2: iteration-count bound $n(\varepsilon) = O(\log\log(1/\varepsilon))$ from quadratic convergence.
- Technical requirements: derivative bounds, `Real.sqrt` / cube-root evaluation cost stub.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Self-contained, no open mathematics — the content is formalization of standard analysis + a cost model.
- Newton quadratic convergence is textbook and supported by Mathlib analysis lemmas.
- The main design work is choosing an honest cost model.

**Estimated Effort**:
- Exploration: 1 day
- If tractable: 3–5 days
- If hard: 1–2 weeks (if the cost model proves subtle)

## References

### Papers
- Kahan, numerical-analysis notes on cubic root-finding cost.
- Trefethen & Bau, "Numerical Linear Algebra" — Newton convergence rates.

### Online Resources
- Wikipedia "Cubic equation" and "Newton's method" — reference formulas.

### Mathlib
- `Mathlib.Analysis.Calculus.MeanValue` — derivative bounds for convergence.
- `Mathlib.Analysis.SpecialFunctions.Pow.Real` — radical evaluation.

## Metadata

```yaml
tags:
  - algebra
  - polynomial
  - complexity
related_proofs:
  - solution-of-cubic
  - solution-of-cubic-oq-03
difficulty: medium
source: proof-suggestion
created: 2026-07-04
```

**Significance**: 4/10
**Tractability**: 7/10
