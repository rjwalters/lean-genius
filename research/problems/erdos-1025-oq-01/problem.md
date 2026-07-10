# Problem: Exact Constant in the Independent-Set Asymptotic g(n) ~ c·n^{1/2} for Erdős Problem #1025

**Slug**: erdos-1025-oq-01
**Created**: 2026-07-09T17:03:08-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
g(n) = \min_{f \in \mathcal{F}_n} \; \max_{\substack{X \subseteq [n] \\ X \text{ independent for } f}} |X|,
\qquad
\mathcal{F}_n = \bigl\{ f : \tbinom{[n]}{2} \to [n] \;:\; f(\{x,y\}) \notin \{x,y\} \bigr\},
$$
$$
\text{determine } \; c = \lim_{n \to \infty} \frac{g(n)}{\sqrt{n}}, \quad \text{i.e. whether the limit exists and its exact value, given } g(n) = \Theta(n^{1/2}).
$$

### Plain Language

Erdős Problem #1025 is solved *up to constants*: for any function $f$ that maps each pair $\{x,y\}$ of an $n$-element ground set to a third element (never $x$ or $y$), one can always find an "independent" set $X$ — one containing none of the values $f(\{x,y\})$ for pairs inside $X$ — of size on the order of $\sqrt{n}$, and this is best possible. What remains open is the *exact constant*: does $g(n)/\sqrt{n}$ converge to a specific number $c$, and if so, what is $c$? The lower bound of Spencer and the upper bound of Conlon–Fox–Sudakov leave a gap between the multiplicative constants they produce.

### Why This Matters

Determining the sharp constant in an extremal asymptotic is the natural next step once the order of magnitude is pinned down, and such constants are notoriously hard (as in the Ramsey, Turán, and Zarankiewicz settings). Here the constant would quantify exactly how "spreadable" a pair function can be, and would sharpen the connection between set mappings (Erdős–Hajnal free-set theory) and hypergraph independence. A matching constant on both sides would turn the qualitative $\Theta(n^{1/2})$ into a genuine limit law, and the techniques (second-moment/deletion refinements on the lower side, algebraic or random-algebraic constructions on the upper side) tend to transfer to neighboring extremal problems.

## Known Results

### What's Already Proven

- Erdős–Hajnal (1958): $n^{1/3} \ll g(n) \ll (n \log n)^{1/2}$ — first bounds, gallery proof `erdos-1025`.
- Spencer (1972): $g(n) \gg n^{1/2}$ via the probabilistic (deletion) method — gallery proof `erdos-1025` (axiom `spencer_lower`).
- Conlon–Fox–Sudakov (2016): $g(n) \ll n^{1/2}$ via an algebraic construction, giving $g(n) = \Theta(n^{1/2})$ — gallery proof `erdos-1025` (axiom `cfs_upper`).

### What's Still Open

- Does $\lim_{n\to\infty} g(n)/\sqrt{n}$ exist? (Existence of the limit vs. mere $\Theta$.)
- If it exists, what is its value $c$? The published lower and upper constants do not coincide.
- More modestly: improve the best explicit lower constant $c_-$ (from optimizing the deletion argument $p n - \binom{n}{2}p^3$) and the best explicit upper constant $c_+$ (from the CFS construction) to narrow the interval $[c_-, c_+]$.

### Our Goal

Nail down, or provably narrow, the constant $c$ such that $g(n) = (c + o(1))\sqrt{n}$. A tractable first milestone is to formalize the *explicit* constant delivered by the deletion method: optimizing $p n - \binom{n}{2} p^{3}$ over $p$ yields $p^\* = \sqrt{2/(3(n-1))}$ and a guaranteed independent set of size $\bigl(\tfrac{2}{3}\bigr)^{3/2}\!\big/\!\sqrt{3}\cdot\sqrt{n}\,(1+o(1))$ after deletion, giving a concrete lower value of $c$ to compare against the CFS upper construction.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1025 | Parent proof: establishes $g(n) = \Theta(n^{1/2})$; this problem seeks the exact constant | Probabilistic/deletion method, algebraic construction, extremal counting |
| erdos-707 | Companion Erdős extremal-combinatorics problem using probabilistic bounds | Probabilistic method, extremal set systems |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Sharpen the deletion (lower) constant**: Include each vertex independently with probability $p$, then delete one endpoint of every "violated" configuration (pairs $x,y \in X$ with $f(\{x,y\}) \in X$). Expected surviving size $\ge pn - \binom{n}{2}p^3$; optimize $p$ to extract the best explicit $c_-$. Refine with a second-moment / alteration argument and by exploiting that each element is the image of at most $\binom{n}{2}$ pairs but on a random $X$ far fewer are active.
   - Why it might work: The deletion method is fully constructive and the optimization is elementary calculus; formalizable in Lean over `ℝ`/`ℕ`.
   - Risk: The naive deletion constant is unlikely to be tight; closing the gap to the true $c$ may need structure absent from a first-moment bound.

2. **Approach B — Tighten the CFS (upper) construction constant**: Analyze the algebraic pair-function construction of Conlon–Fox–Sudakov and extract the leading constant of its maximum independent set, then attempt a random-algebraic variant to lower $c_+$.
   - Why it might work: Explicit constructions expose the constant directly; random-algebraic methods have improved constants in analogous Ramsey/Turán problems.
   - Risk: The construction's constant may itself be non-optimal, and matching it to the lower bound could require a genuinely new idea.

### Key Difficulties

- Sharp constants for $\Theta$-results are among the hardest problems in extremal combinatorics; a matching pair may simply not be within reach of current methods.
- The lower-bound optimum from first moments and the upper-bound construction constant are produced by unrelated machinery, so proving they coincide (if they do) needs a bridge.
- Even *existence* of $\lim g(n)/\sqrt{n}$ is not obvious; supermultiplicativity/subadditivity (Fekete-type) arguments do not obviously apply because $f$ is not a product structure.

### What Would a Proof Need?

- Key lemma 1: A clean expected-size-minus-expected-violations bound for a random subset under a valid pair function, with the exact leading coefficient.
- Key lemma 2: A construction (algebraic or random-algebraic) whose maximum independent set has a provably matching leading coefficient.
- Technical requirements: Careful real-analytic optimization of the $p n - \binom{n}{2}p^3$ profile, concentration inequalities (Chebyshev/Chernoff) to pass from expectation to a.a.s. bounds, and control of lower-order terms.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The order of magnitude took 58 years (1958–2016) to settle; extracting the exact constant is a genuinely harder and open question with no known matching bounds.
- Sharp-constant analogues (e.g. exact constants in off-diagonal Ramsey numbers, Zarankiewicz problems) remain open despite decades of effort, indicating the class is hard.
- However, a *partial* and formalizable goal — the explicit deletion-method lower constant — is tractable: it is elementary optimization plus a standard alteration argument, well within Mathlib's real-analysis and `Finset` tooling.

**Estimated Effort**:
- Exploration: 3–5 days (read CFS 2016, extract both explicit constants).
- If tractable (explicit lower constant only): 1–2 weeks to formalize.
- If hard (matching constant / limit existence): unknown / likely open.

## References

### Papers
- P. Erdős and A. Hajnal, "On the structure of set-mappings," Acta Math. Acad. Sci. Hungar. 9 (1958), 111–131 — origin of the problem and the first $n^{1/3} \ll g(n) \ll (n\log n)^{1/2}$ bounds.
- J. Spencer, "Turán's theorem for k-graphs," Discrete Math. 2 (1972), 183–186 — deletion-method lower bound $g(n) \gg n^{1/2}$.
- D. Conlon, J. Fox, B. Sudakov, "Short proofs of some extremal results II," and related work (2016) — matching upper bound $g(n) \ll n^{1/2}$.

### Online Resources
- https://erdosproblems.com/1025 — canonical statement and status (solved up to constants) of Erdős Problem #1025.

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Turan` — Turán-type extremal machinery, template for deletion/optimization arguments.
- `Mathlib.Probability.Independence.Basic` — independence of indicator variables for the random-subset lower bound.
- `Mathlib.Analysis.SpecialFunctions.Pow.Real` — real powers and asymptotics for handling $n^{1/2}$ and optimizing over $p$.

## Metadata

```yaml
tags:
  - combinatorics
  - set-mappings
  - erdos
  - extremal-combinatorics
  - probabilistic-method
related_proofs:
  - erdos-1025
difficulty: high
source: proof-suggestion
created: 2026-07-09T17:03:08-07:00
```
