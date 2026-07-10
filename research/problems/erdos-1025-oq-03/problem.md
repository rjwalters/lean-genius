# Problem: Algorithmic Complexity of Finding Large Independent Sets in Pair Functions

**Slug**: erdos-1025-oq-03
**Created**: 2026-07-09T17:03:07-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\text{Given a valid pair function } f : \binom{[n]}{2} \to [n] \text{ with } f(\{x,y\}) \notin \{x,y\},
$$
$$
\text{find an independent set } X \subseteq [n] \text{ (i.e. } f(\{x,y\}) \notin X \text{ whenever } x,y \in X)
$$
$$
\text{of size } |X| = \Omega\!\left(n^{1/2}\right), \text{ matching } g(n) = \Theta(n^{1/2}).
$$
$$
\textbf{Question: } \text{Is there a } \mathrm{poly}(n) \text{ (or near-linear) algorithm producing such an } X\text{, and how hard is the exact/optimal version?}
$$

### Plain Language

Erdős Problem #1025 established that every valid pair function on $\{1,\dots,n\}$ has a
guaranteed independent set of size $g(n) = \Theta(n^{1/2})$. That is an *existence* result.
This open question asks about the **algorithmic** side: given a specific pair function $f$
as input, how efficiently can we actually *compute* an independent set achieving the
$\Omega(n^{1/2})$ bound, and how hard is it to find a *maximum* independent set exactly? We
want to know both the complexity of matching the extremal guarantee and the complexity of
optimizing beyond it.

### Why This Matters

Extremal combinatorics frequently proves existence via non-constructive tools (here, the
probabilistic deletion method of Spencer). Turning such an existence proof into an efficient
algorithm — "algorithmic derandomization" — is a recurring and important theme (cf. the
Lovász Local Lemma and the Moser–Tardos algorithm). Pair functions are a clean special case
of set mappings and of $3$-uniform hypergraph independent sets, so an efficient constructive
version illuminates a whole family of extremal problems. Conversely, an NP-hardness result
for the *maximum* independent set version would delineate exactly where tractability ends.

## Known Results

### What's Already Proven

- **Existence, $g(n) = \Theta(n^{1/2})$** — Spencer (1972) lower bound + Conlon–Fox–Sudakov
  (2016) upper bound; formalized in gallery proof `erdos-1025`
  (`Proofs/Erdos1025Problem.lean`).
- **Constructive lower bound (implicit).** Spencer's probabilistic argument (include each
  vertex independently with probability $p \approx n^{-1/2}$, then delete one endpoint of each
  violated pair) is a *randomized polynomial-time* procedure whose expected output is
  $\Omega(n^{1/2})$; the method of conditional expectations derandomizes it into a
  deterministic $\mathrm{poly}(n)$ algorithm.
- **Greedy $\Omega(n^{1/3})$.** The original Erdős–Hajnal (1958) greedy argument is an explicit
  deterministic algorithm, but only certifies the weaker $n^{1/3}$ bound.
- **NP-hardness of general independent set** — maximum independent set in graphs/hypergraphs is
  NP-hard (Karp 1972); the pair-function constraint is a structured 3-uniform hypergraph, so
  hardness does not transfer automatically.

### What's Still Open

- Is there a *deterministic, near-linear-time* algorithm that always outputs an independent
  set of size $\Omega(n^{1/2})$ (matching $g(n)$ up to constants)?
- Is computing a **maximum** independent set for an arbitrary valid pair function NP-hard, or
  does the $f(\{x,y\}) \notin \{x,y\}$ structure admit a polynomial exact algorithm?
- What are the best achievable *constants* algorithmically, versus the extremal constant in
  $g(n) = \Theta(n^{1/2})$?

### Our Goal

Formalize the algorithmic layer on top of `erdos-1025`: (i) define an explicit deterministic
procedure `greedyIndependent` / `derandomizedIndependent` on `PairFunction`, and (ii) prove a
constructive lower bound `∀ f, isValidPairFunction f → isIndependent f (alg f) ∧ (alg f).card ≥ c * sqrt n`.
Reaching the full $\Omega(n^{1/2})$ derandomization is the stretch target; a fully verified
$\Omega(n^{1/3})$ greedy algorithm is the concrete first milestone.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1025 | Parent problem: existence of $\Theta(n^{1/2})$ independent set in pair functions | probabilistic method, extremal combinatorics, set mappings |
| ramseys-theorem | Independent/clique existence via extremal counting; algorithmic Ramsey lower bounds are the classic derandomization analogue | pigeonhole, induction, extremal bounds |
| szemeredi-regularity | Regularity/removal machinery underlies constructive extremal algorithms | regularity, counting, hypergraph structure |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Derandomize Spencer via conditional expectations**: implement the
   include-with-probability-$p$ + deletion argument, then replace random choices by the method
   of conditional expectations (choose each vertex to keep/drop so the conditional expected
   surviving independent-set size never decreases).
   - Why it might work: the pessimistic estimator $pn - \binom{n}{2}p^3$ is a low-degree
     polynomial that is easy to evaluate and update incrementally.
   - Risk: bookkeeping the "deleted endpoint" step deterministically is fiddly; may only yield
     $\Omega(n^{1/2})$ with a worse constant.

2. **Approach B — Structured greedy with a potential function**: process vertices in a smart
   order, maintaining the invariant that the chosen set stays independent, and charge each
   rejection to a distinct forbidden image.
   - Why it might work: gives a clean deterministic $\Omega(n^{1/3})$ (matching Erdős–Hajnal)
     and is directly formalizable in Lean over `Finset`.
   - Risk: pushing greedy past $n^{1/3}$ to $n^{1/2}$ is exactly the historically hard step.

### Key Difficulties

- Derandomization requires a verified pessimistic estimator and a monotonicity proof, which is
  heavier than the existence proof.
- The complexity of the *exact maximum* version is genuinely unknown; proving NP-hardness would
  need a gadget reduction respecting the $f(\{x,y\}) \notin \{x,y\}$ constraint.
- Bridging the informal "$\Omega(n^{1/2})$" to a Lean cardinality bound needs real-analysis
  `Real.sqrt` inequalities alongside `Finset.card` manipulation.

### What Would a Proof Need?

- Key lemma 1: correctness — `isIndependent f (alg f)` for the chosen algorithm `alg`.
- Key lemma 2: size — `(alg f).card ≥ c * Real.sqrt n` (or `≥ c * n^(1/3)` for the greedy
  milestone), via a pessimistic estimator / greedy potential argument.
- Technical requirements: `Finset.card` counting, `Real.sqrt`/`Real.rpow` monotonicity, and a
  clean computable model of `PairFunction` (already present in `Erdos1025Problem.lean`).

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The deterministic $\Omega(n^{1/3})$ greedy milestone is Medium and clearly formalizable; the
  full $\Omega(n^{1/2})$ derandomization and the exact-complexity classification are High/open.
- Analogous derandomizations (method of conditional expectations, Moser–Tardos for LLL) are
  well understood mathematically but nontrivial to formalize.
- Mathlib provides `Finset`, `Real.sqrt`, and probability scaffolding, but no ready-made
  conditional-expectation derandomization framework.

**Estimated Effort**:
- Exploration: 2–4 days
- If tractable (greedy $n^{1/3}$ milestone): 1–2 weeks
- If hard (full $n^{1/2}$ derandomization or hardness proof): unknown / open

## References

### Papers
- P. Erdős, A. Hajnal, "On the structure of set-mappings," Acta Math. Acad. Sci. Hungar. (1958)
  — greedy argument gives the constructive $n^{1/3}$ bound.
- J. Spencer, "Turán's theorem for $k$-graphs," Discrete Math. (1972) — probabilistic deletion
  method; the randomized algorithm that derandomizes to the $n^{1/2}$ bound.
- N. Alon, J. Spencer, "The Probabilistic Method," 4th ed., Wiley (2016) — Chapter on the method
  of conditional expectations / algorithmic derandomization.
- R. M. Karp, "Reducibility Among Combinatorial Problems" (1972) — NP-hardness of maximum
  independent set (context for the exact version).

### Online Resources
- https://erdosproblems.com/1025 — statement and status of the parent problem.

### Mathlib
- `Mathlib.Data.Finset.Card` — cardinality lemmas for the independent-set size bound.
- `Mathlib.Analysis.SpecialFunctions.Pow.Real` — `Real.rpow` for $n^{1/2}$, $n^{1/3}$ bounds.
- `Mathlib.Analysis.SpecialFunctions.Sqrt` — `Real.sqrt` monotonicity for the size estimate.
- `Mathlib.Data.Sym.Sym2` — unordered pairs, the domain of a `PairFunction`.

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
  - ramseys-theorem
  - szemeredi-regularity
difficulty: high
source: gallery-gap
created: 2026-07-09T17:03:07-07:00
```
