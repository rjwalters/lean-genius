# Problem: Lovász Local Lemma and Ramsey Lower Bounds

**Slug**: ramsey-r4k-extensions-oq-03
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\text{(Symmetric LLL) Events } A_1,\dots,A_m,\ \Pr[A_i]\le p,\ \text{each } A_i \text{ mutually independent of all but } \le d \text{ others},\ e\,p\,(d+1)\le 1 \Rightarrow \Pr\!\Big[\bigcap_i \overline{A_i}\Big] > 0.
$$
$$
\text{Application: a lower bound on the Ramsey number } R(k,k) \text{ via LLL over the "monochromatic } K_k\text{" events.}
$$

### Plain Language

The Lovász Local Lemma (LLL) says that if you have many "bad" events, each unlikely and each depending on only a few of the others, then with positive probability none of the bad events happens — so a configuration avoiding all of them exists. We want to formalize the symmetric LLL in Lean 4 and use it in Ramsey theory: model a random 2-coloring of the edges of $K_n$, let the bad events be "this particular $k$-clique is monochromatic," and apply LLL to prove that for suitable $n$ a coloring with no monochromatic $K_k$ exists, i.e. a lower bound $R(k,k) > n$.

### Why This Matters

The Lovász Local Lemma is one of the pillars of the probabilistic method, with applications far beyond Ramsey theory (hypergraph coloring, SAT, routing). It is not in Mathlib. The `ramsey-r4k-extensions` entry currently *axiomatizes* a probabilistic lower bound (`erdos_probabilistic_lower_bound`); a formalized LLL plus a Ramsey application would let us discharge that axiom with a proved statement and provide reusable probabilistic-method infrastructure for the wider gallery.

## Known Results

### What's Already Proven

- `ramsey-r4k-extensions` (AXIOMATIZED): `ramseyUpperBound`, exact small Ramsey numbers via `native_decide` (`r3_3_upper`, …), plus axioms `erdos_probabilistic_lower_bound`, `aks_r3k_upper_bound`, `kim_r3k_lower_bound`.
- Erdős's 1947 first-moment lower bound $R(k,k) > 2^{k/2}$ (the LLL slightly improves the constant).
- Mathlib `ProbabilityTheory` (independence, expectation) and `SimpleGraph` / `SimpleGraph.Clique` provide the combinatorial and probabilistic substrate.

### What's Still Open

- The Lovász Local Lemma (symmetric or general form) is not formalized in Mathlib.
- No Lean proof derives a Ramsey lower bound from LLL.

### Our Goal

Formalize the **symmetric** LLL first (statement + proof via the standard induction on the conditional-probability bound), then apply it to the monochromatic-clique events to obtain a lower bound on $R(k,k)$, replacing `erdos_probabilistic_lower_bound` with a theorem. Even the symmetric LLL as a standalone, reusable lemma — independent of the Ramsey application — is a substantial and valuable contribution.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| ramsey-r4k-extensions | Parent; axiom to discharge and Ramsey framing | ramseyUpperBound, native_decide, probabilistic bounds |
| prob-method-lovasz-local | Direct predecessor on the LLL itself | Lovász Local Lemma, dependency graphs |
| prob-method-applications | Probabilistic-method library and Erdős targets | first moment, expectation |
| ramseys-theorem | Classical Ramsey infrastructure | SimpleGraph.Clique, Ramsey numbers |

## Initial Thoughts

### Potential Approaches

1. **Symmetric LLL by the classical induction**: prove $\Pr[A_i \mid \bigcap_{j\in S}\overline{A_j}] \le 2p$ (or the sharper $x_i$-weighted bound) by induction on $|S|$, then conclude $\Pr[\bigcap \overline{A_i}] > 0$ from $ep(d+1)\le 1$. Instantiate with the $\binom{n}{k}$ monochromatic-clique events, whose dependency degree is bounded by cliques sharing an edge.
   - Why it might work: this is the textbook proof; each step is a finite conditional-probability manipulation.
   - Risk: managing conditional probabilities and the dependency-graph bookkeeping in Mathlib's measure-theoretic `ProbabilityTheory`.

2. **General (asymmetric) LLL with weights $x_i$**: prove the weighted form directly and derive the symmetric corollary.
   - Why it might work: cleaner induction invariant.
   - Risk: more setup before the first usable result.

### Key Difficulties

- Formalizing "mutual independence of $A_i$ from all but $\le d$ events" (a dependency graph on events) in Lean.
- Conditional-probability inequalities and the induction over conditioning sets.
- Bounding the dependency degree for the monochromatic-clique events.

### What Would a Proof Need?

- Key lemma 1: the conditional-probability induction bounding $\Pr[A_i \mid \bigcap_{j\in S}\overline{A_j}]$.
- Key lemma 2: positivity $\Pr[\bigcap_i \overline{A_i}] > 0$ under $ep(d+1)\le 1$.
- Key lemma 3: dependency-degree bound for monochromatic $K_k$ events, then arithmetic to a concrete $R(k,k) > n$.
- Technical requirements: `ProbabilityTheory` conditional probability / independence, `SimpleGraph.Clique`, finite product spaces for random colorings.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- LLL is a well-defined, self-contained theorem with a known elementary proof, so the target is clear.
- But conditional-probability and dependency-graph formalization in Mathlib is nontrivial and may be the bulk of the work.
- The symmetric form alone is a natural, decomposable first milestone even if the Ramsey application lags.

**Estimated Effort**:
- Exploration: 3-5 days (survey Mathlib conditional-probability / independence API)
- If tractable: several weeks (symmetric LLL, then the Ramsey application)
- If hard: the conditional-independence machinery may require new Mathlib-level infrastructure

## References

### Papers
- P. Erdős, L. Lovász, "Problems and results on 3-chromatic hypergraphs and some related questions," 1975 — original LLL.
- J. Spencer, "Ramsey's theorem — a new lower bound," JCTA 1975 — LLL applied to Ramsey numbers.
- Alon & Spencer, *The Probabilistic Method*, Ch. 5 — symmetric LLL and its Ramsey application.

### Online Resources
- Alon–Spencer Chapter 5 — the conditional-probability proof of the symmetric LLL.

### Mathlib
- `Mathlib.Probability.*` (independence, conditional probability, expectation) — probabilistic substrate.
- `Mathlib.Combinatorics.SimpleGraph.Clique` — monochromatic-clique events and Ramsey framing.

## Metadata

```yaml
tags:
  - combinatorics
  - probabilistic-method
  - lovasz-local-lemma
  - ramsey
  - probability
related_proofs:
  - ramsey-r4k-extensions
  - prob-method-lovasz-local
  - ramseys-theorem
difficulty: high
source: proof-suggestion
created: 2026-07-02
```

**Significance**: 6/10
**Tractability**: 4/10
