# Problem: Erdős #1022 — Property B and Sparse Set Families

## Statement

### Plain Language

A set family $\mathcal{F}$ on a ground set $V$ has **Property B** (the Bernstein property) if there is a
2-coloring of $V$ such that no member $f \in \mathcal{F}$ is monochromatic. Equivalently, $\mathcal{F}$
is 2-colorable as a hypergraph.

For an integer $c \geq 0$, call $\mathcal{F}$ **$c$-sparse** if for every finite $X \subseteq V$,
$$
|\{ f \in \mathcal{F} : f \subseteq X \}| \;\leq\; c \cdot |X|.
$$

**Erdős #1022 (open).** Is there a function $c : \mathbb{N} \to \mathbb{N}$ with $c(t) \to \infty$ as
$t \to \infty$, such that for every $t$ every $c(t)$-sparse family $\mathcal{F}$ whose members all have
size at least $t$ has Property B?

### Formal Statement

$$
\exists \, c : \mathbb{N} \to \mathbb{N},\;
\bigl( c(t) \to \infty \bigr)
\;\wedge\;
\bigl( \forall \mathcal{F}\;\forall t,\;
 (\forall f \in \mathcal{F},\, |f| \geq t)
 \wedge \mathcal{F}\text{ is }c(t)\text{-sparse}
 \;\Longrightarrow\;
 \mathcal{F} \in \mathrm{PropB}
\bigr).
$$

Reference: <https://erdosproblems.com/1022>

## Classification

```yaml
tier: C
significance: 6
tractability: 3
erdosNumber: 1022
erdosUrl: https://erdosproblems.com/1022

tags:
  - erdos
  - combinatorics
  - hypergraphs
  - property-b
  - 2-coloring
```

**Significance**: 6/10 — a refinement of the classical Property B threshold programme
linking sparsity (rather than total edge count) to 2-colorability.

**Tractability**: 3/10 — the conjecture is open. Partial cases (matchings, degree-bounded
families) are tractable and several are formalized; a general proof would require either a
fresh combinatorial idea or a probabilistic deletion / LLL argument with a sparsity-aware
threshold.

## Why This Matters

1. **Sparsity vs. size threshold.** The classical Erdős (1963) first-moment bound forbids
   only $|\mathcal{F}| < 2^{t-1}$; the conjecture asks whether a *local* sparsity condition
   ("few members fit inside any small $X$") suffices instead. This is in the spirit of
   refining global to local constraints — common to the LLL and many modern hypergraph
   colouring results.
2. **Property B is the gateway to 2-colorability of hypergraphs.** Improvements feed back to
   $k$-uniform hypergraph 2-coloring lower / upper bounds (Beck, Radhakrishnan–Srinivasan).
3. **Mathlib gap.** Mathlib currently has no general hypergraph 2-colorability / Property B
   API; formalizing the definitions and basic structural lemmas opens the door to a wider
   programme of hypergraph theorems in Lean.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `erdos-1022-oq-01` | Property $B_k$ ($k$-colorability) generalization — monotonicity, hierarchy |
| `erdos-1022-oq-03` | Lovász Local Lemma path to Property B from bounded intersection degree |
| `erdos-100-oq-01` | Other Erdős hypergraph 2-coloring threshold questions |
| `erdos-13-oq-01` | Beck–Lovász style 2-coloring counterexamples |

## Related Problems

- Lovász (1968): the matching case ($c(2) = 1$) — formalized in `matching_has_propertyB`.
- Erdős (1963): $|\mathcal{F}| < 2^{t-1}$ probabilistic bound — formalized in
  `erdos_first_moment_bound`.
- Radhakrishnan–Srinivasan (2000): improved lower bound on the edge count needed to break
  Property B in $t$-uniform families.
- Open Question OQ-01: $k$-colorability generalization (Property $B_k$).
- Open Question OQ-03: Lovász Local Lemma application to Property B.
