# Problem: Instantiating Ramsey Avoidance to a Numeric Diagonal Lower Bound R(m,m)>n

**Slug**: prob-method-applications-wip-01-oq-01
**Created**: 2026-06-27T11:33:01-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\binom{n}{m}\cdot 2^{\,1-\binom{m}{2}} < 1 \;\Longrightarrow\; R(m,m) > n
$$

Equivalently, in the integer form actually produced by specializing the gallery
lemma `ramsey_avoidance` to the complete graph $K_n$ (with $|E| = \binom{n}{2}$
and $|\mathrm{cliques}| = \binom{n}{m}$):

$$
\binom{n}{m}\cdot 2^{\,\binom{n}{2}-\binom{m}{2}+1} < 2^{\binom{n}{2}}
\;\Longrightarrow\; \exists\,\text{a 2-colouring of }E(K_n)\text{ with no monochromatic }K_m .
$$

### Plain Language

The parent gallery proof establishes a general "avoidance" theorem: over any
finite edge set $E$ with a family of $m$-element blocks, if
$|\mathrm{cliques}|\cdot 2^{|E|-m+1} < 2^{|E|}$ then some 2-colouring makes no
block monochromatic. This problem asks to *plug in the concrete numbers* for
the complete graph $K_n$ — the edge set has $\binom{n}{2}$ edges, the $m$-cliques
number $\binom{n}{m}$, and each clique has $\binom{m}{2}$ edges — and read off the
classical Erdős conclusion that the diagonal Ramsey number satisfies $R(m,m) > n$.
It is a specialization/arithmetic exercise on top of an already-verified engine,
not a new theorem.

### Why This Matters

This is the original showcase application of the probabilistic method: Erdős's
1947 proof that diagonal Ramsey numbers grow at least exponentially,
$R(m,m) > \lfloor 2^{m/2}\rfloor$, obtained without constructing any colouring.
The parent entry proves the abstract counting engine but stops short of the
named consequence; closing this gap turns an abstract existence lemma into the
historically famous numeric bound, making the gallery entry self-contained and
pedagogically complete. The value is in the connection (engine ⟶ named result),
since the bound itself is textbook.

## Known Results

### What's Already Proven

- `ramsey_avoidance` (parent gallery proof `prob-method-applications-wip-01`, `Proofs/ProbMethodApplicationsWIP.lean`) — the abstract avoidance theorem this problem instantiates.
- Erdős's diagonal lower bound $R(m,m) > \lfloor 2^{m/2}\rfloor$ — Erdős, *Some remarks on the theory of graphs*, Bull. AMS 53 (1947); textbook treatment in Alon–Spencer, *The Probabilistic Method*, Ch. 1.

### What's Still Open

- Supplying the concrete $K_n$ instantiation: defining `E` as `Sym2 (Fin n)` off-diagonal edges (or `(Finset.univ : Finset (Fin n)).powersetCard 2`) and `cliques` as the $\binom{n}{m}$ $m$-subsets, then discharging `hm` (each clique has $\binom{m}{2}$ edges) and the counting hypothesis `h`.
- Deriving the clean numeric corollary $R(m,m) > n$ (e.g. specializing to $n = \lfloor 2^{m/2}\rfloor$ and verifying the inequality, possibly via `native_decide` for small fixed $m$).

### Our Goal

Instantiate `ramsey_avoidance` to the explicit edge set of $K_n$, substitute
$|E| = \binom{n}{2}$, $|\mathrm{cliques}| = \binom{n}{m}$, and clique size
$\binom{m}{2}$, and obtain the numeric statement $R(m,m) > n$ under
$\binom{n}{m}\cdot 2^{1-\binom{m}{2}} < 1$. We are specializing an existing
verified engine, not proving a new bound.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| prob-method-applications-wip-01 | Parent entry; supplies the `ramsey_avoidance` lemma being instantiated | First-moment/union-bound counting, powerset cardinality bounds |
| prob-method-expectation | Provides the expectation form of the first-moment principle underlying the counting argument | First moment method, linearity of expectation |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Direct edge-set model. Take `E := (Finset.univ : Finset (Fin n)).powersetCard 2` (edges as 2-subsets), `cliques` as the image of `powersetCard m` under "all internal edges". Compute `Fintype.card E = n.choose 2`, `cliques.card = n.choose m`, prove `hm` (internal edges of an $m$-set number `m.choose 2`), then feed the binomial inequality to `ramsey_avoidance`.
   - Why it might work: `ramsey_avoidance` is already proved; only the cardinality bookkeeping and one arithmetic inequality remain.
   - Risk: Sym2 / 2-subset edge encodings carry fiddly Mathlib lemmas; counting internal edges of a clique and showing the clique-edge map is injective can be tedious.

2. **Approach B**: Numeric corollary for fixed/small `m` via decision procedures. Fix `m` and set $n = \lfloor 2^{m/2}\rfloor$, verifying $\binom{n}{m}2^{1-\binom{m}{2}} < 1$ with `decide`/`native_decide`, then quote `ramsey_avoidance`.
   - Why it might work: sidesteps the general binomial-inequality algebra; concrete numbers are decidable.
   - Risk: `native_decide` introduces `Lean.ofReduceBool` (axiom-count implications per project policy); only covers specific `m`, not the general statement.

### Key Difficulties

- Binomial arithmetic: rewriting $2^{\binom{n}{2}-\binom{m}{2}+1} < 2^{\binom{n}{2}}/\binom{n}{m}$ into the classical $\binom{n}{m}2^{1-\binom{m}{2}}<1$ requires care with truncated natural subtraction ($\binom{n}{2}-\binom{m}{2}$ in ℕ) versus the rational/real form.
- The existential-to-numeric step: turning "a non-monochromatic colouring of $K_n$ exists" into the statement "$R(m,m) > n$" needs a Mathlib-compatible definition of $R(m,m)$ (Ramsey number), which may not exist off-the-shelf and might have to be stated as the avoidance conclusion itself.
- Counting the edges/cliques of $K_n$: establishing `Fintype.card E = n.choose 2` and the clique-internal-edge count $\binom{m}{2}$ with an injective clique map.

### What Would a Proof Need?

- Key lemma 1: an edge-set model of $K_n$ with `Fintype.card E = n.choose 2`.
- Key lemma 2: the family of $m$-cliques with cardinality `n.choose m` and each clique contributing exactly `m.choose 2` internal edges (the `hm` hypothesis).
- Technical requirements: natural-number/real bridging for the exponent inequality; a chosen formal meaning for "$R(m,m) > n$" (avoidance form is sufficient and honest).

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The hard mathematical content (the union-bound existence engine) is already proved and verified in the parent entry; this is a specialization plus arithmetic.
- Similar instantiation-of-an-engine tasks are routine once the carrier set is modelled; the gallery already contains comparable counting/cardinality formalizations.
- Mathlib provides `Nat.choose`, `Finset.powersetCard`, `Finset.card`, `Sym2`, and `SimpleGraph` machinery that cover the required edge/clique counts; the main labor is bookkeeping, not deep theory.

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable: 3–5 days for the general $K_n$ instantiation (or ~1 day for a fixed-$m$ `native_decide` corollary)
- If hard: unknown — only if a faithful general Ramsey-number definition and the natural-subtraction exponent algebra prove unexpectedly stubborn

## References

### Papers
- Erdős, Paul, *Some remarks on the theory of graphs*, Bull. AMS 53 (1947), 292–294 — original probabilistic lower bound $R(m,m) > \lfloor 2^{m/2}\rfloor$.
- Alon, Noga; Spencer, Joel H., *The Probabilistic Method*, 4th ed., Wiley (2016) — Chapter 1 derives exactly the $\binom{n}{m}2^{1-\binom{m}{2}}<1 \Rightarrow R(m,m)>n$ form being instantiated.

### Online Resources
- https://en.wikipedia.org/wiki/Probabilistic_method — overview of the method and the Ramsey lower bound application.
- https://en.wikipedia.org/wiki/Ramsey%27s_theorem#Lower_bounds_for_Ramsey_numbers — statement of the diagonal lower bound and the binomial inequality.

### Mathlib
- `Mathlib.Combinatorics.SimpleGraph.Basic` / `Mathlib.Combinatorics.SimpleGraph.Clique` — graphs, complete graphs, and clique predicates for modelling $K_n$ and $K_m$.
- `Mathlib.Data.Nat.Choose.Basic` — `Nat.choose` for $\binom{n}{2}$, $\binom{n}{m}$, $\binom{m}{2}$ and binomial identities.
- `Mathlib.Data.Finset.Powerset` / `Mathlib.Data.Finset.Card` — `powersetCard` and cardinality lemmas for enumerating edges and cliques.

## Metadata

```yaml
tags:
  - combinatorics
  - probabilistic-method
  - ramsey-theory
related_proofs:
  - prob-method-applications-wip-01
  - prob-method-expectation
difficulty: medium
source: gallery-gap
created: 2026-06-27T11:33:01-07:00
```
</content>
</invoke>
