# Problem: Union-Free Extremal Bounds for Multisets and Infinite Families

**Slug**: erdos-1023-oq-04
**Created**: 2026-07-09T15:40:19-07:00
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
F_{\text{multi}}(n, r) \;=\; \max \{\, |\mathcal{F}| : \mathcal{F} \subseteq \{0,1,\dots,r\}^{[n]},\ \text{no } A \in \mathcal{F} \text{ is the multiset union of other members} \,\}
$$

For the infinite-family variant, given an infinite ground set $\Omega$ we ask which cardinal invariants govern the largest union-free family $\mathcal{F} \subseteq \mathcal{P}(\Omega)$ closed under the same forbidden-union condition, and whether an analogue of the middle-layer bound $\binom{n}{\lfloor n/2 \rfloor}$ survives.

### Plain Language

Erdős Problem #1023 concerns *union-free* families of subsets of $\{1,\dots,n\}$: collections in which no set equals the union of other members. Its answer is exact and clean — the maximum size is $F(n) = \binom{n}{\lfloor n/2 \rfloor}$, achieved by the middle layer, with asymptotics $F(n) \sim \sqrt{2/\pi}\,\cdot 2^n/\sqrt{n}$. This open question asks how that story changes when subsets are replaced by *multisets* (elements may appear with multiplicity up to $r$) or when the ground set is *infinite*. In both settings the classical antichain/Sperner machinery no longer applies verbatim, and we want to know whether a comparable extremal formula and matching asymptotic can be recovered.

### Why This Matters

Union-free families sit at the crossroads of extremal set theory, Sperner-type antichain theory, and the additive-combinatorics notion of sum-free / union-free structure. The subset case is fully solved and formally verified in the gallery, so it forms a rigorous springboard. Understanding the multiset and infinite generalizations would clarify how much of the answer is intrinsic to the Boolean lattice versus an artifact of finiteness, connect the problem to Sidon-type and dissociated-set phenomena, and expose which parts of the Erdős–Kleitman upper-bound argument are lattice-structural rather than combinatorial.

## Known Results

### What's Already Proven

- $F(n) = \binom{n}{\lfloor n/2 \rfloor}$ for the subset case — Erdős–Kleitman (1968), *On combinations of sets*; formalized as `unionFreeMax_eq_middle` in `Proofs/Erdos1023Problem.lean` (upper bound axiomatized as `erdos_kleitman_upper`).
- Every antichain is union-free, and the middle layer is a maximum antichain — Sperner (1928); formalized as `antichain_unionFree` and `middleLayer_antichain`.
- Asymptotic $F(n) \sim \sqrt{2/\pi}\,\cdot 2^n/\sqrt{n}$ via Stirling — formalized as `unionFreeMax_asymptotic` (constant `asymptoticConstant`, `stirling_central` axiomatized).
- The subset result also follows from Problem #447 (2-union-free families) since union-free $\subseteq$ 2-union-free — Hunter's observation, `hunter_observation`.

### What's Still Open

- The exact value or growth rate of the multiset extremal function $F_{\text{multi}}(n,r)$ for $r \ge 2$; no Sperner analogue on $\{0,\dots,r\}^{[n]}$ (a graded lattice that is not Boolean) is known to be tight here.
- Whether an infinite ground set admits a meaningful extremal invariant, or whether the family can be made arbitrarily large so that only density/measure-theoretic refinements carry content.
- Which lemmas of the Erdős–Kleitman upper-bound argument are lattice-structural and survive the passage to $\{0,\dots,r\}^{[n]}$ or to $\mathcal{P}(\Omega)$ with $|\Omega|$ infinite.

### Our Goal

Formalize a precise Lean 4 statement of the multiset union-free extremal function $F_{\text{multi}}(n,r)$, establish the lower bound coming from the largest middle layer of the graded lattice $\{0,\dots,r\}^{[n]}$, and identify (with proof or documented gap) whether the Erdős–Kleitman upper bound generalizes. As a first concrete milestone, settle the base case $r = 1$ (recovering the existing subset theorem) and the smallest genuinely new case $r = 2$.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1023 | Direct parent: subset union-free extremal theorem being generalized | Antichains, Sperner middle layer, Erdős–Kleitman upper bound, Stirling asymptotics |
| erdos-447 | 2-union-free families with the same extremal answer; template for a stronger forbidden-union condition | Sperner-type extremal bound, Hunter's reduction |
| erdos-1062 | Arithmetic antichain analogue (no element divides two others), solved by middle-layer argument | Maximum-antichain / middle-layer bound |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Graded-lattice middle layer**: Model multisets as $\{0,\dots,r\}^{[n]}$, a graded lattice under coordinatewise $\le$, and take the largest rank level as a lower-bound union-free family (multiset unions strictly raise total degree, so an antichain in this order is union-free).
   - Why it might work: the union-strictly-increases-rank argument that makes antichains union-free is purely order-theoretic and does not use the Boolean structure.
   - Risk: the maximum antichain in $\{0,\dots,r\}^{[n]}$ (given by the middle rank, a Sperner-type result for this poset) may not be *tight* as a union-free family — the upper bound is the hard, possibly false, direction.

2. **Approach B — Reduction to the Boolean case**: Encode each coordinate value in $\{0,\dots,r\}$ by a monotone block of Boolean coordinates (order-embedding into $\{0,1\}^{n\lceil \log_2(r+1)\rceil}$) and transport the subset bound.
   - Why it might work: reuses the fully formalized subset result directly.
   - Risk: the embedding need not preserve the *union* operation, so union-freeness of the image may not correspond to union-freeness of the preimage; likely yields only a loose bound.

### Key Difficulties

- The multiset lattice is not Boolean, so Sperner's exact middle-layer theorem must be replaced by its graded-poset generalization, and the Erdős–Kleitman compression/shifting argument may not transfer.
- The infinite case likely lacks a finite extremal invariant, forcing a reformulation (density, measure, or cardinal characteristic) before anything can be proved.

### What Would a Proof Need?

- Key lemma 1: multiset union strictly increases total degree, hence any rank-antichain in $\{0,\dots,r\}^{[n]}$ is union-free (lower bound).
- Key lemma 2: a Sperner-type / LYM inequality for the graded lattice $\{0,\dots,r\}^{[n]}$ identifying the largest antichain.
- Technical requirements: a formal `Multiset`/`Fin (r+1) → Fin n` model, a rank function, and either a generalized Erdős–Kleitman upper bound or a documented axiom marking the open gap.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The subset case required an axiomatized Erdős–Kleitman upper bound even after full formalization; the multiset upper bound is strictly harder and may be genuinely open in the literature.
- The lower bound (rank-antichain) is plausibly tractable and mirrors `middleLayer_unionFree` from the parent proof, giving a concrete first deliverable.
- Mathlib provides `Finset`, `Multiset`, `Nat.Choose.Central`, and partial antichain/`IsAntichain` infrastructure, but no graded-poset Sperner theorem, so the hard direction lacks direct support.

**Estimated Effort**:
- Exploration: 2–4 days
- If tractable: 2–4 weeks (lower bound plus $r=2$ base cases)
- If hard: unknown (general multiset upper bound and infinite reformulation)

## References

### Papers
- P. Erdős and D. J. Kleitman, *On combinations of sets*, Nordisk Matematisk Tidskrift 16 (1968), 20–25 — establishes $F(n) = \binom{n}{\lfloor n/2\rfloor}$ for subsets; the argument to be generalized.
- E. Sperner, *Ein Satz über Untermengen einer endlichen Menge*, Math. Z. 27 (1928), 544–548 — antichain theorem underlying the lower bound; the graded-lattice analogue is what the multiset case needs.
- P. Frankl, *Extremal set systems*, Handbook of Combinatorics (1995), 1293–1329 — survey of union-free families and shifting/compression methods relevant to the upper bound.

### Online Resources
- https://erdosproblems.com/1023 — canonical statement and status of the parent Erdős problem.

### Mathlib
- `Mathlib.Data.Nat.Choose.Central` — central binomial coefficients for the exact and asymptotic subset bound.
- `Mathlib.Order.Antichain` / `Mathlib.Combinatorics.SetFamily` — antichain and set-family infrastructure to be adapted to the graded multiset lattice.
- `Mathlib.Data.Multiset.Basic` — multiset model for the generalized ground objects.

## Metadata

```yaml
tags:
  - combinatorics
  - set-families
  - erdos
  - extremal-combinatorics
  - antichains
related_proofs:
  - erdos-1023
  - erdos-447
difficulty: high
source: proof-suggestion
created: 2026-07-09T15:40:19-07:00
```
