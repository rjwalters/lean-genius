# Problem: Characterizing Non-Superincreasing DSS Sets

**Slug**: erdos-1-wip-01-oq-04
**Created**: 2026-07-09T00:00:00Z
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

$$
\text{Characterize } \mathcal{F}_{\mathrm{DSS}} = \{A \subset \mathbb{N} : \forall S, T \subseteq A,\ \textstyle\sum_{s \in S} s = \sum_{t \in T} t \Rightarrow S = T\}
$$

$$
\text{via intrinsic combinatorial predicates } P(A) \text{ with } P(A) \iff A \in \mathcal{F}_{\mathrm{DSS}}, \quad P \text{ not the superincreasing condition } \big(a_k > \textstyle\sum_{j<k} a_j\big).
$$

### Plain Language

A set $A$ of positive integers has *distinct subset sums* (DSS) when no two different subsets add up to the same total. There is a clean sufficient condition: if the elements, sorted increasingly, are *superincreasing* (each element exceeds the sum of all smaller ones, as with $1, 2, 4, 8, \ldots$), then $A$ automatically has DSS. But the converse fails: sets like $\{6, 9, 11, 12, 13\}$ have DSS yet are *not* superincreasing. This problem asks whether the structural theory built for superincreasing DSS sets can be extended to describe *all* DSS sets — ideally through combinatorial properties (a growth pattern, a counting invariant, a forbidden configuration) that certify DSS membership without simply re-checking the $2^n$ subset sums by definition.

### Why This Matters

The Erdős distinct-subset-sum problem (\$500, posed c. 1931) asks how small the largest element of an $n$-element DSS set can be, conjecturally $\max(A) \geq c \cdot 2^n$. The best constructions (Conway–Guy, $\max \approx 0.22 \cdot 2^n$) are superincreasing, but so are the far-from-optimal powers of 2 ($\max = 2^{n-1}$) — superincreasing-ness alone does not explain optimality. Because optimal DSS sets need not be superincreasing (indeed for $n \geq 4$ the extremal max is below $2^{n-1}$), any route to the Erdős conjecture that leans on the superincreasing lemma is fundamentally limited. A genuine characterization of the whole family $\mathcal{F}_{\mathrm{DSS}}$ — or even a strictly larger, still-verifiable sufficient class — would give researchers a handle on non-superincreasing extremal sets and a cleaner target for formalization than raw subset-sum injectivity.

## Known Results

### What's Already Proven

- `dss_superincreasing_extend` — superincreasing extension is sufficient for DSS; formalized in `Proofs/Erdos1Wip01.lean` (erdos-1-wip-01, verified, 0 sorries/0 axioms).
- `dss_elements_pos`, `not_dss_of_mem_zero` — every DSS set consists of positive integers, since $\emptyset$ and $\{0\}$ collide (erdos-1-wip-01).
- `dss_subset`, `dss_singleton` — DSS is hereditary (downward closed) and every singleton qualifies, so $\mathcal{F}_{\mathrm{DSS}}$ is an independence system (erdos-1-wip-01).
- `dss_sum_lower_bound`, `dss_sum_ge_pow_sub_one` — pigeonhole gives $2^n \le \mathrm{sum}(A) + 1$, i.e. $\mathrm{sum}(A) \ge 2^n - 1$ (erdos-1-wip-01).
- Counting bound $\max(A) \ge (2^n - 1)/n$ and the Dubroff–Fox–Xu entropy bound $\max(A) \ge \sqrt{2/\pi}\,2^n/\sqrt{n}$ (erdos-1 gallery cluster, OQ01/OQ02).

### What's Still Open

- Whether an intrinsic combinatorial predicate (not subset-sum injectivity restated) can characterize $\mathcal{F}_{\mathrm{DSS}}$ exactly.
- Whether there is a sufficient condition strictly weaker than superincreasing that still certifies DSS and captures known non-superincreasing examples such as $\{6, 9, 11, 12, 13\}$.
- Whether the independence system $\mathcal{F}_{\mathrm{DSS}}$ has additional axioms (beyond hereditary + positivity + the sum bound) distinguishing it structurally.
- Whether such a characterization would sharpen the max-element bound toward the Erdős constant $c$.

### Our Goal

Begin an OBSERVE-phase investigation: catalogue small non-superincreasing DSS sets, formalize candidate intermediate sufficient conditions in Lean (e.g. a "bounded-deficit" relaxation of superincreasing), and prove or refute that a chosen relaxed condition still implies DSS. The near-term formal target is a Lean lemma of the form "if $A$ satisfies weaker condition $Q$ then $A$ has DSS," strictly generalizing `dss_superincreasing_extend`, together with a witnessed example showing $Q$ captures a non-superincreasing set.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-1-wip-01 | Provides the superincreasing lemma, positivity, hereditary, and sum-bound results this problem extends | Finset subset-sum case analysis, induction, pigeonhole |
| erdos-1 | States the Erdős conjecture and proves the counting bound the characterization aims to sharpen | Counting / pigeonhole on subset sums |
| erdos-1-oq-02 | Entropy/Fourier lower bound giving the strongest current constraint on max element | Fourier analysis, entropy inequalities |
| erdos-1-oq-03 | Defines `minDSSBound` via `Nat.find`; a characterization would make its values more computable | `Nat.find`, existence witnesses |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Bounded-deficit relaxation**: Replace "each $a_k$ exceeds the sum of predecessors" with "each $a_k$ exceeds the sum minus a controlled deficit," then prove DSS survives when deficits cannot align to a collision.
   - Why it might work: known non-superincreasing DSS sets violate superincreasing by small margins; a quantified slack may still forbid subset-sum coincidences.
   - Risk: the deficit bookkeeping may reduce back to checking injectivity, giving no genuinely new predicate.

2. **Approach B — Forbidden-configuration / independence-system axioms**: Study $\mathcal{F}_{\mathrm{DSS}}$ as an independence system and search for a finite list of forbidden minors or an exchange-type axiom characterizing membership.
   - Why it might work: hereditary families often admit forbidden-substructure characterizations (matroid/greedoid analogy).
   - Risk: DSS independence systems are known not to be matroids (no exchange axiom), so a clean finite characterization may not exist.

### Key Difficulties

- Any candidate predicate must be provably equivalent to (or strictly imply) DSS without secretly re-encoding the $2^n$-subset-sum test.
- Non-superincreasing DSS sets are irregular; enumerating and pattern-matching them (e.g. via OEIS A005318 extremal sets) may not reveal a uniform law.

### What Would a Proof Need?

- Key lemma 1: a relaxed sufficient condition $Q$ with `Q A → hasDistinctSubsetSums A`, generalizing `dss_superincreasing_extend`.
- Key lemma 2: a concrete non-superincreasing witness (e.g. $\{6,9,11,12,13\}$) satisfying $Q$ but not the superincreasing predicate, verified in Lean.
- Technical requirements: Finset sum manipulation, `decide`/`Finset.powerset` evaluation for small witnesses, and careful case analysis mirroring the existing 4-case extension proof.

## Tractability Assessment

**Difficulty**: High

**Justification**:
- The full characterization is likely as hard as the Erdős conjecture itself; partial relaxations are more realistic.
- Similar hereditary-family characterizations (matroids, greedoids) exist but the DSS system lacks the exchange axiom, removing the standard toolkit.
- Mathlib provides Finset, powerset, and sum infrastructure sufficient to state and check candidate conditions on small sets, but no ready-made DSS theory beyond what erdos-1-wip-01 built.

**Estimated Effort**:
- Exploration: several days to enumerate small non-superincreasing DSS sets and propose a candidate predicate.
- If tractable: 1–3 weeks to formalize a strictly-weaker sufficient condition and a witness.
- If hard: unknown (a full characterization is plausibly open-problem hard).

## References

### Papers
- Erdős, P., "Problems in additive number theory," Proc. ICM Amsterdam, 1955 — original posing of the distinct-subset-sum question.
- Conway, J. H.; Guy, R. K., "Solution of a problem of P. Erdős," Colloq. Math. 20 (1968), 307–309 — superincreasing sequence with $\max \approx 0.22009 \cdot 2^n$.
- Dubroff, Q.; Fox, J.; Xu, M. W., "A note on the Erdős distinct subset sums problem," SIAM J. Discrete Math., 2021 — entropy lower bound $\max(A) \ge \sqrt{2/\pi}\,2^n/\sqrt{n}$.

### Online Resources
- https://oeis.org/A005318 — minimum largest element of an $n$-element DSS set (Conway–Guy sequence), listing extremal, often non-superincreasing, sets.
- https://www.erdosproblems.com/1 — Erdős Problem #1 catalogue entry with status and known bounds.

### Mathlib
- `Mathlib.Data.Finset.Powerset` — powerset enumeration for evaluating subset sums on small witnesses.
- `Mathlib.Algebra.BigOperators.Basic` — `Finset.sum` lemmas used throughout the DSS case analysis.
- `Mathlib.Data.Nat.Log` / `Mathlib.Algebra.Order.Monoid` — ordering and geometric-sum utilities for growth-condition bookkeeping.

## Metadata

```yaml
tags:
  - additive-combinatorics
  - subset-sums
  - extremal-combinatorics
  - structural-theory
  - number-theory
  - erdos
related_proofs:
  - erdos-1-wip-01
  - erdos-1
difficulty: high
source: proof-suggestion
created: 2026-07-09T00:00:00Z
```
