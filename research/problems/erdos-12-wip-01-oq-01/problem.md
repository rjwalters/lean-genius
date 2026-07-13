# Problem: Quantitative Local Density Bound for Erdős #12 (Half-Residue Obstruction)

**Slug**: erdos-12-wip-01-oq-01
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $A \subseteq \mathbb{N}$ be a *divisibility-free* set (no element divides another).
The parent proof (`erdos-12-wip-01`) establishes the **local obstruction**: for each
$a \in A$, at most one larger element of $A$ is a multiple of $a$, and no two larger
elements are antipodal modulo $a$ (i.e. there are no $b, c \in A$, $b, c > a$, with
$b + c \equiv 0 \pmod a$).

The goal is to **sharpen** this into a *quantitative local density bound*: show that
among the residues $\{0, 1, \dots, a-1\}$, at most roughly half are available to the
larger elements of $A$. Concretely, for a fixed $a \in A$, define

$$
R_a = \{\, b \bmod a : b \in A,\ b > a \,\}.
$$

Prove a bound of the form

$$
|R_a| \le \left\lceil \frac{a}{2} \right\rceil + O(1),
$$

capturing that the antipodal-pair obstruction ($x$ and $a-x$ cannot both occur)
forbids at least one of each antipodal residue pair, so at most $\lceil a/2 \rceil$
residue classes mod $a$ can be occupied by larger elements.

### Plain Language

The parent proof shows a "no antipodal pairs mod $a$" rule for divisibility-free sets.
Pairing up each residue $x$ with its partner $a - x$, that rule says you can keep at
most one member of each pair. Since there are about $a/2$ such pairs, at most about
half of all residues mod $a$ can be used by the larger elements. This turns a purely
*structural* obstruction into a *counting* one — a density statement — which is the
natural first quantitative step toward a self-contained proof that divisibility-free
sets have density zero.

### Why This Matters

Erdős asked (question (iii)) whether $\sum_{n \in A} 1/n$ converges for every
divisibility-free set $A$. A quantitative local density bound is the elementary
engine behind such sparsity results. Formalizing the "at most half the residues"
step makes the local-to-global density argument concrete and reusable, and it is a
strictly self-contained refinement of an already-verified gallery result.

## Known Results

### What's Already Proven

- **Parent `erdos-12-wip-01`** (verified, 0 sorries): for each $a \in A$, at most one
  larger multiple of $a$ lies in $A$, and no two larger elements are antipodal mod $a$.
- Standard divisibility-free set theory (Behrend, Erdős): such sets have logarithmic
  density zero.

### What's Still Open

- Question (iii): convergence of $\sum_{n\in A} 1/n$ for all divisibility-free $A$
  (this OQ is only a *first step* toward it, not the full result).
- The $k$-fold antipodal generalization $a \mid (b_1 + \dots + b_k)$.

### Our Goal

Prove **only** the quantitative local statement $|R_a| \le \lceil a/2 \rceil + O(1)$
from the antipodal-pair obstruction — a finite, elementary counting lemma. Do not
attempt the full density-zero / convergence result in this problem.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-12-wip-01 | Direct parent; supplies the antipodal-pair obstruction | Modular arithmetic, divisibility |
| (divisibility-free set entries) | Density-zero context | Counting, Finset cardinality |

## Initial Thoughts

### Potential Approaches

1. **Antipodal pairing / involution count**: Define the involution $x \mapsto (a - x) \bmod a$
   on residues mod $a$. The obstruction says $R_a$ contains at most one point from each
   $\{x, a-x\}$ orbit. Bound $|R_a|$ by the number of orbits $= \lceil a/2 \rceil$ (fixed
   points $0$ and $a/2$ handled separately).
   - Why it might work: it is exactly the structure the parent already proved.
   - Risk: edge cases at the fixed points $x=0$ and (for even $a$) $x = a/2$.

### Key Difficulties

- Careful `Finset` bookkeeping of the involution and its fixed points in Lean.
- Choosing the cleanest statement (residue-set cardinality vs. counting elements).

### What Would a Proof Need?

- Key lemma: an involution on `Finset (ZMod a)` such that no two co-selected points are
  antipodal has image of size $\le \lceil a/2 \rceil$.
- Reuse of the parent's antipodal-obstruction lemma as the hypothesis.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Pure finite combinatorics on top of an already-verified obstruction lemma.
- Involution-counting arguments are well supported in Mathlib (`Finset`, `ZMod`).
- No analytic machinery required for this first step.

**Estimated Effort**:
- Exploration: hours
- If tractable: days

## References

### Papers
- P. Erdős, "Note on sequences of integers no one of which is divisible by any other" (1935).

### Mathlib
- `ZMod`, `Finset.card`, involution lemmas — residue counting.

## Metadata

```yaml
tags:
  - number-theory
  - density
  - divisibility-free-sets
  - residues
  - erdos
related_proofs:
  - erdos-12-wip-01
difficulty: medium
source: proof-suggestion
created: 2026-07-02
```

**Significance**: 5/10
**Tractability**: 6/10
