# Problem: Erdős #476 — Structure of Cauchy-Davenport Extremal Sets

**Slug**: erdos-476-oq-05
**Created**: 2026-04-21T20:38:05+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Let $p$ be a prime and $A, B \subseteq \mathbb{Z}/p\mathbb{Z}$ with $|A| + |B| \leq p + 1$. If
$$|A + B| = |A| + |B| - 1$$
(equality in Cauchy-Davenport), then $A$ and $B$ are arithmetic progressions with the **same common difference**.

### Plain Language

The Cauchy-Davenport theorem gives a lower bound $|A+B| \geq \min(p, |A|+|B|-1)$. When does equality hold? The answer (Freiman's theorem for $\mathbb{Z}/p\mathbb{Z}$, or the equality case of Cauchy-Davenport) is that $A$ and $B$ must both be arithmetic progressions sharing the same common difference — i.e., $A = a + d \cdot [k]$ and $B = b + d \cdot [l]$ for the same $d$.

### Why This Matters

The structure theorem for Cauchy-Davenport extremizers is a cornerstone of **additive combinatorics** (Freiman-Ruzsa theory). It characterizes when sumsets are "as small as possible" — a key tool in:
- Szemerédi's theorem and its relatives
- Freiman's theorem ($|A+A| \leq K|A|$ implies $A$ is contained in a GAP)
- Cryptographic applications (small sumsets in groups)

## Known Results

### What's Already Proven

- `erdos-476`: The Cauchy-Davenport lower bound $|A+B| \geq \min(p, |A|+|B|-1)$ for $\mathbb{Z}/p\mathbb{Z}$. (verified)

### What's Still Open

- The **equality case characterization**: when $|A+B| = |A|+|B|-1$.
- Freiman's full structure theorem for $\mathbb{Z}/p\mathbb{Z}$.

### Our Goal

Prove the equality characterization: if $|A+B| = |A|+|B|-1$ in $\mathbb{Z}/p\mathbb{Z}$, then $A$ and $B$ are APs with the same common difference.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `erdos-476` | Cauchy-Davenport lower bound | Polynomial method or compression |
| `erdos-35` | Additive combinatorics problems | Sidon sets |
| `erdos-268` | Harmonic density | Sumset density |

## Initial Thoughts

### Potential Approaches

1. **Vosper's theorem**: The equality case of Cauchy-Davenport is classical (Vosper 1956). Lean proof: use the proof of Vosper's theorem directly.
   - Why it might work: Vosper's theorem is well-studied and the proof is clean.
   - Risk: May require significant setup around arithmetic progressions in $\mathbb{Z}/p\mathbb{Z}$.

2. **Compression argument**: The proof of Cauchy-Davenport via compression (shifting operation) naturally reveals extremal structure.
   - Why it might work: The compression proof is constructive and reveals the AP structure.
   - Risk: Formalizing the compression operators in Lean may be verbose.

3. **Polynomial method**: If the Cauchy-Davenport proof used the polynomial method (Alon's combinatorial Nullstellensatz), the equality case can be analyzed via the polynomial structure.

### Key Difficulties

- Need to define arithmetic progressions in $\mathbb{Z}/p\mathbb{Z}$ precisely.
- The equality case requires both $A$ and $B$ to be APs, which needs a careful inductive argument.
- Handling edge cases: $|A| = 1$ or $|B| = 1$.

### What Would a Proof Need?

- Definition: Arithmetic progression $a + d \cdot \{0, 1, \ldots, k-1\}$ in $\mathbb{Z}/p\mathbb{Z}$.
- Lemma (Vosper's theorem): Structure of extremizers.
- Induction: Strip off one element and use the inductive hypothesis.

## Tractability Assessment

**Difficulty**: Medium-High

**Justification**:
- The parent bound (Cauchy-Davenport) is already formalized, providing the infrastructure.
- Vosper's theorem has a clean proof but requires nontrivial combinatorial lemmas.
- Mathlib's `ZMod` infrastructure supports arithmetic in $\mathbb{Z}/p\mathbb{Z}$.

## References

### Papers
- Vosper, A.G. "The fraction of primes represented by sumsets," *Proc. London Math. Soc.* (1956).
- Nathanson, M. *Additive Number Theory*, Ch. 2.

### Mathlib
- `ZMod` — arithmetic in $\mathbb{Z}/p\mathbb{Z}$
- `Finset.card_add_le` — Cauchy-Davenport infrastructure
- `IsPrimeField` — prime field properties

## Metadata

```yaml
tags:
  - additive-combinatorics
  - erdos
  - cauchy-davenport
  - sumsets
  - vosper
related_proofs:
  - erdos-476
difficulty: medium-high
source: gallery-gap
created: 2026-04-21T20:38:05+02:00
```

**Significance**: 7/10
**Tractability**: 6/10
