# Problem: q-Vandermonde Identity via Gaussian Binomial Coefficients

## Statement

### Plain Language

Can the **q-Vandermonde identity**

$$
\sum_{k=0}^{r} q^{(m-k)(r-k)} \binom{m}{k}_q \binom{n}{r-k}_q = \binom{m+n}{r}_q
$$

be formalized using Mathlib's Gaussian binomial coefficient API? This slug **built** the API from first principles (Mathlib v4.26.0 has no `GaussianBinomial`), **proved** the $m=0$ / $n=0$ base cases of q-Vandermonde, the closed form at $k=1$ via the geometric sum, and the reflection symmetry $\binom{n+1}{1}_q = \binom{n+1}{n}_q$, and **graduated** to `verified-original` status (0 sorries, 0 axioms, 297 LOC). The full inductive q-Vandermonde proof remains future work; see `state.md` § Next Action.

### Formal Statement

$$
\sum_{k=0}^{r} q^{(m-k)(r-k)} \binom{m}{k}_q \binom{n}{r-k}_q = \binom{m+n}{r}_q
$$

where $\binom{n}{k}_q$ is the **Gaussian (q-)binomial coefficient**:

$$
\binom{n}{k}_q := \frac{[n]_q!}{[k]_q! \, [n-k]_q!}, \qquad [k]_q! := \prod_{i=1}^{k} (1 + q + q^2 + \cdots + q^{i-1})
$$

equivalently characterized by the **q-Pascal recurrence** (the definition used in this slug):

$$
\binom{n+1}{k+1}_q = q^{k+1} \binom{n}{k+1}_q + \binom{n}{k}_q, \qquad \binom{n}{0}_q = 1, \quad \binom{0}{k+1}_q = 0.
$$

## Classification

```yaml
tier: B
significance: 6
tractability: 5
status: verified
badge: original
slugStatus: graduated
tags:
  - combinatorics
  - q-analogs
  - gaussian-binomial
  - q-vandermonde
  - extension
  - seeker-selected
  - research
```

**Significance**: 6/10 — q-deformations of classical combinatorial identities are central to combinatorics, representation theory, and quantum groups. The q-Vandermonde specializes to classical Vandermonde at $q=1$ and to the binomial theorem at $r=m$.

**Tractability**: 5/10 — The Gaussian binomial API was missing from Mathlib v4.26.0; building it from first principles (without polynomial-quotient or rational-function machinery, just `CommSemiring` + q-Pascal recurrence) is moderately involved. The inductive step of the full identity remains open (re-indexing the convolution sum with $q^{(m-k)(r-k)}$ weights is non-trivial).

**Slug Status**: graduated — verified-original, 13 theorems + 1 def, 0 sorries, 0 axioms, 297 LOC. Two PRs merged: #16707 (q-Vandermonde m=0 / n=0 base cases) and #16779 (k=1 closed form + reflection).

## Why This Matters

1. **Subspace-counting interpretation** — $\binom{n}{k}_q$ counts $k$-dimensional subspaces of an $n$-dimensional vector space over $\mathbb{F}_q$ (when $q$ is a prime power). The q-Vandermonde identity counts pairs $(V, W)$ with $V \subseteq W$ in two ways: directly (LHS) and via fixed-dimension partitions (RHS).
2. **Specializes to classical Vandermonde** — At $q = 1$, $\binom{n}{k}_q = \binom{n}{k}$ and the q-Vandermonde becomes the classical Vandermonde $\sum_k \binom{m}{k}\binom{n}{r-k} = \binom{m+n}{r}$.
3. **Bridges combinatorics and quantum groups** — q-Pascal, q-Vandermonde, and the related q-binomial theorem are the entry points to the combinatorial side of quantum group representation theory ($U_q(\mathfrak{sl}_2)$ and beyond).
4. **Provides the missing GaussianBinomial scaffolding** — At Mathlib v4.26.0, this slug's API (q-Pascal recurrence, vanishing, diagonal, $q \to 1$ specialization, $k=1$ closed form) is the foundation any future upstream contribution would build on.

## Related Gallery Proofs

| Slug | Relationship | Description |
|------|--------------|-------------|
| [binomial-theorem-oq-02-oq-02](../../../src/data/proofs/binomial-theorem-oq-02-oq-02/) | extends | Parent: classical Vandermonde's identity. This entry develops the q-deformation of the binomial coefficients and proves the $m=0$ / $n=0$ base cases of the q-Vandermonde convolution; classical Vandermonde base cases recovered as the $q \to 1$ specialization. |
| [binomial-theorem-oq-02-oq-03](../../../src/data/proofs/binomial-theorem-oq-02-oq-03/) | related | q-Multinomial Coefficients and the q-Multinomial Theorem — higher-arity sibling. Both develop q-analogues of Pascal-style identities; q-Vandermonde is the 2-variable specialization of the q-multinomial convolution. |
| [binomial-theorem-oq-02](../../../src/data/proofs/binomial-theorem-oq-02/) | related | Multinomial theorem — classical ($q = 1$) underpinning of the convolution structure that q-Vandermonde generalizes. |

## Related Problems

- **Andrews, *q-Series* (1986)** — survey of q-analogues including q-Vandermonde, q-Saalschütz, q-Pfaff-Saalschütz, and the Rogers–Ramanujan identities.
- **Kac & Cheung, *Quantum Calculus* (2002)** — modern textbook on q-deformations of analysis and combinatorics; presents Gaussian binomials via the q-Pascal recurrence.
- **Bressoud, *Proofs and Confirmations* (1999)** — combinatorial proofs of q-identities via lattice paths and tilings.

## References

- **Lindsay N. Childs**, *A Concrete Introduction to Higher Algebra* (3rd ed., 2009), Springer. § Gaussian binomial coefficients.
- **George E. Andrews**, *The Theory of Partitions* (1976), Cambridge. § q-binomial coefficient identities.
- **Mathlib4 v4.26.0** — no `GaussianBinomial` namespace yet (verified via Grep at lake pin `2df2f0150c…`); the API in `proofs/Proofs/BinomialTheoremOQ02OQ02OQ01.lean` is original to this slug.

## OEIS Sequences

- [A008949](https://oeis.org/A008949) — Triangle of partial sums of Gaussian binomial coefficients $\binom{n}{k}_q$ evaluated at $q = 2$.
- [A015486](https://oeis.org/A015486) — Gaussian binomial coefficient $\binom{2n}{n}_2$ (subspaces of even-dimensional binary vector spaces).
