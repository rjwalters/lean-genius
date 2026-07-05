# Problem: Minimal Symmetric-Prime Offset Bounds for the Strong Goldbach Reformulation

**Slug**: strong-goldbach-symmetric-oq-03
**Created**: 2026-07-04
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
\forall\, m \ge 2,\ \exists\, k \in \{0, 1, \dots, m-2\} \ \text{such that}\ (m-k)\ \text{and}\ (m+k)\ \text{are both prime.}
$$

Define the *minimal symmetric offset* $k_{\min}(m) = \min\{\,k \ge 0 : m-k,\ m+k \text{ both prime}\,\}$. The question concerns the growth and extremal behavior of $k_{\min}(m)$.

### Plain Language

Every even number $n = 2m$ can (conjecturally) be written as a sum of two primes $p + q$. Writing $p = m-k$, $q = m+k$ makes the pair *symmetric* about $m$, with offset $k$. We ask: how small can we always guarantee the offset to be, and is there an even $n$ whose *only* symmetric prime decomposition uses an offset $k$ that is close to the maximum $m$ (i.e. one prime near $2m$ and the other near $0$)?

### Why This Matters

The offset $k_{\min}(m)$ is a fine-grained refinement of the strong Goldbach conjecture: bounding it uniformly is strictly stronger than Goldbach itself, and its extremal values are governed by the distribution of primes in short intervals around $m$ and by prime gaps. Even conditional/heuristic bounds connect Goldbach to the Hardy–Littlewood circle-method asymptotics for the number of representations.

## Known Results

### What's Already Proven

- Strong Goldbach verified computationally up to $4 \times 10^{18}$ (Oliveira e Silva et al.) — bounds $k_{\min}(m)$ empirically.
- Hardy–Littlewood conjectural asymptotic $r(2m) \sim 2 C_2 \prod_{p \mid m} \frac{p-1}{p-2} \frac{2m}{(\log 2m)^2}$ for the number of Goldbach representations — parent gallery entry `strong-goldbach-symmetric`.
- Prime-gap results (Zhang, Maynard–Tao bounded gaps) constrain how sparse primes near $m$ can be.

### What's Still Open

- Any unconditional uniform upper bound on $k_{\min}(m)$ (would imply Goldbach).
- Whether there exist $m$ with $k_{\min}(m) \gg m^{1/2}$ or larger.
- The precise relationship between $k_{\min}(m)$ and the maximal prime gap near $m$.

### Our Goal

Formalize the reformulation and its equivalence to strong Goldbach in Lean, define $k_{\min}$, and prove the elementary structural facts: (i) existence of *some* symmetric pair is equivalent to Goldbach for $2m$; (ii) an explicit finite decision procedure for $k_{\min}(m)$ on any given $m$; (iii) a conditional bound $k_{\min}(m) \le g(m)$ in terms of the prime-counting function in short intervals.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| strong-goldbach-symmetric | Parent entry; symmetric reformulation of Goldbach | reformulation, prime pairs |
| infinitude-of-primes | Prime existence infrastructure | Euclid / Mathlib `Nat.Prime` |
| bertrand-postulate | Primes in intervals $[m, 2m]$ | interval prime bounds |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Elementary equivalence + decidable finite search**: Prove `symmetric pair exists ↔ Goldbach for 2m`, then implement $k_{\min}$ as `Nat.find` over a decidable predicate. Bounds follow from `Nat.Prime` decidability.
   - Why it might work: purely elementary, strong Mathlib `Nat.Prime` support.
   - Risk: the *bound* on $k_{\min}$ is the hard, genuinely open part.

2. **Approach B — Conditional bound from prime-gap hypotheses**: Assume a short-interval prime hypothesis (e.g. a prime in every $[m - m^\theta, m]$) and derive $k_{\min}(m) \le m^\theta$.
   - Why it might work: reduces to an established (if conjectural) analytic input, cleanly axiomatized.
   - Risk: must state the hypothesis honestly as an assumption; result is `axiomatized`.

### Key Difficulties

- The uniform bound is equivalent to (an aspect of) Goldbach — unconditionally open.
- Connecting $k_{\min}$ to prime gaps requires short-interval prime distribution not in Mathlib.

### What Would a Proof Need?

- Key lemma 1: `(∃ k, Nat.Prime (m-k) ∧ Nat.Prime (m+k)) ↔ ∃ p q, p.Prime ∧ q.Prime ∧ p + q = 2*m`.
- Key lemma 2: decidability of the symmetric-pair predicate → `kMin` well-defined via `Nat.find`.
- Technical requirements: `Mathlib.NumberTheory.Primorial`, `Nat.Prime` decidability, optionally Bertrand's postulate (`Nat.exists_prime_lt_and_le_two_mul`).

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The equivalence and decidable-search parts are elementary and fully formalizable now.
- The extremal/bound part is open; scope should target the structural theorems + a clearly axiomatized conditional bound.
- Mathlib's `Nat.Prime` and Bertrand infrastructure directly support the tractable core.

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable (structural core): 3–5 days
- If hard (unconditional bounds): unknown / open

## References

### Papers
- Hardy & Littlewood, "Some problems of 'Partitio Numerorum' III", 1923 — representation asymptotics.
- Oliveira e Silva, Herzog, Pardi, "Empirical verification of the even Goldbach conjecture...", 2014 — computational bounds.

### Online Resources
- OEIS A002375 (number of Goldbach representations) — empirical offset data.

### Mathlib
- `Mathlib.NumberTheory.Bertrand` — a prime in $(m, 2m]$.
- `Mathlib.Data.Nat.Prime.Basic` — decidable primality, `Nat.find`.

## Metadata

```yaml
tags:
  - number-theory
  - goldbach
  - prime-gaps
related_proofs:
  - strong-goldbach-symmetric
  - bertrand-postulate
difficulty: medium
source: proof-suggestion
created: 2026-07-04
```

**Significance**: 6/10
**Tractability**: 6/10
