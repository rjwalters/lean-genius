# Problem: Completing the Lean Formalization of Erdős #227 (Maximum Term vs Maximum Modulus)

**Slug**: erdos-227-wip-01
**Created**: 2026-07-09T17:33:19-07:00
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
\text{For every } \lambda \in \Bigl[0, \tfrac{1}{2}\Bigr] \text{ there is an entire } f(z) = \sum_{n \ge 0} a_n z^n \text{ with } \lim_{r \to \infty} \frac{\mu(r)}{M(r)} = \lambda,
$$

where $\mu(r) = \max_{n} |a_n| r^n$ is the maximum term and $M(r) = \max_{|z| = r} |f(z)|$ is the maximum modulus; consequently the limit, when it exists, need **not** be $0$, and the sharp range of achievable values is $[0, \tfrac{1}{2}]$.

### Plain Language

We want to finish machine-checking a Lean 4 formalization of a solved Erdős problem in complex analysis. Erdős asked whether, for an entire function, the ratio of its largest power-series term $\mu(r)$ to its maximum modulus $M(r)$ must tend to $0$ whenever the limit exists. Clunie and Hayman (1964) disproved this by constructing entire functions realizing any prescribed limit $\lambda$ in $[0, 1/2]$, and $1/2$ is sharp. The gallery entry `erdos-227` states the Clunie–Hayman construction as an assumption and still contains one `sorry`; it derives `original_conjecture_false` from that assumption using $\lambda = 1/4$. Our goal is to eliminate the remaining `sorry`, prove the elementary facts about $\mu(r)$ and $M(r)$ (non-negativity, the trivial inequality $\mu(r) \le M(r)$) directly in Mathlib, and reduce the entry to a single clearly-stated Clunie–Hayman existence assumption.

### Why This Matters

1. **Removing the last sorry**: The entry has `sorries: 1` and badge `wip`; discharging that sorry and formalizing the supporting inequalities moves the formalization toward a defensible verified core with one named assumption.
2. **Foundational entire-function API**: Formalizing $\mu(r) \le M(r)$ and the non-negativity/monotonicity of maximum term and maximum modulus yields reusable Lean definitions for power-series growth theory, currently thin in Mathlib.
3. **Honest counterexample encoding**: Cleanly isolating the Clunie–Hayman construction as one existence assumption makes precise exactly what deep input is imported, distinguishing the trivially-true inequality $\mu \le M$ from the nontrivial disproof of the original conjecture.

## Known Results

### What's Already Proven

- The elementary bound $\mu(r) \le M(r)$ for every entire function — classical, provable from Cauchy's coefficient estimates.
- Clunie and Hayman's construction of entire functions with $\lim_{r\to\infty}\mu(r)/M(r) = \lambda$ for any prescribed $\lambda \in [0, 1/2]$ — Clunie, Hayman (1964).
- Sharpness of the upper endpoint: the limit can never exceed $1/2$ — Clunie, Hayman (1964).
- The gallery theorem `original_conjecture_false`, derived from the Clunie–Hayman assumption using $\lambda = 1/4$.

### What's Still Open

- The precise analytic structure of extremal entire functions achieving the endpoint $\lambda = 1/2$.
- Whether the characterization extends to meromorphic functions with the Nevanlinna characteristic $T(r)$ replacing $M(r)$.
- For functions of finite positive order $\rho > 0$, the exact set of achievable $\liminf$ and $\limsup$ values of $\mu(r)/M(r)$.

### Our Goal

Complete `Proofs/Erdos227Problem.lean` by (i) discharging the single remaining `sorry`, ideally by formally proving the non-negativity of `maxTerm` and `maxModulus` and the trivial inequality $\mu(r) \le M(r)$; (ii) tightening the `EntireFunction` structure and the definitions of $\mu(r)$ and $M(r)$ so they are well-typed suprema over non-negative reals; and (iii) retaining the Clunie–Hayman existence statement as one explicit assumption, disclosed in `meta.json`, from which `original_conjecture_false` follows. The aim is a sorry-free file whose only nontrivial input is the Clunie–Hayman construction.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| erdos-227 | Direct parent entry; supplies the `EntireFunction` structure, `maxTerm`/`maxModulus` definitions, and the Clunie–Hayman assumption to be tightened | Power series, suprema over $\mathbb{R}$, filter limits (`Tendsto`) |
| erdos-116 | Companion complex-analysis Erdős entry where sharp bounds are stated but the deep theorem stays axiomatized, same formalization pattern | Complex modulus, extremal estimates, analytic bounds |

## Initial Thoughts

### Potential Approaches

1. **Approach A**: Discharge the sorry by proving the elementary inequalities $0 \le \mu(r) \le M(r)$ from Mathlib's supremum and Cauchy-estimate lemmas.
   - Why it might work: $\mu(r)$ and $M(r)$ are suprema of non-negative quantities, so `Real.iSup_nonneg` gives non-negativity; the term-by-term bound $|a_n| r^n \le M(r)$ follows from Cauchy's inequality, giving $\mu(r) \le M(r)$.
   - Risk: Mathlib may lack a directly applicable Cauchy coefficient-estimate lemma in the exact form needed, forcing an auxiliary derivation.

2. **Approach B**: Restructure so the whole entry reduces to a single Clunie–Hayman existence axiom plus purely definitional lemmas, and derive `original_conjecture_false` with $\lambda = 1/4$.
   - Why it might work: Concentrating all deep content into one assumption maximizes the sorry-free/verified surface and makes the disclosed assumption minimal and auditable.
   - Risk: Formalizing the statement of the construction (existence of $f$ with a prescribed limit) requires care with the `Tendsto` limit encoding to keep it faithful.

### Key Difficulties

- The Clunie–Hayman construction is a genuine research-level analytic result with no realistic path to full Lean formalization; it must remain an assumption.
- Establishing $\mu(r) \le M(r)$ formally depends on Cauchy coefficient estimates whose Mathlib availability must be verified.

### What Would a Proof Need?

- Key lemma 1: `maxTerm r ≥ 0` and `maxModulus r ≥ 0` via non-negativity of suprema of non-negative reals.
- Key lemma 2: The trivial inequality $\mu(r) \le M(r)$ from Cauchy's coefficient bound.
- Technical requirements: A faithful `Tendsto` encoding of "$\mu(r)/M(r) \to \lambda$" and a single disclosed Clunie–Hayman existence assumption for $\lambda \in [0, 1/2]$.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The remaining work is a single `sorry` plus a handful of elementary inequalities about suprema of non-negative reals, which Mathlib supports well (`Real.iSup_nonneg`, `ge_of_tendsto`).
- Similar entire-function bookkeeping (non-negativity, limit lower bounds) already appears in the file's declared Mathlib dependencies, indicating the pieces are within reach.
- The only deep content, the Clunie–Hayman construction, is deliberately kept as an assumption, so the tractable portion is genuinely finite.

**Estimated Effort**:
- Exploration: 1–2 days to locate the right Cauchy-estimate and supremum lemmas.
- If tractable: 3–7 days to remove the sorry and prove the supporting inequalities.
- If hard: the Clunie–Hayman construction remains a permanent assumption.

## References

### Papers
- Clunie, Hayman, "The maximum term of a power series" (1964) — construction achieving any $\lambda \in [0, 1/2]$ and sharpness.
- Erdős, correspondence/problem list — original question whether the limit must be $0$.
- Hayman, "The local growth of power series: a survey of the Wiman–Valiron method" — background on $\mu(r)$ vs $M(r)$.

### Online Resources
- https://erdosproblems.com/227 — problem statement and status.

### Mathlib
- Mathlib.Data.Real.Archimedean — `Real.iSup_nonneg` for non-negativity of suprema.
- Mathlib.Topology.Order.OrderClosed — `ge_of_tendsto` to lift eventual bounds through limits.
- Mathlib.Analysis.Complex.Basic — complex norm $\|\cdot\|$ replacing the removed `Complex.abs`.

## Metadata

```yaml
tags:
  - complex-analysis
  - entire-functions
  - power-series
  - maximum-modulus
  - counterexample
  - formalization
related_proofs:
  - erdos-227
  - erdos-116
difficulty: medium
source: proof-suggestion
created: 2026-07-09T17:33:19-07:00
```

**Significance**: 6/10
**Tractability**: 7/10
