# Problem: Deficiency Gap of a Prime Power — Exact Closed Form and Abundancy Asymptotics

**Slug**: perfect-numbers-oq-05-oq-01
**Created**: 2026-07-01T22:11:22-07:00
**Status**: Active
**Source**: gallery-gap <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

### Formal Statement

Let $p$ be prime and $k \ge 0$. Define the deficiency gap of the prime power $p^k$ by
$$
D(p^k) \;:=\; 2p^k - \sigma(p^k),
$$
where $\sigma(p^k) = \sum_{j=0}^{k} p^j = \dfrac{p^{k+1}-1}{p-1}$ is the sum of divisors. We seek an exact closed form for the gap and its asymptotic behavior.

**Exact gap identity.** Writing $\sigma(p^k) = \left(\sum_{j=0}^{k-1} p^j\right) + p^k = \dfrac{p^k - 1}{p-1} + p^k$, the gap is exactly the *complement* of the lower geometric tail:
$$
D(p^k) \;=\; 2p^k - \sigma(p^k) \;=\; p^k - \sum_{j=0}^{k-1} p^j \;=\; p^k - \frac{p^k - 1}{p-1}.
$$
For $p = 2$ this collapses to $D(2^k) = 2^k - (2^k - 1) = 1$ (constant), and for $p \ge 3$ it grows:
$$
D(p^k) \;=\; p^k\!\left(1 - \frac{1 - p^{-k}}{p-1}\right) \;=\; p^k \cdot \frac{(p-2) + p^{-k}}{p-1} \;\sim\; p^k \cdot \frac{p-2}{p-1}.
$$

**Abundancy limit.** The abundancy index $A(p^k) := \sigma(p^k)/p^k$ satisfies, in $\mathbb{Q}$ (or $\mathbb{R}$),
$$
A(p^k) \;=\; \frac{\sigma(p^k)}{p^k} \;=\; 1 + \frac{1}{p} + \cdots + \frac{1}{p^k} \;=\; \frac{p - p^{-k}}{p-1} \;\xrightarrow[k \to \infty]{}\; \frac{p}{p-1} \;<\; 2 \quad (p \ge 2).
$$
The two targets are (i) the integer identity $D(p^k) = p^k - \frac{p^k-1}{p-1}$ (equivalently $2p^k - \sigma(p^k) = p^k - \sum_{j<k}p^j$), proved in $\mathbb{N}$; and (ii) the real/rational limit `Filter.Tendsto (fun k => (σ(p^k) : ℝ)/p^k) atTop (𝓝 (p/(p-1)))`.

### Plain Language

A prime power $p^k$ is always *deficient*: the sum of its divisors falls short of $2p^k$, so it can never be a perfect number. This problem asks precisely *how far short* it falls. The parent proof shows only that the gap is positive; here we pin down its exact size, $2p^k - \sigma(p^k) = p^k - (1 + p + \cdots + p^{k-1})$, and describe how it behaves as the prime or the exponent grows. For $p = 2$ the gap is always exactly $1$ (powers of two are only *just* deficient), but for larger primes the gap blows up like $p^k \cdot \frac{p-2}{p-1}$. Equivalently, the "abundancy" $\sigma(p^k)/p^k$ — the divisor sum measured in units of $p^k$ — climbs toward a hard ceiling of $p/(p-1)$ that it never reaches.

### Why This Matters

This is a quantitative refinement of the parent's qualitative deficiency inequality: instead of "$\sigma(p^k) < 2p^k$" we get the exact shortfall and its growth law. The abundancy index $\sigma(n)/n$ is the central object of the theory of perfect, abundant, and multiply-perfect numbers, and because $\sigma$ is multiplicative, $\sigma(n)/n = \prod_i \sigma(p_i^{a_i})/p_i^{a_i}$ factors over prime powers. The per-prime-power bound $\sigma(p^k)/p^k < p/(p-1)$ is exactly the input to the classical estimates behind odd-perfect-number constraints (e.g. $\prod_{p \mid n} p/(p-1) > 2$ forces $n$ to have enough distinct small prime factors) and to abundancy-index arguments for multiply-perfect and amicable numbers. Making both the exact gap and the sharp limit available as Lean theorems supplies a reusable building block for that entire multiplicative analysis.

## Known Results

### What's Already Proven

- **Parent inequality $\sigma(p^k) < 2p^k$** — `perfect-numbers-oq-05` (`Proofs/PerfectNumbersOQ05.lean`, `sigma_one_prime_pow_lt` / `prime_pow_is_deficient`), via the geometric bound `Nat.geomSum_lt` that $\sum_{j<k} p^j < p^k$.
- **Closed form $\sigma(p^k) = \sum_{j=0}^{k} p^j$ and geometric-sum evaluation** — Mathlib `ArithmeticFunction.sigma_one_apply_prime_pow`, `Finset.geom_sum_eq` (giving $(p^{k+1}-1)/(p-1)$ in a field), `Nat.geomSum_eq`.
- **Multiplicativity of $\sigma$** — Mathlib `ArithmeticFunction.isMultiplicative_sigma`, so abundancy factors over prime powers; `Nat.sigma_one_eq_sigmaOne` links `Nat.sigma 1` to the arithmetic function.
- **Geometric-series limits** — Mathlib `tendsto_pow_atTop_nhds_zero_of_lt_one` (for $p^{-k} \to 0$ when $0 < 1/p < 1$) and `hasSum_geometric_of_lt_one`, giving $\sum 1/p^j = p/(p-1)$.

### What's Still Open

- No Lean theorem states the **exact deficiency gap** $2p^k - \sigma(p^k) = p^k - \frac{p^k - 1}{p-1}$ (integer form) as a standalone identity.
- No Lean theorem gives the **abundancy limit** as a `Filter.Tendsto`: $\sigma(p^k)/p^k \to p/(p-1)$ in $\mathbb{R}$, nor the growth law $D(p^k) \sim p^k (p-2)/(p-1)$ for $p \ge 3$.
- The special-case collapse $D(2^k) = 1$ (constant gap for powers of two) is not separately recorded.

### Our Goal

Formalize, for prime $p$ and all $k$: (1) the exact integer gap identity $2p^k - \sigma(p^k) = p^k - \sum_{j<k} p^j = p^k - \frac{p^k-1}{p-1}$; (2) the constant-gap corollary $D(2^k) = 1$; and (3) the real-valued abundancy limit `Tendsto (fun k => (σ(p^k):ℝ)/p^k) atTop (𝓝 (p/(p-1)))`, with the strict bound $p/(p-1) < 2$ for $p \ge 2$ tying back to the parent's deficiency statement.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| perfect-numbers-oq-05 | Direct parent: proves $\sigma(p^k) < 2p^k$ via $\sum_{j<k}p^j < p^k$; we quantify the exact gap it leaves open | `Nat.geomSum_lt`, `sigma_one_apply_prime_pow`, `Finset.sum_range_succ` |
| perfect-numbers | Euclid–Euler even-perfect characterization; abundancy factors over prime powers, our per-prime-power bound feeds it | multiplicativity of $\sigma$, Mersenne primes |
| harmonic-divergence | Companion analytic limit: $\sum 1/p^j$ is a convergent geometric series (contrast with the divergent harmonic sum) | geometric vs harmonic series, `Filter.Tendsto` |

## Initial Thoughts

### Potential Approaches

1. **Approach A (algebraic, integer gap)**: Expand $\sigma(p^k) = \sum_{j \in \text{range}(k+1)} p^j$ via `sigma_one_apply_prime_pow`, peel the top term with `Finset.sum_range_succ` to write $\sigma(p^k) = \left(\sum_{j<k} p^j\right) + p^k$, then $2p^k - \sigma(p^k) = p^k - \sum_{j<k} p^j$ follows by `omega` (using $\sum_{j<k}p^j < p^k$ from the parent to keep $\mathbb{N}$-subtraction well-behaved). Convert $\sum_{j<k} p^j$ to $\frac{p^k-1}{p-1}$ via `Nat.geomSum_eq` (needs $2 \le p$).
   - Why it might work: it is exactly the parent's decomposition, reused; every lemma already exists in Mathlib.
   - Risk: $\mathbb{N}$-subtraction; the identity $p^k - \frac{p^k-1}{p-1}$ uses truncated division, so it is cleanest to prove the subtraction-free form $\sigma(p^k) + D = 2p^k$ and $\sigma(p^k) + p^k = 2p^k \wedge \dots$, or state the division version over $\mathbb{Q}$.

2. **Approach B (analytic, abundancy limit)**: Work in $\mathbb{R}$. Write $\sigma(p^k)/p^k = \sum_{j=0}^{k} p^{-j} = \frac{1 - p^{-(k+1)}}{1 - p^{-1}}$ via `Finset.geom_sum_eq` / `geom_series`, then take $k \to \infty$ using `tendsto_pow_atTop_nhds_zero_of_lt_one` on $p^{-(k+1)}$ to get the limit $\frac{1}{1-p^{-1}} = \frac{p}{p-1}$. Alternatively use `hasSum_geometric_of_lt_one` directly and `HasSum.tendsto_sum_nat`.
   - Why it might work: standard geometric-series limit; the ratio $1/p \in (0,1)$ for $p \ge 2$.
   - Risk: casting $\sigma(p^k)$ (a `Nat`) to $\mathbb{R}$ and matching it to the real geometric partial sum; index bookkeeping (range $k+1$ vs the tail term $p^{-(k+1)}$).

### Key Difficulties

- **$\mathbb{N}$ subtraction vs $\mathbb{Q}/\mathbb{R}$**: The integer gap $2p^k - \sigma(p^k)$ is a truncated subtraction; safest to prove the additive form and derive subtraction with `omega` under the parent's strict inequality. The division form $\frac{p^k-1}{p-1}$ is exact in $\mathbb{N}$ only because $(p-1) \mid (p^k-1)$ (`Nat.sub_one_dvd_sub_of_dvd_sub` / geometric factorization), so a $\mathbb{Q}$ statement is cleaner for the limit.
- **Integer vs real formulation**: The exact gap is naturally integer; the abundancy limit is naturally real. Bridging requires a cast lemma relating `(∑ p^j : ℕ) : ℝ` to `∑ (p:ℝ)^j` (`Nat.cast_sum`, `push_cast`).

### What Would a Proof Need?

- Key lemma 1: $\sigma(p^k) = \left(\sum_{j<k} p^j\right) + p^k$ (peel top term) → gap $= p^k - \sum_{j<k} p^j$ by `omega`.
- Key lemma 2: $\sigma(p^k)/p^k = \sum_{j=0}^{k}(1/p)^j = \frac{1-(1/p)^{k+1}}{1-1/p}$ in $\mathbb{R}$ (`Finset.geom_sum_eq`).
- Technical requirements: `push_cast` to move between $\mathbb{N}$ and $\mathbb{R}$; `tendsto_pow_atTop_nhds_zero_of_lt_one` for $p^{-(k+1)} \to 0$; `Nat.geomSum_eq` for the integer closed form; the parent's `geomSum_prime_pow_lt` to control $\mathbb{N}$-subtraction.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The integer gap identity is essentially a rearrangement of the parent's own decomposition ($\sigma = $ lower tail $+ p^k$), closed by `omega`; low risk.
- The abundancy limit is a textbook geometric-series limit; Mathlib has every ingredient (`geom_sum_eq`, `tendsto_pow_atTop_nhds_zero_of_lt_one`, `hasSum_geometric_of_lt_one`).
- Similar analytic limits are already handled in the gallery (harmonic/geometric series entries), and the parent proof is 0-axiom and clean.
- Main cost is casting/index bookkeeping between $\mathbb{N}$ and $\mathbb{R}$, not deep mathematics.

**Estimated Effort**:
- Exploration: a few hours
- If tractable: 1–2 days
- If hard: unknown (only if `Filter.Tendsto` cast plumbing proves unexpectedly stubborn)

## References

### Papers
- Hardy, G. H. & Wright, E. M., *An Introduction to the Theory of Numbers* — the divisor function $\sigma$, the closed form $\sigma(p^k) = (p^{k+1}-1)/(p-1)$, and the abundancy index $\sigma(n)/n$.
- Nicomachus of Gerasa, *Introduction to Arithmetic* (c. 100 AD) — original deficient/perfect/abundant classification by comparing $n$ with its proper-divisor sum.

### Online Resources
- https://en.wikipedia.org/wiki/Divisor_function — abundancy index and the geometric-series formula for $\sigma$ on prime powers.
- https://en.wikipedia.org/wiki/Deficient_number — deficiency $2n - \sigma(n)$ and the classification.

### Mathlib
- `Nat.ArithmeticFunction.sigma` / `ArithmeticFunction.sigma_one_apply_prime_pow` — $\sigma_1(p^k) = \sum_{j\le k} p^j$.
- `Nat.sigma_one_eq_sigmaOne` — links `Nat.sigma 1` to the arithmetic-function `σ`.
- `Finset.geom_sum_eq` / `Nat.geomSum_eq` — closed form $\sum_{j<k} x^j = (x^k - 1)/(x - 1)$.
- `tendsto_pow_atTop_nhds_zero_of_lt_one` / `hasSum_geometric_of_lt_one` — geometric-series limit for the abundancy `Filter.Tendsto` to $p/(p-1)$.

## Metadata

```yaml
tags:
  - number-theory
  - perfect-numbers
  - divisor-sum
  - deficient-numbers
  - geometric-series
related_proofs:
  - perfect-numbers-oq-05
  - perfect-numbers
  - harmonic-divergence
difficulty: medium
source: gallery-gap
created: 2026-07-01T22:11:22-07:00
```

**Significance**: 5/10
**Tractability**: 7/10
