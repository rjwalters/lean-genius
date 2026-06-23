# Problem: Tighten Chebyshev's Prime Counting Constants to 0.921 and 1.106

**Slug**: chebyshev-pnt-bridge-oq-01
**Created**: 2026-04-21T05:55:03-07:00
**Status**: Active
**Source**: proof-suggestion

## Problem Statement

### Formal Statement

$$
0.921 \leq \liminf_{x \to \infty} \frac{\pi(x) \log x}{x} \leq \limsup_{x \to \infty} \frac{\pi(x) \log x}{x} \leq 1.106
$$

Or equivalently, using Chebyshev's theta function $\theta(x) = \sum_{p \leq x} \log p$:

$$
0.921 \cdot x \leq \theta(x) \leq 1.106 \cdot x \quad \text{for all sufficiently large } x
$$

### Plain Language

The existing `ChebyshevPNTBridge.lean` proof establishes that $\log 2 \leq \liminf \pi(x)\log(x)/x \leq \limsup \leq 2\log 4$, i.e., constants approximately $0.693$ and $1.386$. Chebyshev's 1852 paper gave tighter bounds: $0.921$ and $1.106$. The goal is to formalize these sharper constants in Lean 4.

### Why This Matters

Chebyshev's 0.921/1.106 bounds are the historically important result — they were the first rigorous proof that $\pi(x) \sim x/\log x$ to within a constant factor. Tightening from $(\log 2, 2\log 4) \approx (0.693, 1.386)$ to $(0.921, 1.106)$ completes the historical formalization and brings the Lean proof in line with the classical mathematical literature.

## Known Results

### What's Already Proven

- `pow_sqrt_primeCounting_le`: $(√n)^{\pi(n)-\pi(√n)} \leq 4^n$ — `ChebyshevPNTBridge.lean`
- `primeCounting_lower_bound`: $4^n \leq (2n+1)(2n)^{\pi(2n)}$ — `ChebyshevPNTBridge.lean`
- Together give: $\log 2 \leq \liminf \pi(x)\log(x)/x \leq \limsup \leq 2\log 4$
- `Nat.primorial_le`: $\text{primorial}(n) \leq 4^n$ — Mathlib

### What's Still Open

- Tighten lower constant from $\log 2 \approx 0.693$ to $0.921$
- Tighten upper constant from $2\log 4 \approx 1.386$ to $1.106$

### Our Goal

Formalize Chebyshev's sharper argument. The key idea uses products over multiple intervals and binomial coefficient estimates with better constants than the central binomial bound.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `chebyshev-pnt-bridge` | Parent proof with weaker constants | Primorial bounds, $\binom{2n}{n} \leq 4^n$ |
| `chebyshev-bounds` | Elementary Chebyshev bounds | Parity arguments, log estimates |
| `infinitude-primes-4k1` | Related PNT-style reasoning | Dirichlet characters |

## Initial Thoughts

### Potential Approaches

1. **Multi-interval binomial approach**: Chebyshev's original argument uses the product $\binom{2n}{n}\binom{2n-1}{n}\cdots$ over multiple intervals to get tighter constants. Key: $\binom{30}{14} \cdot \binom{30}{6} \cdot \ldots$ gives constants closer to 0.921.
   - Why it might work: Follows Chebyshev's 1852 paper directly; the argument is combinatorial
   - Risk: Requires careful tracking of many intermediate estimates; may be tedious to formalize

2. **Theta function approach**: Work with $\theta(x) = \sum_{p \leq x} \log p$ directly, proving $0.921x \leq \theta(x) \leq 1.106x$ via the identity $\theta(x) = \sum_p \lfloor \log_p x \rfloor \cdot \log p - \psi(x)$ corrections.
   - Why it might work: Cleaner to state bounds on $\theta$ than on $\pi$
   - Risk: Mathlib's `Nat.von_mangoldt` infrastructure may be sparse

3. **Sorry-stub approach**: State the sharp bound as a theorem with `sorry` and focus on whether the infrastructure exists.
   - Why it might work: Quick way to test feasibility
   - Risk: Not a complete proof

### Key Difficulties

- Chebyshev's original proof uses the product $N = \binom{2n}{n}\binom{2n-1}{n-1}\binom{3n}{n}\binom{4n}{n}$ which requires evaluating specific binomial combinations
- The constants $0.921$ and $1.106$ come from $\log(2^1 \cdot 3^{1/2} \cdot 5^{1/5} \cdot 30^{1/30})$ — a specific product formula
- Real-number analysis of limits in Lean 4 requires careful `Filter.Tendsto` / `limsup`/`liminf` setup

### What Would a Proof Need?

- Key lemma: Product of consecutive binomial coefficients gives tighter primorial bound
- Key lemma: $\theta(x)/x$ satisfies explicit bounds via the multi-product argument
- Technical: Mathlib's `Real.log`, `Filter.limsup`, `Nat.primorial` all need to interact cleanly

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The mathematical argument is classical and well-understood (Chebyshev 1852)
- Mathlib already has primorial, prime counting, and central binomial coefficient tools
- The main challenge is careful real-number arithmetic to track the specific constants 0.921 and 1.106
- Similar level of difficulty to formalizing Mertens' theorem bounds

**Estimated Effort**:
- Exploration: 1-2 days (read Chebyshev's original argument, identify Mathlib gaps)
- If tractable: 1-2 weeks (careful formalization of multi-interval estimates)
- If hard: Fall back to axiomatized version with explicit constant statements

## References

### Papers
- Chebyshev, P.L. (1852) "Mémoire sur les nombres premiers" — original proof with 0.921/1.106
- Erdős, P. (1949) "On a new method in elementary number theory" — simplified version

### Mathlib
- `Mathlib.NumberTheory.Primorial` — primorial and its bounds
- `Mathlib.NumberTheory.PrimeCounting` — $\pi(x)$ function
- `Mathlib.Data.Nat.Choose.Central` — $\binom{2n}{n}$ bounds

## Metadata

```yaml
tags:
  - number-theory
  - prime-counting
  - chebyshev-bounds
  - pnt
related_proofs:
  - chebyshev-pnt-bridge
  - chebyshev-bounds
  - infinitude-primes-4k1
difficulty: medium
source: proof-suggestion
created: 2026-04-21T05:55:03-07:00
```

**Significance**: 7/10
**Tractability**: 7/10
