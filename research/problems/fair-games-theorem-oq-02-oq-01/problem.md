# Problem: Optional Stopping Theorem (Doob) Formalization via Mathlib

**Slug**: fair-games-theorem-oq-02-oq-01
**Created**: 2026-04-22T09:05:08+02:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Construct a simple symmetric random walk $(S_n)_{n \geq 0}$ with $S_0 = k$ as a Lean 4
`MeasureTheory.Martingale` and apply Doob's Optional Stopping Theorem to prove:

$$E[S_\tau] = k$$

where $\tau = \inf\{n : S_n \in \{0, N\}\}$ is the first hitting time of $\{0, N\}$.

### Plain Language

The fair-games-theorem gallery proof establishes the Optional Stopping Theorem (OST)
abstractly. This problem asks: **can we instantiate it with a concrete example?**

Specifically:
1. Build a simple symmetric random walk $S_n = k + X_1 + \cdots + X_n$ where each $X_i \in \{+1, -1\}$ with equal probability, as a `MeasureTheory.Martingale` against a suitable filtration.
2. Define the stopping time $\tau$ (hitting time of $\{0, N\}$) as a `MeasureTheory.IsStoppingTime`.
3. Apply `MeasureTheory.Martingale.stoppedValue_eq_expected` (or equivalent Mathlib lemma) to derive $E[S_\tau] = S_0 = k$.
4. Use this to recover the classical ruin probability $P(S_\tau = 0) = 1 - k/N$.

### Why This Matters

The abstract OST proof in the gallery is elegant but self-referential: it never instantiates
a concrete random process. This problem builds the bridge from abstract martingale theory
to classical probability examples. It is prerequisite infrastructure for:
- `fair-games-theorem-oq-02-oq-03`: Variance of ruin time (needs $E[M_\tau]$ for quartic martingale)
- `fair-games-theorem-oq-02-oq-04`: Biased Gambler's Ruin (needs $E[r^{S_\tau}]$ for geometric martingale)

## Known Results

### What's Already Proven

- `fair-games-theorem`: OST for bounded stopping times — `MeasureTheory.Martingale.stoppedValue_eq_expected` exists in Mathlib (0 sorries, 1 axiom for submartingale converse direction)
- `fair-games-theorem-oq-02`: $E[\tau] = k(N-k)$ and $P(\text{ruin}) = 1 - k/N$ (verified, 0 sorries)
- Mathlib has `MeasureTheory.Martingale`, `IsStoppingTime`, and `stoppedValue` for discrete-time processes

### What's Still Open

- No concrete simple random walk example in the gallery as a Lean `Martingale`
- Linking `ProbabilityTheory.iIndepFun` Bernoulli increments to the `Martingale` typeclass

### Our Goal

Produce a verified Lean 4 theorem of the form:

```lean
theorem simple_rw_expected_stopped_value
    (k N : ℕ) (hk : 0 < k) (hkN : k < N)
    (P : MeasureTheory.Measure (ℕ → Bool)) [IsProbabilityMeasure P] :
    -- random walk S_n with S_0 = k, steps ±1
    -- τ = hitting time of {0, N}
    E[S τ] = k
```

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `fair-games-theorem` | OST infrastructure | Submartingale sandwich, `stoppedValue_eq_expected` |
| `fair-games-theorem-oq-02` | Expected ruin time | Classical RW martingale $S_n$, $S_n^2 - n$ |
| `fair-games-theorem-oq-02-oq-03` | Variance (downstream) | Quartic martingale |

## Initial Thoughts

### Potential Approaches

1. **Bernoulli product space**: Construct $\Omega = \{+1, -1\}^\mathbb{N}$ with product measure, define $X_i(\omega) = \omega_i$, and set $S_n = k + \sum_{i=0}^{n-1} X_i$.
   - Why it might work: Mathlib has `ProbabilityTheory.iIndepFun` for product measures
   - Risk: Connecting `iIndepFun` structure to `Martingale` typeclass requires careful filtration setup

2. **Abstract martingale stance**: Define $S_n$ axiomatically as satisfying the martingale property without constructing the probability space explicitly.
   - Why it might work: Simpler to state; uses `Martingale` typeclass directly
   - Risk: Less foundationally satisfying; may not transfer to downstream applications

### Key Difficulties

- Building the canonical filtration $(\mathcal{F}_n)$ from the increments in Lean
- Proving the Markov/martingale property under the product measure
- `IsStoppingTime` verification for hitting times in Lean

### What Would a Proof Need?

- A product probability space for Bernoulli$(\frac{1}{2})$ increments
- `Filtration` defined by $\mathcal{F}_n = \sigma(X_0, \ldots, X_{n-1})$
- The martingale property: `E[S_{n+1} | ℱ_n] = S_n`
- Boundedness of `τ ∧ N` for applying Mathlib's bounded-stopping-time OST

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Mathlib has all required ingredients (`Martingale`, `IsStoppingTime`, `stoppedValue`, product measures)
- The construction is standard probability theory
- Main challenge is ergonomics: connecting Mathlib's abstract framework to a concrete product space
- Similar constructions exist in Mathlib for random walks in other contexts

**Estimated Effort**:
- Exploration: 1-2 days (survey Mathlib random walk / product space infrastructure)
- If tractable: 3-7 days (construction + martingale property + OST application)
- If hard: 2-4 weeks (if filtration/product space interface is rough)

## References

### Papers
- Doob, J.L. (1953) — *Stochastic Processes*, Chapter VII: Optional stopping theorem

### Mathlib
- `Mathlib.Probability.Martingale.OptionalStopping` — `stoppedValue_eq_expected`, bounded OST
- `Mathlib.Probability.Process.HittingTime` — `IsStoppingTime` for hitting times
- `Mathlib.Probability.Independence.Basic` — `iIndepFun` for product spaces
- `Mathlib.MeasureTheory.Measure.MeasureSpace` — product measures

## Metadata

```yaml
tags:
  - probability
  - martingale
  - optional-stopping
  - random-walk
  - gambler-ruin
related_proofs:
  - fair-games-theorem
  - fair-games-theorem-oq-02
  - fair-games-theorem-oq-02-oq-03
difficulty: medium
source: gallery-gap
created: 2026-04-22T09:05:08+02:00
```

**Significance**: 8/10
**Tractability**: 6/10
