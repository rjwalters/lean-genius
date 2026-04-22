# Problem: Fair Games — Wald's Identity Formalization via Mathlib

**Slug**: fair-games-theorem-oq-02-oq-01-oq-01
**Created**: 2026-04-22
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

Wald's Identity: If `(Y_i)` are i.i.d. random variables with `E[Y_i] = μ`, and `τ` is a
stopping time with `E[τ] < ∞`, then:

$$E\left[\sum_{i=1}^{\tau} Y_i\right] = \mu \cdot E[\tau]$$

Can this be formalized in Lean 4 using Mathlib's integration and martingale tools?

### Plain Language

Wald's identity says: if you stop a sequence of i.i.d. random variables at a random time
(a stopping time) that has finite expectation, then the expected total sum equals the
expected number of terms times the expected value of each term.

This is a fundamental result in sequential analysis and probability theory, closely
related to the optional stopping theorem (which has been formalized in `fair-games-theorem-oq-02-oq-01`).

### Why This Matters

- **Sequential analysis**: Wald's identity underlies sequential hypothesis testing,
  insurance risk theory, and random walk analysis.
- **Mathlib gap**: Wald's identity is not currently in Mathlib (as of early 2026), making
  this a genuine contribution opportunity.
- **Connection to gallery**: `fair-games-theorem-oq-02-oq-01` (Doob's OST, verified via Mathlib)
  provides infrastructure that should shorten this proof.
- **Generality**: Applies to gambling systems, random walks, branching processes.

## Known Results

### What's Already Proven

- `fair-games-theorem-oq-02-oq-01`: Doob's Optional Stopping Theorem via Mathlib
  (verified, badge: mathlib)
- Mathlib: `MeasureTheory.Martingale`, `MeasureTheory.StoppingTime`
- Mathlib: `MeasureTheory.integral_sum` for interchange of sum and expectation
- The optional stopping theorem (which is stronger than Wald's identity in some settings)

### What's Still Open

- Wald's identity in Lean 4 / Mathlib
- The precise Mathlib statement would need: `iid` formalization, `StoppingTime`, `E[τ] < ∞`

### Our Goal

Formalize Wald's identity:
```lean
theorem wald_identity {Ω : Type*} [MeasureSpace Ω] {Y : ℕ → Ω → ℝ}
    (h_iid : ∀ i, Integrable (Y i)) (h_mean : ∀ i, E[Y i] = μ)
    (τ : Ω → ℕ) (h_stop : IsStoppingTime ...) (h_fin : E[τ] < ∞) :
    E[∑ i in Finset.range τ, Y i] = μ * E[τ]
```
(exact form subject to Lean/Mathlib conventions)

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| fair-games-theorem-oq-02-oq-01 | Doob OST (parent), Mathlib-based | Martingales, stopping times |
| fair-games-theorem-oq-02 | Gambler's ruin via optional stopping | Probability, martingales |
| fair-games-theorem | Fair games / martingale convergence | Doob's theorem |

## Initial Thoughts

### Potential Approaches

1. **Martingale approach**: Note that `M_n = ∑_{i≤n} Y_i - n*μ` is a martingale (zero-mean
   i.i.d. increments). Apply optional stopping to get `E[M_τ] = 0`, which is exactly
   `E[∑ Y_i] = μ * E[τ]`.
   - Why it might work: Directly uses Doob OST from the gallery
   - Risk: Need `E[τ] < ∞` to control the remainder term

2. **Direct dominated convergence**: Express `E[∑_{i≤τ} Y_i] = ∑_{n≥0} E[Y_{n+1} * 1_{τ>n}]`
   and use independence of `Y_{n+1}` from `{τ > n}` (which is ℱ_n-measurable).
   - Why it might work: Standard textbook approach (Gut, "Probability: A Graduate Course")
   - Risk: Requires careful measurability arguments

3. **Adapt from Doob OST**: The Doob OST proof in `fair-games-theorem-oq-02-oq-01` already
   handles the interchange of expectation and stopping; Wald's identity may be a corollary.
   - Why it might work: Minimal new work if the OST proof is flexible enough
   - Risk: OST and Wald apply to different classes of processes

### Key Difficulties

- Formalizing i.i.d. in Mathlib: `ProbabilityTheory.iIndepFun`
- Interchange of sum and expectation: `E[∑ ...] = ∑ E[...]` under integrability
- Independence of `Y_{n+1}` from `𝒢_n` where `𝒢_n = σ(Y_1,...,Y_n)`

### What Would a Proof Need?

- `ProbabilityTheory.iIndepFun` for the i.i.d. assumption
- `MeasureTheory.StoppingTime.measurableSet_le` for filtration compatibility
- Dominated convergence theorem (`MeasureTheory.tendsto_integral_of_dominated_convergence`)
- E[τ] < ∞ expressed as `(fun ω => (τ ω : ℝ)).Integrable`

## Tractability Assessment

**Difficulty**: Challenging

**Justification**:
- The mathematical statement is well-understood and classical
- Mathlib has substantial probability infrastructure (martingales, stopping times)
- The main challenge is connecting i.i.d. independence to stopping time measurability
- No direct Mathlib import exists; requires building the argument from components

**Estimated Effort**:
- Exploration: 2-3 days (survey Mathlib probability API, find the right lemmas)
- If tractable: 1-2 weeks (the proof requires careful measurability bookkeeping)
- Milestone: Getting `E[∑_{i≤τ} Y_i] = ∑_{n≥0} E[Y_{n+1} 1_{τ>n}]` formalized

## References

### Papers
- Wald, A., "Sequential tests of statistical hypotheses" (1945)
- Gut, A., *Probability: A Graduate Course* (2005), Chapter 5

### Mathlib
- `ProbabilityTheory.iIndepFun` — independence of random variables
- `MeasureTheory.StoppingTime` — stopping times and filtrations
- `MeasureTheory.Martingale` — martingale definitions and OST
- `Doob_maximal_inequality` — from fair-games-theorem-oq-02-oq-01 infrastructure

## Metadata

```yaml
tags:
  - probability
  - martingale
  - optional-stopping
  - wald-identity
  - mathlib
  - sequential-analysis
related_proofs:
  - fair-games-theorem-oq-02-oq-01
  - fair-games-theorem-oq-02
difficulty: challenging
source: gallery-gap
created: 2026-04-22
```

**Significance**: 6/10
**Tractability**: 6/10
