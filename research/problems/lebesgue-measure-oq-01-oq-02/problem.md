# Problem: Lebesgue Integral of Thomae Function via Bochner Integral

**Slug**: lebesgue-measure-oq-01-oq-02
**Created**: 2026-04-05
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\int_0^1 f(x) \, d\lambda = 0
\quad \text{where} \quad
f(x) = \begin{cases} 1/q & \text{if } x = p/q \text{ in lowest terms} \\ 0 & \text{if } x \in \mathbb{R} \setminus \mathbb{Q} \end{cases}
$$

### Plain Language

The **Thomae function** (also called the modified Dirichlet function or popcorn function) assigns $1/q$ to every rational $p/q$ in lowest terms, and $0$ to every irrational. Compute its Lebesgue integral explicitly using Mathlib's Bochner integral framework. The answer is 0 because the Thomae function equals 0 almost everywhere — its support is exactly $\mathbb{Q} \cap [0,1]$, which is countable and has Lebesgue measure 0.

### Why This Matters

This is Open Question #2 from `lebesgue-measure-oq-01` (the Dirichlet function gallery proof). While the Dirichlet function integral (OQ-01) was proved using `integral_eq_zero_of_ae`, the Thomae function requires working with a more complex function (varying values $1/q$, not just $0/1$). The result illustrates a key principle: the Lebesgue integral ignores countable sets, so even a function with dense discontinuities can integrate to exactly 0.

## Known Results

### What's Already Proven

- `lebesgue-measure-oq-01`: The Dirichlet function $\mathbf{1}_\mathbb{Q}$ integrates to 0 via `integral_eq_zero_of_ae`
- `Mathlib.MeasureTheory.Integral.SetIntegral`: Bochner integral framework
- Rationals are countable: `Rat.countable`
- Countable sets have measure zero: `MeasureTheory.measure_countable`
- `MeasureTheory.integral_eq_zero_of_ae` — if f = 0 a.e. then ∫ f = 0

### What's Still Open

- Explicit Bochner integral computation for Thomae function in Lean
- Measurability of Thomae function (needed as precondition)

### Our Goal

1. Define the Thomae function in Lean 4
2. Prove it is measurable (or a.e. equal to a measurable function)
3. Prove it equals 0 almost everywhere (support ⊆ ℚ which has measure 0)
4. Conclude the Bochner integral is 0 via `integral_eq_zero_of_ae`

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `lebesgue-measure-oq-01` | Direct parent — proved Dirichlet function integral | `integral_eq_zero_of_ae`, `ae_iff` |
| `lebesgue-measure` | Grandparent — Lebesgue measure basics | Measure theory infrastructure |
| `lebesgue-measure-oq-02` | Sibling — Thomae and Riemann integrability (Lebesgue criterion) | Lebesgue criterion |

## Initial Thoughts

### Potential Approaches

1. **AE zero approach** (most direct):
   - Show Thomae function is 0 for all irrationals
   - The rationals have measure 0 (countable)
   - Apply `integral_eq_zero_of_ae` directly
   - Risk: Need measurability of Thomae function first

2. **Indicator function decomposition**:
   - Decompose Thomae as $\sum_{n=1}^{\infty} \frac{1}{n} \cdot \mathbf{1}_{S_n}$ where $S_n = \{p/n : \gcd(p,n)=1\}$
   - Each $S_n$ is finite (measure 0), so each term integrates to 0
   - Risk: Convergence argument needed for infinite sum

### Key Difficulties

- Defining Thomae function in Lean without decidability issues (use `Classical`)
- Proving measurability (Thomae is Borel measurable via continuity at irrationals)
- The `if x ∈ ℚ then ... else 0` pattern requires `Decidable` instances or `Classical.dec`

### What Would a Proof Need?

- Key lemma 1: `thomae_ae_zero : ∀ᵐ x ∂μ, thomae x = 0`
- Key lemma 2: `thomae_measurable : Measurable thomae` (or `AEMeasurable`)
- Conclusion: `∫ x in Set.Icc 0 1, thomae x ∂MeasureTheory.volume = 0`

## Tractability Assessment

**Difficulty**: Low-Medium

**Justification**:
- Core idea identical to Dirichlet function proof (already done in OQ-01)
- Main new work: defining Thomae function and proving measurability
- Measurability is the potential sticking point
- Mathlib has all needed building blocks

**Estimated Effort**:
- Exploration: 1-2 hours
- If tractable: 1-3 days

## References

### Mathlib
- `MeasureTheory.integral_eq_zero_of_ae` — key lemma
- `MeasureTheory.measure_countable` — countable sets have measure 0
- `Rat.countable` — ℚ is countable
- `Mathlib.MeasureTheory.Integral.Bochner` — Bochner integral framework

## Metadata

```yaml
tags:
  - measure-theory
  - lebesgue-integral
  - bochner-integral
  - thomae-function
  - almost-everywhere
related_proofs:
  - lebesgue-measure-oq-01
  - lebesgue-measure
  - lebesgue-measure-oq-02
difficulty: low-medium
source: gallery-gap
created: 2026-04-05
```
