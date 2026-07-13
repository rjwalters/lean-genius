# Problem: Higher-order fixed-point-free characterization of the diagonal argument

**Slug**: cantors-theorem-oq-03-oq-02
**Created**: 2026-06-24
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The Lawvere fixed-point form of Cantor's theorem says: if there is no $g : \beta \to \beta$ without a fixed point (equivalently, if every endo-map of $\beta$ has a fixed point), then no $f : \alpha \to (\alpha \to \beta)$ is surjective. This leaf asks for the **higher-order** analogue:
$$
\text{for } f : \alpha \to \big((\alpha \to \beta) \to \gamma\big), \quad \text{what condition on } \gamma \text{ replaces ``}g : \beta \to \beta\text{ has no fixed point''?}
$$
Determine and prove the correct structural (Lawvere-style) hypothesis under which such higher-order $f$ cannot be surjective.

### Plain Language

Cantor's diagonal argument has a clean abstract form (Lawvere's fixed-point theorem): surjectivity of a map into a function space forces every self-map of the codomain to have a fixed point. The parent entry develops this fixed-point-free characterization. This leaf pushes it **one type-level up** — from codomains $\alpha \to \beta$ to higher-order codomains $(\alpha \to \beta) \to \gamma$ — and asks what the corresponding non-existence-of-fixed-point condition becomes.

### Why This Matters

Pins down exactly how Lawvere's diagonal lemma scales to higher-order function spaces — clarifying the general "no-fixed-point ⟹ no-surjection" pattern that underlies Cantor, Russell, Gödel, and Tarski. A conceptual consolidation with reusable Lean lemmas.

## Known Results

### What's Already Proven

- Parent `cantors-theorem-oq-03` — the diagonal argument in cardinal arithmetic and the fixed-point-free characterization.
- Mathlib: `Function.cantor_surjective`, `Function.cantor_injective`, and the general Lawvere fixed-point lemma pattern (`Function.Surjective` + diagonalization).

### What's Still Open

- The higher-order statement and the precise hypothesis on $\gamma$.
- Whether the higher-order case reduces to the first-order Lawvere lemma or genuinely needs a new structural condition.

### Our Goal

State the higher-order Lawvere/diagonal lemma for codomain $(\alpha \to \beta) \to \gamma$, identify the correct fixed-point hypothesis, and prove the non-surjectivity conclusion axiom-free.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cantors-theorem-oq-03 | Parent: diagonal/fixed-point characterization | Lawvere diagonal lemma |
| cantor-diagonalization-oq-04-oq-01-oq-01-oq-01 | Diagonalization machinery | diagonal construction |

## Initial Thoughts

### Potential Approaches

1. **Approach A — reduce to first-order Lawvere**: Treat $(\alpha \to \beta) \to \gamma$ as a codomain and apply the standard Lawvere lemma with the right "point-surjectivity" hypothesis; check whether the fixed-point condition is simply on $\gamma$-valued self-maps.
   - Why it might work: Lawvere's lemma is parametric in the codomain; the higher-order case may be an instance.
   - Risk: the higher-order structure may require weak point-surjectivity rather than plain surjectivity.

2. **Approach B — direct diagonal construction**: Build the diagonal map explicitly at the higher type and derive a fixed point, isolating the needed hypothesis.
   - Why it might work: makes the structural condition explicit.
   - Risk: more intricate; higher-order diagonalization bookkeeping.

### Key Difficulties

- Correctly formulating the higher-order hypothesis (point-surjectivity vs. surjectivity).
- Avoiding a vacuous or trivially-reducible statement.

### What Would a Proof Need?

- Key lemma 1: the parametric Lawvere fixed-point lemma.
- Key lemma 2: the higher-order diagonalization map and its fixed point.
- Technical requirements: careful handling of `Function.Surjective` at the higher type.

## Tractability Assessment

**Difficulty**: Medium–High

**Justification**:
- Mathlib has the first-order Cantor/Lawvere lemmas to build on.
- The conceptual work (finding the right hypothesis) is the bottleneck, not raw proof engineering.
- Risk that the statement collapses to the first-order case, requiring careful scoping to stay non-trivial.

**Estimated Effort**:
- Exploration: 1 day (decide the right statement)
- If tractable: 2–4 days
- If hard: unknown

## References

### Papers
- F. W. Lawvere, "Diagonal arguments and cartesian closed categories" (1969) — the fixed-point lemma underlying all diagonal arguments.

### Mathlib
- `Mathlib.Logic.Function.Basic` — `Function.cantor_surjective`, `Function.cantor_injective`.

## Metadata

```yaml
tags:
  - set-theory
  - diagonal-argument
  - fixed-point
  - higher-order
related_proofs:
  - cantors-theorem-oq-03
  - cantor-diagonalization-oq-04-oq-01-oq-01-oq-01
difficulty: high
source: gallery-gap
created: 2026-06-24
```
