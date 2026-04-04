# Problem: Fodor's Pressing-Down Lemma

**Slug**: cantor-diagonalization-oq-02-oq-03-oq-02
**Created**: 2026-04-04T02:41:19-07:00
**Status**: Active
**Source**: cantor-diagonalization-oq-02-oq-03 <!-- gallery-gap | proof-suggestion | user-request | external -->

## Problem Statement

Formalize Fodor's pressing-down lemma (Fodor 1956): for any regular uncountable cardinal κ, any regressive function f: S → κ.ord on a stationary set S ⊆ κ.ord (i.e., f(α) < α for all α ∈ S) is constant on some stationary subset. This requires formalizing stationary and club sets in Lean.

### Formal Statement

$$
\text{For any regular uncountable cardinal } \kappa \text{ and regressive } f: S \to \kappa
\text{ on stationary } S \subseteq \kappa, \exists \alpha < \kappa, f^{-1}(\{\alpha\}) \text{ is stationary.}
$$

### Plain Language

Fodor's lemma (also called the Pressing-Down Lemma) is a fundamental result in set theory. It says that if you have a stationary set of ordinals and a function that sends each ordinal to a strictly smaller one, then some value must be attained on a stationary subset. This is closely related to the diagonal argument generalized to regular cardinals.

### Why This Matters

Fodor's lemma is a cornerstone of infinite combinatorics and set theory. It is used in many arguments involving club and stationary sets. Formalizing it in Lean requires first formalizing the notions of club sets and stationary sets for regular cardinals.

## Known Results

### What's Already Proven

- Diagonal argument generalized to regular cardinals — gallery proof cantor-diagonalization-oq-02-oq-03
- Basic ordinal arithmetic in Mathlib

### What's Still Open

- Lean formalization of stationary and club sets for uncountable regular cardinals
- Fodor's lemma itself

### Our Goal

Formalize Fodor's pressing-down lemma in Lean 4 using Mathlib's ordinal and cardinal theory, including the necessary definitions of club and stationary sets.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| cantor-diagonalization-oq-02-oq-03 | Parent: Diagonal Argument Generalized to Regular Cardinals | Ordinals, cardinals, diagonal |

## Initial Thoughts

### Potential Approaches

1. **Direct formalization**: Define club/stationary sets, prove Fodor's lemma directly
   - Why it might work: The proof is classical and well-documented
   - Risk: Mathlib may lack key pieces of the ordinal/cardinal API

2. **Leverage Mathlib ordinals**: Use existing Mathlib ordinal theory as a base
   - Why it might work: Mathlib has substantial ordinal/cardinal theory
   - Risk: Club/stationary set definitions may need to be added from scratch

### Key Difficulties

- Defining stationary and club sets for arbitrary regular uncountable cardinals in Lean 4
- The proof requires transfinite induction arguments
- Mathlib's club/stationary set API status is uncertain

### What Would a Proof Need?

- Key lemma 1: Definition and basic properties of club sets
- Key lemma 2: Definition and basic properties of stationary sets
- Technical requirements: Regular cardinal and regressive function APIs in Mathlib

## Tractability Assessment

**Difficulty**: Challenging

**Justification**:
- Requires significant set-theoretic infrastructure
- Mathlib's support for club/stationary sets needs checking
- The proof technique is well-known but the formalization setup is non-trivial

**Estimated Effort**:
- Exploration: 2-3 days
- If tractable: 2-3 weeks
- If hard: unknown

## References

### Papers
- Fodor, G. (1956) — "Eine Bemerkung zur Theorie der regressiven Funktionen"

### Online Resources
- Mathlib Ordinal and Cardinal modules

### Mathlib
- `Mathlib.SetTheory.Ordinal.Basic` — ordinal arithmetic
- `Mathlib.SetTheory.Cardinal.Basic` — cardinal arithmetic

## Metadata

```yaml
tags:
  - set-theory
  - ordinals
  - cardinals
  - stationary-sets
  - fodors-lemma
related_proofs:
  - cantor-diagonalization-oq-02-oq-03
difficulty: challenging
source: cantor-diagonalization-oq-02-oq-03
category: extension
created: 2026-04-04T02:41:19-07:00
```

**Significance**: 8/10
**Tractability**: 6/10
