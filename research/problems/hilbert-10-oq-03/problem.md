# Problem: Characterize Number Fields with Decidable H10

**Slug**: hilbert-10-oq-03
**Created**: 2026-04-05T03:34:00-07:00
**Status**: Active
**Source**: gallery-gap
**Parent**: hilbert-10 (Hilbert's Tenth Problem: Undecidability of Diophantine Equations)
**Tier**: A
**Significance**: 8/10
**Tractability**: 4/10

---

## Problem Statement

### Formal Statement

Let $K$ be a number field (finite extension of $\mathbb{Q}$) and $\mathcal{O}_K$ its ring of integers.

**H10 for $\mathcal{O}_K$**: Is there an algorithm to decide whether a polynomial $P \in \mathbb{Z}[x_1, \ldots, x_n]$ has a solution in $\mathcal{O}_K^n$?

**Open question (oq-03)**: Characterize precisely which number fields $K$ have decidable H10 for $\mathcal{O}_K$.

The conjectured answer: H10 is **undecidable** for $\mathcal{O}_K$ for every number field $K$. This would follow if $\mathbb{Z}$ is Diophantine over $\mathcal{O}_K$ for all $K$.

### Plain Language

Hilbert's 10th problem asks: can you algorithmically check if a polynomial equation has integer solutions? MRDP (1970) proved: no, for $\mathbb{Z}$. But what about the ring of integers of other number fields like $\mathbb{Q}(\sqrt{2})$ or $\mathbb{Q}(\sqrt{-5})$?

We want to characterize exactly which number fields K have this problem decidable vs. undecidable. The prevailing expectation is that it's undecidable everywhere, but this requires showing $\mathbb{Z}$ is Diophantine (definable by a polynomial equation) inside each $\mathcal{O}_K$.

### Why This Matters

H10 over rings of integers generalizes one of the most celebrated undecidability results. A complete characterization would:
1. Settle the arithmetic definability of $\mathbb{Z}$ in all number rings
2. Connect computability theory, algebraic number theory, and elliptic curves
3. Provide a Lean-verifiable instantiation of undecidability beyond $\mathbb{Z}$

---

## Known Results

### What's Already Proven

- **$\mathbb{Z}$**: H10 is undecidable (MRDP theorem, 1970) — parent gallery proof `hilbert-10`
- **Totally real fields** (Julia Robinson, 1962): $\mathbb{Z}$ is first-order definable in $\mathcal{O}_K$ for all totally real $K$, hence H10 is undecidable
- **Imaginary quadratic fields**: H10 undecidable for $\mathbb{Q}(\sqrt{-d})$ via class group arguments
- **Shlapentokh (1989–2008)**: H10 undecidable for large classes of number fields using elliptic curve constructions to define $\mathbb{Z}$ Diophantinely
- **Mazur–Rubin (2010)**: Conditional on Shafarevich–Tate group assumptions, $\mathbb{Z}$ is Diophantine in $\mathcal{O}_K$ for all $K$

### What's Still Open

- Whether H10 over $\mathbb{Q}$ itself is decidable — a major open problem
- Whether every number field's ring of integers has undecidable H10 unconditionally (without BSD-type conjectures)
- A clean formal characterization of the decidable/undecidable boundary

### Our Goal

Formalize one of the known undecidability results for a specific class of number fields in Lean 4. The most tractable entry point is either:
- The totally real case (using Robinson's definability argument)
- A specific imaginary quadratic field
- A conditional result assuming $\mathbb{Z}$ is Diophantine in $\mathcal{O}_K$

---

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `hilbert-10` | Parent proof; H10 undecidable over $\mathbb{Z}$ | MRDP, reduction from halting |
| `hilbert-10-oq-01` | Companion open question (in-progress) | computability |
| `hilbert-10-oq-02` | Companion open question (in-progress) | computability |

---

## Initial Thoughts

### Potential Approaches

1. **Approach A: Conditional formalization**
   - Assume `ℤ_is_diophantine_in (K : NumberField)` as an axiom
   - Prove: this implies H10 undecidable for `𝒪_K`
   - Why it might work: the reduction is clean and mostly follows the MRDP template
   - Risk: may be a shallow restatement of `hilbert-10`

2. **Approach B: Robinson's totally real case**
   - Formalize Julia Robinson's first-order definition of $\mathbb{Z}$ in totally real fields
   - Lean's `Algebra.isTotallyReal` may provide hooks
   - Why it might work: definability argument is purely algebraic
   - Risk: Robinson's definability uses quantifier alternation — hard to formalize cleanly in Lean 4

3. **Approach C: Reduction framework**
   - Define a `H10Reducible` typeclass: rings where halting reduces to H10
   - Instantiate for $\mathbb{Z}$ (from parent proof), then show extension to $\mathcal{O}_K$ via universal property
   - Why it might work: compositional, reuses parent proof
   - Risk: Lean's instance hierarchy may require significant boilerplate

### Key Difficulties

- Robinson's definability uses model-theoretic quantifiers — translating to Lean is non-trivial
- Elliptic curve constructions (Shlapentokh's approach) require significant Mathlib machinery
- Any "complete characterization" theorem is still open mathematically — can only formalize known cases

### What Would a Proof Need?

- Key lemma: $\mathbb{Z}$ is Diophantine in $\mathcal{O}_K$ for the target field $K$
- Key lemma: H10 undecidable for $R$ whenever $\mathbb{Z}$ is Diophantine in $R$ (reduction from parent proof)
- Technical: number field ring-of-integers type in Lean/Mathlib (`RingOfIntegers`)

---

## Tractability Assessment

**Difficulty**: High (Moonshot for full characterization; High for conditional/specific case)

**Justification**:
- Full characterization requires open mathematics
- Conditional version (assuming $\mathbb{Z}$ Diophantine) is more tractable but may be shallow
- Totally real case requires Robinson's definability, which is a significant formalization project
- Mathlib has `NumberField`, `RingOfIntegers`, and `IsTotallyReal` — good infrastructure

**Estimated Effort**:
- Exploration: 1-2 sessions
- Conditional formalization: 2-4 sessions
- Robinson's totally real case: 5+ sessions

---

## References

### Papers
- Julia Robinson, "The undecidability of algebraic rings and fields", PAMS (1962)
- Alexandra Shlapentokh, *Hilbert's Tenth Problem: Diophantine Classes and Extensions to Global Fields*, Cambridge (2007)
- Barry Mazur & Karl Rubin, "Ranks of twists of elliptic curves and Hilbert's Tenth Problem", JAMS (2010)
- Kirsten Eisenträger, "Hilbert's tenth problem for algebraic function fields of characteristic 2", JNT (2004)

### Mathlib
- `Mathlib.NumberTheory.NumberField.Basic` — NumberField, RingOfIntegers
- `Mathlib.RingTheory.Polynomial.Basic` — polynomial ring tools
- `Mathlib.Logic.Encodable.Basic` — encodability for decidability arguments

---

## Metadata

```yaml
tags:
  - computability
  - undecidability
  - number-theory
  - hilbert-problems
  - number-fields
related_proofs:
  - hilbert-10
difficulty: high
source: gallery-gap
created: 2026-04-05T03:34:00-07:00
```
