# Problem: Erdős #1108 OQ-01 — Finitely Many Perfect Squares in Factorial Sums?

**Slug**: erdos-1108-oq-01
**Tier**: B | **Significance**: 6/10 | **Tractability**: 6/10
**Category**: completion
**Source**: gallery-gap
**Status**: Active (OBSERVE)

## Problem Statement

### Formal Statement

Let $A = \{\sum_{n \in S} n! : S \subseteq \mathbb{N},\, S \text{ finite}\}$ be the
set of all finite sums of distinct factorials. The open question is:

$$
|A \cap \{n^2 : n \in \mathbb{N}\}| < \infty \; ?
$$

In Lean, using definitions from `Erdos1108Problem.lean`:

```lean
-- Available gallery definitions:
def FactorialSums : Set ℕ :=
  {m : ℕ | ∃ S : Finset ℕ, m = ∑ n ∈ S, n.factorial}

def KthPowersInFactorialSums (k : ℕ) : Set ℕ :=
  {m ∈ FactorialSums | ∃ r : ℕ, m = r ^ k}

-- Open question: Is (KthPowersInFactorialSums 2).Finite ?
```

### Plain Language

Can a finite sum of distinct factorials equal a perfect square, and if so, are there
only finitely many such squares? The question is whether
$n_1! + n_2! + \cdots + n_r! = m^2$ has only finitely many solutions in distinct
non-negative integers.

Known: 1 = 0! = 1! is a perfect square in the set. Whether infinitely many others
exist is open.

**Status**: OPEN — asked by Erdős at Oberwolfach in 1988, motivated by discussions
with Mahler shortly before Mahler's death.

### Why This Matters

1. **Diophantine equations involving factorials** — rare intersection of exponential
   (factorial) and polynomial (square) growth
2. **Connection to Problem #398** — Erdős also asked whether $1 + n!$ is a perfect
   square for infinitely many n (also open)
3. **Brindza-Erdős partial result** — provides a key intermediate result about
   the largest factorial index in a powerful number representation
4. **Formalization target** — the Brindza-Erdős (1991) bound is a concrete known
   result that may be formalizable with Mathlib's factorial/prime power tools

## Known Results

### What's Already Proven

- **Brindza-Erdős (1991)**: For fixed r, if $n_1! + \cdots + n_r!$ is a powerful
  number then $n_1 \leq C(r)$ for some constant depending only on r.
- **Gallery base**: `Erdos1108Problem.lean` (171 lines, 0 axioms, 0 sorries) —
  fully formalized definitions with small example proofs.
- **1 is a solution**: `1 ∈ KthPowersInFactorialSums 2` is proved in the gallery.

### What's Still Open

- Whether `(KthPowersInFactorialSums 2).Finite` (the main OQ-01 question)
- Whether `PowerfulFactorialSums.Finite` (OQ-02)
- Whether $1 + n!$ is a square for infinitely many n (related Problem #398)

### Our Goal

**Primary**: Determine whether the Brindza-Erdős (1991) bound can be formalized in
Lean using Mathlib tools (`Nat.factorial`, `Nat.factorization`, `Nat.multiplicity`).

**Secondary**: Add the main conjecture as an axiom with supporting structure —
reduce the proof to its essential dependencies.

**Tertiary**: Survey Mathlib for Baker's theorem or related Baker-type bounds on
linear forms in logarithms that would close the gap.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `erdos-1108` | Parent — defines `FactorialSums`, `KthPowersInFactorialSums` | `Nat.factorial`, `Finset.sum` |
| `wilsons-theorem-oq-03` | Legendre formula for p-adic valuation of n! | `Nat.factorization` |
| `erdos-1132-oq-01` | Axiom reduction workflow reference | axiom reduction |

## Initial Thoughts

### Potential Approaches

1. **Formalize Brindza-Erdős bound**: The bound gives: for fixed r terms, if the sum
   is powerful then the smallest index is bounded. Proof uses Thue-Siegel-Roth/Baker.
   - Why it might work: Mathlib has `Nat.factorization_factorial`, Legendre tools
   - Risk: Baker's theorem (linear forms in logarithms) is not in Mathlib

2. **Axiomatize and derive consequences**: Add `brindza_erdos_bound` as an axiom
   and use it to derive finiteness for KthPowersInFactorialSums 2.
   - Why it might work: Standard axiom-reduction pattern used across Erdős gallery
   - Risk: The implication (bound for fixed r → finiteness for all r) is non-trivial

3. **Computational exploration**: Use `decide` or `norm_num` to verify no factorial
   sums up to some bound are squares other than 1.
   - Why it might work: Concrete bound on small cases
   - Risk: Only provides lower bound, doesn't address finiteness

### Key Difficulties

- **Baker's theorem** not in Mathlib — the main tool for Brindza-Erdős
- **Powerful number characterization**: Need to define and work with the condition
  `∀ p : ℕ, p.Prime → p ∣ m → p^2 ∣ m` explicitly in Lean
- **Growth rate formalization**: Factorial growth vs polynomial growth argument
  requires careful `Filter.Tendsto` reasoning

### What Would a Proof Need?

- `Nat.factorization_factorial` — p-adic valuation of n! (check if in Mathlib)
- `Nat.Powerful` or equivalent — powerful number definition
- Baker's theorem — likely must be axiomatized: `axiom baker_linear_log_form : ...`
- `Set.Finite.ofFinset` — once bounded, finiteness follows

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Main conjecture is genuinely OPEN — not just a formalization challenge
- However, Brindza-Erdős partial result provides concrete axiom target
- Gallery infrastructure is clean (0 axioms, 0 sorries) — good foundation
- Pattern matches other Erdős axiom-reduction problems in gallery
- Realistic outcome: 1-2 new axioms added, with structured proof outline

**Estimated Effort**:
- Exploration: 2-4 hours (check Mathlib API, survey proof structure)
- If axiomatizing Brindza-Erdős: 4-8 hours
- Full proof: Unknown — requires Baker's theorem formalization

## References

### Papers
- Brindza-Erdős (1991), "On some Diophantine problems involving powers and
  factorials", J. Austral. Math. Soc. Ser. A 51, 1-7.
- Mahler (1975), motivating problem about sums and perfect powers.

### Mathlib
- `Mathlib.Data.Nat.Factorial.Basic` — `Nat.factorial`, basic properties
- `Mathlib.Data.Nat.Multiplicity` — `Nat.factorization`, p-adic valuations
- `Mathlib.Data.Set.Finite` — `Set.Finite` for finiteness conclusion
- `Mathlib.NumberTheory.Bernoulli` — factorial-adjacent number theory

## Metadata

```yaml
tags:
  - erdos
  - number-theory
  - factorials
  - perfect-powers
  - diophantine
  - axiom-reduction
related_proofs:
  - erdos-1108
  - wilsons-theorem-oq-03
  - erdos-1132-oq-01
difficulty: medium
source: gallery-gap
created: 2026-04-05
```
