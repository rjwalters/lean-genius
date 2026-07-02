# Problem: Continued-Fraction Expansion of log₂3 for Eliahou's Sharp Cycle-Length Constant

**Slug**: collatz-cycles-oq-02-oq-01
**Created**: 2026-07-02
**Status**: Active
**Source**: proof-suggestion <!-- open question of the verified parent collatz-cycles-oq-02 -->

## Problem Statement

### Formal Statement

$$
\text{Compute the continued fraction } \log_2 3 = [1; 1, 1, 2, 2, 3, 1, 5, \ldots]\
\text{and use its convergents } p_k/q_k \text{ to bound } |q \log_2 3 - p|\
\text{from below, yielding Eliahou's sharp constant in } L \ge c \cdot \log(\text{min element}).
$$

### Plain Language

The parent proof gives a general logarithmic lower bound on the length L of a nontrivial Collatz cycle. Eliahou (1993) sharpened the constant in that bound; the sharpening rests on how well log₂3 can be approximated by rationals, which is governed by the continued-fraction expansion of log₂3. This problem asks to formalize that continued-fraction expansion (its early partial quotients / convergents) and extract the explicit irrationality-measure input that produces Eliahou's sharp numerical constant.

### Why This Matters

It converts an abstract "there exists a constant" bound into an explicit, certified numerical constant, and it exercises Mathlib's continued-fraction and Diophantine-approximation machinery on a concrete transcendental-flavored quantity. The convergent-based lower bound on |q·log₂3 − p| is a reusable Diophantine ingredient.

## Known Results

### What's Already Proven

- General logarithmic lower bound on Collatz cycle length — parent `collatz-cycles-oq-02` (verified, 0-axiom, original).
- Mathlib continued-fraction API (`GenContFract`) and convergent properties.

### What's Still Open (in the gallery)

- The explicit continued-fraction convergents of log₂3 and the resulting sharp constant.

### Our Goal

Formalize the first several convergents of log₂3, prove the standard best-approximation lower bound `|q·log₂3 − p| ≥ 1/(q_{k+1}+q_k)` for the relevant range, and thread it into a sharpened cycle-length constant matching Eliahou's value.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| collatz-cycles-oq-02 | Direct parent; the cycle-length bound whose constant we sharpen | logarithmic estimates, diophantine input |

## Initial Thoughts

### Potential Approaches

1. **Approach A — Convergent lower bound (recommended)**: use the general continued-fraction fact that for a best-approximation denominator q_k, `|q_k·α − p_k|` is bounded below in terms of q_{k+1}; specialize α = log₂3. Verify the early partial quotients numerically (interval arithmetic / `norm_num` on 2^p vs 3^q inequalities) and feed the convergent bound into the parent inequality.
   - Why it might work: the irrationality-measure input is a clean, standard CF lemma; the numeric partial quotients are decidable via integer power comparisons.
   - Risk: certifying partial quotients requires careful `2^a < 3^b < 2^c` bounds; matching Eliahou's exact constant needs the right convergent depth.

2. **Approach B — Direct log₂3 bounds**: bypass the full CF and prove just the specific rational-approximation inequality Eliahou uses.
   - Why it might work: less machinery.
   - Risk: less reusable; may still need CF facts implicitly.

### Key Difficulties

- Certifying `log₂3`'s partial quotients from integer power inequalities.
- Reproducing Eliahou's exact constant (bookkeeping of which convergent is used).

### What Would a Proof Need?

- Key lemma 1: partial quotients of log₂3 up to needed depth, via `2^p` vs `3^q` comparisons.
- Key lemma 2: convergent best-approximation lower bound on `|q·log₂3 − p|`.
- Technical requirements: `Mathlib.Algebra.ContinuedFractions.*`, `Real.logb`, `norm_num`.

## Tractability Assessment

**Difficulty**: Medium–High

**Justification**:
- The Diophantine-approximation core is standard, but pinning the exact Eliahou constant and certifying CF partial quotients in Lean is delicate.
- A partial result (an explicit, possibly non-optimal, improved constant) is a valuable intermediate deliverable.

**Estimated Effort**:
- Exploration: 1–2 days
- If tractable: 1–2 weeks

## References

### Papers
- S. Eliahou, "The 3x+1 problem: new lower bounds on nontrivial cycle lengths," Discrete Math. 118 (1993) — source of the sharp constant.

### Mathlib
- `Mathlib.Algebra.ContinuedFractions.Computation.*` — CF of a real number and convergents.
- `Mathlib.Analysis.SpecialFunctions.Logb` — `log₂`.

## Metadata

```yaml
tags:
  - number-theory
  - collatz
  - continued-fractions
  - diophantine-approximation
related_proofs:
  - collatz-cycles-oq-02
difficulty: high
source: proof-suggestion
created: 2026-07-02
```
