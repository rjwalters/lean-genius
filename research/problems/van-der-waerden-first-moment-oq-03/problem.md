# Problem: Integrate the Verified First-Moment van der Waerden Lower Bound into the erdos-138 Framework (Reduce Axiomatized Growth Statements)

**Slug**: van-der-waerden-first-moment-oq-03
**Created**: 2026-06-28T10:47:36-07:00
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

The gallery proof `van-der-waerden-first-moment` establishes the *elementary*
first-moment (union-bound) lower bound for van der Waerden numbers: roughly
$$
W(k) \gtrsim 2^{(k-1)/2},
$$
formalized as `vdw_lower_bound : n*n < 2^(k-1) → (good 2-coloring exists)` in
`proofs/Proofs/VanDerWaerdenFirstMoment.lean` — a fully verified, axiom-free statement.
Meanwhile `erdos-138` (`Erdos138Problem.lean`) axiomatizes **all** of its growth bounds,
including `kozik_shabanov_lower_bound` ($W(k) \ge c\,2^k$) and `berlekamp_lower_bound`
($W(p+1) \ge p\,2^p$). Goal: connect the verified first-moment bound to erdos-138 and
replace reliance on an axiom by a machine-checked lower bound wherever the elementary
bound is strong enough to do so.

### Plain Language

erdos-138 currently *assumes* (as axioms) every lower bound on how fast van der Waerden
numbers grow. We already have a fully *proven* elementary lower bound in a separate file.
This task is to plug that proven bound into the erdos-138 development so that at least one
growth statement there stops being an axiom and becomes a theorem.

### Why This Matters

It reduces the axiom surface of a flagship gallery entry (erdos-138 has 8 axioms) by
contributing a verified growth statement. Even a weaker-but-proven bound improves
integrity over a stronger-but-axiomatized one for the regime it covers.

## Known Results

### What's Already Proven

- `van-der-waerden-first-moment` — verified `vdw_lower_bound` (elementary $\sim 2^{k/2}$), axiom-free.
- Mathlib `Combinatorics` van der Waerden existence (`Combinatorics.exists_mono_in_...`-style results).

### What's Still Open / Honest Constraint

- The elementary first-moment bound ($\sim 2^{k/2}$) is **weaker** than erdos-138's
  axiomatized lower bounds (`kozik_shabanov_lower_bound` $\sim 2^k$, `berlekamp_lower_bound`).
  It therefore **cannot** eliminate those specific stronger axioms.
- The tractable target is to add a *verified* lower-bound theorem to erdos-138's
  namespace (replacing the need to axiomatize the elementary regime) and to document
  precisely the strength gap to the remaining axiomatized bounds.

### Our Goal

1. State and prove, inside / importable by `Erdos138Problem.lean`, a verified lower bound
   on `W k` derived from `vdw_lower_bound` (no new axioms).
2. Identify whether any existing erdos-138 axiom is subsumed by it; if none is, downgrade
   the claim to "supplements" rather than "eliminates" and record the comparison.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| van-der-waerden-first-moment | Source of the verified bound | First-moment / union bound, `Finset` counting |
| erdos-138 | Target framework with axiomatized growth bounds | Axioms `kozik_shabanov_lower_bound`, `berlekamp_lower_bound` |

## Initial Thoughts

### Potential Approaches

1. **Approach A — direct import**: Re-express `vdw_lower_bound` in terms of erdos-138's
   `W` definition and add it as a theorem in that namespace.
   - Why it might work: Both are about the same object `W k`; mostly a definitional bridge.
   - Risk: Definitional mismatch between the two files' formulations of `W`.

2. **Approach B — honest negative result**: If the verified bound subsumes no existing
   axiom, prove the strength gap formally ($2^{k/2} = o(2^k)$) and document that the
   axiomatized bounds remain necessary, contributing the verified bound as a new theorem.
   - Why it might work: Always yields a publishable, honest outcome.
   - Risk: Lower "wow" value, but high integrity.

### Key Difficulties

- Reconciling the two files' definitions of $W$ and of "valid coloring".
- Avoiding overclaiming: the elementary bound does not match the axiomatized exponents.

### What Would a Proof Need?

- Key lemma 1: bridge `vdw_lower_bound`'s coloring-existence statement to a numeric lower bound on `W k`.
- Key lemma 2: a definitional-equivalence lemma between the two `W` formulations.

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- The hard analytic content (the first-moment bound) is already verified.
- Remaining work is a bridging/integration formalization with a guaranteed honest outcome.
- Risk is definitional friction, not deep mathematics.

**Estimated Effort**:
- Exploration: 1 day
- If tractable: 3–5 days
- If hard: 1–2 weeks (definitional reconciliation)

## References

### Papers
- Graham, Rothschild, Spencer, *Ramsey Theory* — van der Waerden number bounds.
- Erdős, probabilistic (first-moment) lower bounds for Ramsey-type numbers.

### Online Resources
- Mathlib docs: `Mathlib.Combinatorics.vanDerWaerden` and related.

### Mathlib
- `Finset` counting / first-moment infrastructure already used in the source file.

## Metadata

```yaml
tags:
  - combinatorics
  - van-der-waerden
  - first-moment
  - axiom-elimination
related_proofs:
  - van-der-waerden-first-moment
  - erdos-138
difficulty: medium
source: gallery-gap
created: 2026-06-28T10:47:36-07:00
```
