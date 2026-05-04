# Problem: Newton-Girard Recurrence — Independent Inductive Proof Without Mathlib

## Statement

### Plain Language

Prove the general Newton-Girard recurrence for all k ≥ 1 using a direct inductive argument,
without relying on Mathlib's `MvPolynomial.psum_eq_mul_esymm_sub_sum`. The recurrence states:

  p_k = e_1·p_{k-1} − e_2·p_{k-2} + ... + (−1)^{k−1}·k·e_k

where p_k = Σ xᵢᵏ (power sums) and e_k = Σ_{i₁<...<iₖ} xᵢ₁···xᵢₖ (elementary symmetric polynomials).

### Formal Statement

For σ : Fintype and R : CommRing, the goal is a self-contained theorem:

```lean
theorem newton_girard_general (k : ℕ) (hk : 0 < k) :
    psum σ R k = ∑ j in Finset.range k, (−1 : R)^j • esymm σ R (j+1) * psum σ R (k-j-1)
                 + (−1 : R)^(k+1) • k • esymm σ R k
```

(Exact signature subject to refinement during OBSERVE phase.)

### Context

The parent proof `amgm-inequality-oq-02-oq-01-oq-02-oq-01` established cases k=1,2,3 from
the Mathlib lemma. This OQ asks for the general case by induction — a self-contained
verification that does not import the Mathlib result as a black box.

## Classification

```yaml
tier: B
significance: 6
tractability: 5
tags:
  - seeker-selected
  - extension
  - algebra
  - symmetric-functions
  - induction
```

**Significance**: 6/10 — Pedagogically valuable; demonstrates the recurrence can be proved
by elementary induction, not just via Mathlib's antidiagonal machinery.

**Tractability**: 5/10 — Challenging but well-defined. The inductive step requires careful
bookkeeping of signs and indices in MvPolynomial.

## Why This Matters

1. **Independence verification**: The parent proof relies on a Mathlib lemma as a black box.
   An inductive proof provides a genuinely self-contained gallery entry.
2. **Technique demonstration**: Shows how to work with `MvPolynomial`, `esymm`, and `psum`
   in an inductive setting — valuable for the wider Lean community.
3. **Mathlib PR candidate**: A clean standalone proof of the Newton-Girard recurrence could
   strengthen the existing Mathlib API or provide an alternative derivation.

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| `amgm-inequality-oq-02-oq-01-oq-02-oq-01` | Parent: k=1,2,3 cases via Mathlib lemma |
| `amgm-inequality-oq-02-oq-01-oq-02` | Off-Diagonal Symmetry in Symmetric Functions |
| `amgm-inequality-oq-02-oq-01` | Newton-Girard Identity: Square of Sum Decomposition |
| `amgm-inequality-oq-02` | Maclaurin's Inequalities (grandparent chain) |

## Key Lean Resources

- `MvPolynomial.psum_eq_mul_esymm_sub_sum` — the Mathlib lemma to avoid using
- `MvPolynomial.esymm_one`, `MvPolynomial.psum_one` — base cases
- `MvPolynomial.esymm_map_algebraMap` — potentially useful for recursion
- Existing lean file: `proofs/Proofs/AmgmInequalityOQ02OQ01OQ02OQ01.lean`

## Suggested Approach

1. **OBSERVE**: Read parent Lean file; understand existing MvPolynomial API
2. **ORIENT**: Check Mathlib for inductive machinery on `esymm`/`psum`; survey
   any existing proofs of Newton-Girard by induction in Mathlib4
3. **DECIDE**: Choose between (a) direct polynomial identity induction or
   (b) generating function approach if Mathlib formal power series are available
4. **ACT**: Implement base case (k=1: p₁=e₁) + inductive step
