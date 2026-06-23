# Problem: Prove `tsum_even_add_odd` via `Equiv` (Euler Identity Axiom Elimination)

**Slug**: euler-identity-oq-01-oq-01
**Created**: 2026-04-04T20:00:00-07:00
**Status**: Active
**Source**: gallery-gap
**Tier**: B | **Significance**: 6/10 | **Tractability**: 7/10

## Problem Statement

### Formal Statement

The parent proof `EulerIdentityOQ01.lean` uses this axiom:

```lean
axiom tsum_even_add_odd {f : ℕ → ℂ} (h : Summable f) :
  ∑' k : ℕ, f (2 * k) + ∑' k : ℕ, f (2 * k + 1) = ∑' n : ℕ, f n
```

**Goal**: Prove this as a theorem (eliminating the axiom) using `Equiv.tsum_eq` with
the explicit bijection `ℕ ⊕ ℕ ≃ ℕ` defined by `Sum.inl k ↦ 2*k` and `Sum.inr k ↦ 2*k+1`.

### Plain Language

Every summable sequence can be split into its even-indexed and odd-indexed subsequences,
and the two subseries sum to the original:

$$\sum_{n=0}^{\infty} f(n) = \sum_{k=0}^{\infty} f(2k) + \sum_{k=0}^{\infty} f(2k+1)$$

This is mathematically obvious but requires non-trivial API work in Lean 4 to prove
formally via `tsum` (topological sums, not finitely-supported sums).

## Why This Matters

1. **Axiom elimination**: Removes 1 of 3 axioms from `EulerIdentityOQ01.lean`, reducing
   the parent proof from 3 axioms to 2 — moving it one step closer to a fully verified
   formalization of Euler's 1748 argument.

2. **Reusable lemma**: The result is domain-general (`{f : ℕ → ℂ}` or even `{f : ℕ → α}`
   for a suitable topological structure) and could be contributed to Mathlib.

3. **Equiv technique**: Demonstrates the `Equiv.tsum_eq` pattern for type-index rewriting
   of infinite sums, a useful technique for future Taylor series formalizations.

## Approach via `Equiv`

The key bijection is:

```lean
def evenOddEquiv : ℕ ⊕ ℕ ≃ ℕ where
  toFun := fun x => match x with
    | Sum.inl k => 2 * k
    | Sum.inr k => 2 * k + 1
  invFun := fun n =>
    if n % 2 == 0 then Sum.inl (n / 2) else Sum.inr (n / 2)
  left_inv := by ...
  right_inv := by ...
```

Then use:
- `Equiv.tsum_eq evenOddEquiv` or `tsum_sum` for the coproduct split
- `HasSum.sigma` or `hasSum_iff_hasSum_compl_add_compl` for summability transfer
- `tsum_fintype` is not applicable (ℕ is infinite), use infinite splitting

**Alternative approaches**:
1. `Nat.sumCompl` — Mathlib may have a related bijection
2. Direct `hasSum` construction via `HasSum.add` on disjoint index sets
3. Check if `tsum_even_add_odd` already exists in Mathlib 4 under a different name
   (search `Mathlib.Topology.Algebra.InfiniteSum.*`)

## Lean 4 Infrastructure to Investigate

```lean
-- Key Mathlib APIs to examine:
#check Equiv.tsum_eq          -- reindex a tsum via equivalence
#check tsum_sum               -- tsum over a fintype sum of index types
#check HasSum.sigma           -- sigma type splitting
#check hasSum_subtype_compl   -- complementary subset splitting
#check Summable.hasSum        -- summability → hasSum
#check tsum_eq_zero_add       -- related: split off first term

-- In Mathlib.Topology.Algebra.InfiniteSum.Basic:
#check tsum_even_add_odd      -- CHECK: does this already exist?
```

## Classification

```yaml
tier: B
significance: 6
tractability: 7
tags:
  - analysis
  - infinite-sums
  - tsum
  - axiom-elimination
  - euler-identity
  - lean4-formalization
```

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| euler-identity-oq-01 | **Parent proof** — this eliminates its axiom #1 (`tsum_even_add_odd`) |
| euler-identity | Alternative Euler proof using Mathlib's `Complex.exp_mul_I` |
| fourier-series | Uses tsum splitting for Fourier coefficient extraction |

## Expected Deliverable

A file `proofs/Proofs/EulerIdentityOQ01OQ01.lean` containing:

```lean
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic

namespace EulerIdentityOQ01OQ01

theorem tsum_even_add_odd {f : ℕ → ℂ} (h : Summable f) :
    ∑' k : ℕ, f (2 * k) + ∑' k : ℕ, f (2 * k + 1) = ∑' n : ℕ, f n := by
  sorry  -- Prove via Equiv ℕ ⊕ ℕ ≃ ℕ

end EulerIdentityOQ01OQ01
```

with the sorry eliminated.

## Open Questions from Parent Proof

The `euler-identity-oq-01` conclusion explicitly asks:

> "Can `tsum_even_add_odd` be proved using `Equiv.tsum_eq` with the explicit bijection
> ℕ ≃ ℕ ⊕ ℕ given by even/odd decomposition?"

This problem answers that question.

## References

- Parent: `src/data/proofs/euler-identity-oq-01/meta.json` (see `assumptions` field)
- Parent Lean: `proofs/Proofs/EulerIdentityOQ01.lean` (axiom at lines 88-135)
- Mathlib: `Mathlib.Topology.Algebra.InfiniteSum.Basic`
