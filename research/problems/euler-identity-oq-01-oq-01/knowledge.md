# Knowledge Base: euler-identity-oq-01-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

**Goal**: Prove `tsum_even_add_odd` — split a summable series into even/odd subseries.

**Axiom signature** (from EulerIdentityOQ01.lean):
```lean
axiom tsum_even_add_odd {f : ℕ → ℂ} (h : Summable f) :
  ∑' k : ℕ, f (2 * k) + ∑' k : ℕ, f (2 * k + 1) = ∑' n : ℕ, f n
```

**Proposed approach**: Use `Equiv.tsum_eq` with the bijection `evenOddEquiv : ℕ ⊕ ℕ ≃ ℕ`
where `Sum.inl k ↦ 2*k` and `Sum.inr k ↦ 2*k+1`.

**Impact**: Eliminates axiom #1 of 3 from `EulerIdentityOQ01.lean` (parent proof).

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]
