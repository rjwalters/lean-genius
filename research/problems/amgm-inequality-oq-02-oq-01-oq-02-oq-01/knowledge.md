# Knowledge Base: amgm-inequality-oq-02-oq-01-oq-02-oq-01

**Last Updated**: 2026-04-26

---

## Problem Understanding

Prove the Newton-Girard recurrence corollaries connecting power sums and elementary
symmetric polynomials. Key objects:
- `psum σ R k` = Σᵢ Xᵢᵏ (k-th power sum polynomial)
- `esymm σ R k` = Σ_{i₁<...<iₖ} Xᵢ₁·...·Xᵢₖ (k-th elementary symmetric polynomial)
- `MvPolynomial.psum_eq_mul_esymm_sub_sum`: Newton's identity in Mathlib's antidiagonal form

---

## Session 2026-04-26 (Session 1) — All 3 Corollaries Proved

**Mode**: FRESH
**Outcome**: COMPLETED — 3 → 0 sorries

### What I Did

1. Surveyed Mathlib's `NewtonIdentities.lean` to understand `psum_eq_mul_esymm_sub_sum` signature
2. Read `psum_one`, `esymm_one` from Mathlib Defs
3. Removed incorrect `newton_girard_recurrence` wrapper (used `range` form vs actual `antidiagonal` form)
4. Proved all three corollaries directly from `psum_eq_mul_esymm_sub_sum`

### Key Findings

**`psum_one_eq_esymm_one`**: Trivial — `psum_one.trans esymm_one.symm`. Both are `∑ i, X i`.

**`psum_two_eq`** (p₂ = e₁² − 2·e₂):
- Apply `psum_eq_mul_esymm_sub_sum` at k=2
- `antidiagonal(2) ∩ Ioo 0 2 = {(1,1)}` (computed by `omega`)
- `(-1)^3 * 2 * e₂ - (-1)^1 * e₁ * e₁ = e₁² - 2e₂` closes by `ring`

**`psum_three_eq`** (p₃ = e₁·p₂ − e₂·p₁ + 3·e₃):
- Apply `psum_eq_mul_esymm_sub_sum` at k=3
- `antidiagonal(3) ∩ Ioo 0 3 = {(1,2),(2,1)}` (computed by `omega`)
- `Finset.sum_insert (by decide)` separates the two elements
- `(-1)^4 * 3 * e₃ - ((-1)^1 * e₁ * p₂ + (-1)^2 * e₂ * p₁) = e₁*p₂ - e₂*p₁ + 3*e₃` by `ring`

### Reusable Pattern

```lean
have hfilt : (Finset.antidiagonal n).filter (fun a : ℕ × ℕ => a.1 ∈ Ioo 0 n) = {s} := by
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, Finset.Nat.mem_antidiagonal, mem_Ioo,
             Finset.mem_singleton, Prod.mk.injEq]
  omega
simp only [hfilt, Finset.sum_singleton, ...]
ring
```

This pattern handles any concrete `k` by `omega`-deciding the filter and then `ring` for the algebra.

### Files Modified

- `proofs/Proofs/AmgmInequalityOQ02OQ01OQ02OQ01.lean` (0 sorries, 0 axioms)
- `src/data/proofs/amgm-inequality-oq-02-oq-01-oq-02-oq-01/meta.json` (status → verified, sorries → 0)

### PR

PR #12569: feat: Newton-Girard corollaries k=1,2,3 proved (0 sorries, 0 axioms)
