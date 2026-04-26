# Knowledge Base: Newton-Girard Recurrence for Symmetric Polynomials

**Problem**: amgm-inequality-oq-02-oq-01-oq-02-oq-01
**Last Updated**: 2026-04-26
**Status**: COMPLETE (0 sorries, 0 axioms)

---

## Problem Understanding

Prove the 3 Newton-Girard corollaries connecting power sums pₖ and elementary
symmetric polynomials eₖ, using Mathlib's `psum_eq_mul_esymm_sub_sum`.

- p₁ = e₁
- p₂ = e₁² − 2·e₂
- p₃ = e₁·p₂ − e₂·p₁ + 3·e₃

---

## Session 2026-04-26 (Session 1) — Complete Proof

**Mode**: FRESH
**Outcome**: All 3 corollaries proved (0 sorries)

### What I Did

1. Surveyed `AmgmInequalityOQ02OQ01OQ02OQ01.lean` — had 3 sorry corollaries
2. Fixed `newton_girard_recurrence` (wrong signature: `n ≠ 0` → `0 < n`, wrong sum form)
3. Found `antidiagonal` comes from `HasAntidiagonal` typeclass (`export HasAntidiagonal (antidiagonal mem_antidiagonal)`)
4. Proved all 3 corollaries via `psum_eq_mul_esymm_sub_sum` + filter computation + `ring`

### Key Findings

- `antidiagonal` is accessible globally via `HasAntidiagonal` export (NOT `Nat.antidiagonal`)
- `mem_antidiagonal` is the simp lemma for antidiagonal membership
- For `psum_one_eq_esymm_one`: `rw [psum_one, esymm_one]` closes directly
- For `psum_two_eq`: antidiagonal 2 filtered by `Set.Ioo 0 2` = `{(1,1)}`; then `ring`
- For `psum_three_eq`: antidiagonal 3 filtered by `Set.Ioo 0 3` = `{(1,2),(2,1)}`; then `ring`
- Named args `(σ := σ) (R := R)` needed for `psum_eq_mul_esymm_sub_sum` in term-mode (not tactic mode)
- `ring` handles `(-1)^3 = -1`, `(-1)^4 = 1` in CommRing correctly
- `with` syntax (`∑ a ∈ s with P, f`) must match Mathlib's form for `exact` to typecheck

### Files Modified

- `proofs/Proofs/AmgmInequalityOQ02OQ01OQ02OQ01.lean` — 3 sorries → 0 sorries

### Proof Strategy

```lean
-- p₁ = e₁
theorem psum_one_eq_esymm_one : psum σ R 1 = esymm σ R 1 := by rw [psum_one, esymm_one]

-- p₂ = e₁² − 2·e₂
have h := psum_eq_mul_esymm_sub_sum (σ := σ) (R := R) 2 two_pos
have hfilt : (antidiagonal 2).filter (... Set.Ioo 0 2) = {(1,1)} := by
  ext ⟨a, b⟩; simp only [mem_filter, mem_antidiagonal, Set.mem_Ioo, ...]; omega
rw [hfilt, sum_singleton] at h
rw [h, psum_one_eq_esymm_one]; ring

-- p₃ = e₁·p₂ − e₂·p₁ + 3·e₃
-- same pattern with antidiagonal 3 → {(1,2),(2,1)}
rw [hfilt, sum_insert (by decide : (1,2) ∉ ({(2,1)} : Finset _)), sum_singleton] at h
rw [h]; ring
```

---

## Insights

1. `antidiagonal n` for ℕ comes from `HasAntidiagonal` typeclass export, not `Nat.antidiagonal`
2. `mem_antidiagonal : a ∈ antidiagonal n ↔ a.fst + a.snd = n` is auto-simp
3. `ext ⟨a, b⟩ + simp [mem_filter, mem_antidiagonal, Set.mem_Ioo] + omega` proves filter = small Finset
4. Named args `(σ := σ) (R := R)` required for implicit arg inference in term-mode Newton-Girard proof
5. `ring` in CommRing correctly evaluates `(-1)^n` for small concrete n
6. `with` notation for sums (`∑ a ∈ s with P`) must match Mathlib's form for `exact` unification
