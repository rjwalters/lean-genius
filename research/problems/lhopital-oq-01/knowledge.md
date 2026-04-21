# Knowledge Base: lhopital-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

**Goal**: Prove the counterexample to the converse of L'Hôpital's rule:
- f(x) = x + sin(x), g(x) = x
- lim (f/g)(x) = 1 as x → ∞  [PROVED]
- lim (f'/g')(x) = lim (1 + cos x) does NOT exist [PROVED]

This is Lean formalization in `LHopitalOQ01.lean` (namespace `LHopitalConverse`).

---

## Insights

### Session 2026-04-21 (Session 1) — FRESH

**Mode**: FRESH
**Outcome**: Proof completed, building

#### Key Approach

**Part 1** (lim f/g = 1): Direct ε-N proof.
- Write (x + sin x)/x = 1 + sin(x)/x
- |sin x / x| ≤ 1/x for x > 0 (since |sin x| ≤ 1)
- For x > 1/ε + 1: 1/x < ε. Use `div_lt_iff` + `nlinarith` with hint `hfield : ε*(1/ε) = 1`

**Part 2** (no limit): Subsequential limit argument.
- Along n*2π: cos = 1, so 1+cos = 2. Use `Real.cos_nat_mul_two_pi`.
- Along n*2π+π: cos = -1, so 1+cos = 0. Use `Real.cos_nat_mul_two_pi_add_pi`.
- `tendsto_congr` converts `Tendsto (const c) atTop (𝓝 c)` to `Tendsto (const f) atTop (𝓝 c)`.
- `tendsto_nhds_unique` then derives L = 2 and L = 0 — contradiction.

#### Key Mathlib Lemmas Used
- `Real.abs_sin_le_one` — |sin x| ≤ 1
- `Real.cos_nat_mul_two_pi (n : ℕ)` — cos(n * 2π) = 1
- `Real.cos_nat_mul_two_pi_add_pi (n : ℕ)` — cos(n * 2π + π) = -1
- `Tendsto.atTop_mul_const'` — from `tendsto_natCast_atTop_atTop` to get n*2π → ∞
- `tendsto_atTop_mono` — n*2π ≤ n*2π+π entails second seq → ∞ too
- `tendsto_congr` — congruence for Tendsto
- `tendsto_nhds_unique` — uniqueness of limits in T2Space

#### Issues Encountered
- `hasDerivAt_id` → not in Mathlib; removed the lemma (not needed for main proof)
- `atTop_add_const` → doesn't exist; use `tendsto_atTop_mono` with `le_add_of_nonneg_right`
- `tendsto_congr` rewriting: use `.mp tendsto_const_nhds` pattern, not `rw [←...]`
- `nlinarith` needs explicit hint `hfield : ε*(1/ε) = 1` for the ε-N bound

---

## Files Created

- `proofs/Proofs/LHopitalOQ01.lean` — main proof file
- Gallery files: `src/data/proofs/lhopital-oq-01/` (meta.json, annotations.json, index.ts)

---

## Dead Ends

- `Filter.Tendsto.div_atTop` — requires f to converge, but sin x doesn't
- `squeeze_zero_norm` — worked in principle but the `|x|⁻¹ → 0` part needed careful handling
- `tendsto_abs_atTop_atTop` — doesn't exist in Mathlib

---

## Next Steps

1. Verify build compiles (ongoing)
2. If successful, commit and add to gallery
