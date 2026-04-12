# Knowledge Base: denumerability-rationals-oq-01

## Problem: The Cardinality Gap — ℚ, ℝ, and the Continuum Hypothesis

**Status**: COMPLETED (0 sorries, 2 axioms for independence)
**Phase**: COMPLETED
**File**: `proofs/Proofs/DenumerabilityRationalsOQ01.lean` (270 lines)

---

## Problem Understanding

Starting from the denumerability of ℚ (|ℚ| = ℵ₀, proved in `DenumerabilityRationals.lean`),
this problem asks: what cardinals lie between |ℚ| and |ℝ|?

This is precisely the Continuum Hypothesis (CH), independent of ZFC.

---

## Session 2026-04-06 (Session 1) — Complete Proof

**Mode**: FRESH
**Outcome**: completed — 0 sorries, 2 axioms, builds successfully

### What I Did

1. Studied related proofs: `ContinuumHypothesis.lean`, `CantorsTheoremOQ01.lean`, existing OQs
2. Designed 7-part proof structure connecting denumerability to CH
3. Identified exact Mathlib lemma names needed
4. Wrote `DenumerabilityRationalsOQ01.lean` (270 lines)
5. Fixed two compilation errors:
   - CH equivalence: rewrote complex `rw` chain to explicit `h_aleph1_succ` lemma
   - `Cardinal.continuum_def` doesn't exist → used `Cardinal.two_power_aleph0.symm`
6. Build passed: `✔ [3061/3061] Built Proofs.DenumerabilityRationalsOQ01`

### Key Findings

- `Cardinal.mk_denumerable ℚ : Cardinal.mk ℚ = ℵ₀` — clean entry point
- `Cardinal.mk_real : #ℝ = 𝔠` — direct from Mathlib
- `Cardinal.aleph_one_le_continuum` exists in Mathlib (not just in gallery files)
- Key proof: `Cardinal.aleph 1 = Order.succ ℵ₀` requires `Cardinal.aleph_succ` + `Cardinal.aleph_zero` + ordinal `1 = succ(0)` from `Order.succ_eq_add_one`
- `Order.lt_succ_iff.mp` closes `κ < Order.succ ℵ₀ → κ ≤ ℵ₀`
- `Cardinal.two_power_aleph0 : 2^ℵ₀ = 𝔠` is the key continuum lemma (not `continuum_def`)

### Files Created

- `proofs/Proofs/DenumerabilityRationalsOQ01.lean` (new)
- `src/data/proofs/denumerability-rationals-oq-01/meta.json` (new)
- `src/data/research/problems/denumerability-rationals-oq-01.json` (updated)

### Mathematical Summary

Proved in ZFC (0 axioms needed):
1. |ℚ| = ℵ₀ < |ℝ| = 𝔠 (the gap exists)
2. |𝒫(ℚ)| = 𝔠 (Dedekind cut connection)
3. ℵ₁ ≤ 𝔠 (smallest uncountable ≤ continuum)
4. CH ↔ no intermediate cardinal (equivalence proved)
5. CH implications: under CH, only {ℵ₀, 𝔠} among infinite cardinals ≤ 𝔠

Required axioms (2 for independence):
- `godel_ch_consistent_with_ZFC` — Gödel 1940
- `cohen_not_ch_consistent_with_ZFC` — Cohen 1963

### Next Steps

None — proof is complete. Potential future work:
- Formalize PFA implying 𝔠 = ℵ₂
- Formalize Easton's theorem constraints on 2^κ
