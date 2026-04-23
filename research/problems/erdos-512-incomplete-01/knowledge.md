# Knowledge: erdos-512-incomplete-01

## Problem Summary

**Goal**: Fill measure theory sorries in `Erdos512Problem.lean` (Littlewood conjecture formalization).

**File**: `proofs/Proofs/Erdos512Problem.lean`

## Status: 1 sorry remaining (L2_norm / Parseval)

### Sorries
1. `L1norm_upper_bound` (line 102): `∫₀¹ |∑_{n∈A} e(nθ)| dθ ≤ |A|` — **PROVED**
2. `L2_norm` (line 194): `∫₀¹ |∑_{n∈A} e(nθ)|² dθ = |A|` — **OPEN** (Parseval's theorem)

## Proof Architecture

### L1norm_upper_bound (PROVED)

Strategy:
1. **Continuity**: `expSumNorm A` is continuous (finite sum of continuous exponentials + Complex.abs). Proved via `Complex.continuous_abs.comp + continuous_finset_sum + Complex.continuous_exp.comp + fun_prop`.
2. **Integrability**: `ContinuousOn.integrableOn_compact isCompact_Icc`
3. **Constant integrability**: `integrableOn_const.mpr (Or.inr (by simp [Real.volume_Icc]))`
4. **Monotone integral**: `setIntegral_mono_on hint hcint measurableSet_Icc hbdd`
5. **Constant integral = A.card**: `set_integral_const + smul_eq_mul + Real.volume_Icc + ENNReal.toReal_ofReal`

### L2_norm (OPEN — Parseval's theorem)

Mathematical proof:
1. `|∑_{n∈A} e(nθ)|² = ∑_{m,n∈A×A} e((m-n)θ)` via `Complex.normSq`
2. Interchange sum and integral (Fubini for finite sums)
3. `∫₀¹ e(kθ) dθ = δ_{k,0}`: 
   - k=0: trivial
   - k≠0: antiderivative = `exp(2πikθ)/(2πik)`, value = `(exp(2πik)-1)/(2πik) = 0`
4. `∑_{m,n∈A} δ_{m=n} = |A|`

**Estimated complexity**: 80-120 lines of Lean

## Key Mathlib APIs

| API | Purpose |
|-----|---------|
| `Complex.continuous_abs` | Continuity of complex norm |
| `continuous_finset_sum` | Finite sum of continuous functions |
| `ContinuousOn.integrableOn_compact` | Compact set + continuousOn = integrable |
| `setIntegral_mono_on` | Monotone set integral bounds |
| `set_integral_const` | Constant integral: `∫ c = (μ s).toReal • c` |
| `Real.volume_Icc` | Lebesgue measure of [a,b] = ofReal(b-a) |
| `ENNReal.toReal_ofReal` | `(ofReal r).toReal = r` for r ≥ 0 |

## Session 2026-04-23 (Session 1) — L1norm_upper_bound Proved

**Mode**: FRESH
**Outcome**: PROGRESS — SORRY 1 eliminated; 1 sorry remains (L2_norm)

### What I Did

1. Read the existing proof file (240 lines, 2 sorries)
2. Identified that `L1norm_upper_bound` was tractable via continuity + monotone integration
3. Applied the proof (already present in main repo from Aristotle integration `d6783713f0`)
4. Applied same proof to the worktree's feature branch

### Key Findings

**fun_prop** handles the continuity of `fun θ : ℝ => Complex.exp (2 * π * ↑n * θ * I)` (linear in θ, standard composition).

**setIntegral_mono_on** signature: `IntegrableOn f s → IntegrableOn g s → MeasurableSet s → (∀ x ∈ s, f x ≤ g x) → ∫ f ≤ ∫ g`

**Constant integral**: `set_integral_const` (snake_case, not camelCase) gives `∫ x in s, c = (μ s).toReal • c`.

### Files Modified

- `proofs/Proofs/Erdos512Problem.lean` (+28 lines: L1norm_upper_bound proved)

### Next Steps

1. **Prove L2_norm** (Parseval): ~80-120 lines via normSq expansion + character orthogonality
2. **Alternative**: Submit to Aristotle companion file
3. Character orthogonality: `∫₀¹ exp(2πikθ) dθ = 0` for k : ℤ, k≠0 — needs FTC + Complex.exp_int_mul_two_pi_mul_I

