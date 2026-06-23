# Problem: Cauchy-Schwarz Integral OQ-04: Heisenberg Uncertainty Principle

**Slug**: cauchy-schwarz-integral-oq-04
**Created**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

**Source**: `src/data/proofs/cauchy-schwarz-integral/meta.json`, open question 4

Can the Heisenberg uncertainty principle `Δx · Δp ≥ ℏ/2` be formalized as a derivable
consequence of the Cauchy-Schwarz inequality in L2?

## Mathematical Context

The Heisenberg uncertainty inequality:
- `⟨x²⟩ · ⟨p²⟩ ≥ (1/4) · |⟨[x,p]⟩|²`
- For quantum mechanics: `⟨ψ|x²|ψ⟩ · ⟨ψ|p²|ψ⟩ ≥ (1/4) · |⟨ψ|[x,p]|ψ⟩|²`

The proof derives from Cauchy-Schwarz in L2:
1. `|⟨f,g⟩|² ≤ ‖f‖² · ‖g‖²`
2. With `f = x·ψ` and `g = ∂ψ/∂x`
3. The commutator `[x, p] = iℏ` contributes the RHS

## Approach

This is a substantial formalization involving:
- L2 function spaces
- Fourier analysis / momentum operator as derivative
- Integration by parts

**Mathlib support**: `MeasureTheory.inner_mul_le_norm_mul_iff`, L2 spaces

## Tractability: CHALLENGING
