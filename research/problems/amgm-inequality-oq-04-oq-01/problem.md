# Problem: Elliptic Integral K(k) Definition in Lean via Mathlib

**Slug**: amgm-inequality-oq-04-oq-01
**Created**: 2026-04-04T02:46:36-07:00
**Status**: Active
**Source**: amgm-inequality-oq-04 <!-- gallery-gap -->

## Problem Statement

Define K(k) = ∫₀^{π/2} dθ/√(1-k²sin²θ) in Lean using Mathlib's intervalIntegral and prove its basic properties: K(0)=π/2, K is increasing on [0,1), and K→∞ as k→1⁻.

This is the first step toward formalizing the Gauss AGM connection to elliptic integrals.

## Context

- Source: `amgm-inequality-oq-04` (Gauss AGM Iteration and Elliptic Integrals)
- Category: extension (analysis / special functions)
- Tractability: challenging (requires Mathlib.Analysis.SpecialFunctions.Integrals)

## First Steps

1. Search Mathlib for existing elliptic integral definitions
2. Try defining K(k) using `MeasureTheory.intervalIntegral`
3. Prove K(0) = π/2 as warm-up
