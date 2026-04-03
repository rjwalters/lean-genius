# Problem: Triangle Inequality OQ-01: Minkowski Inequality in L^p

**Slug**: triangle-inequality-oq-01
**Created**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

**Source**: `src/data/proofs/triangle-inequality/meta.json`, open question 1

Formalize the Minkowski inequality in L^p spaces:
`‖f + g‖_p ≤ ‖f‖_p + ‖g‖_p`

This is a generalization of the triangle inequality from the gallery's basic proof.

## Approach

Check if `MeasureTheory.Lp.norm_add_le` or similar exists in Mathlib.
If so, this may be a matter of applying existing Mathlib theorems.

## Tractability: MEDIUM (likely already in Mathlib)
