# Problem: Cauchy-Crofton Formula for General Convex Bodies

**Slug**: buffons-needle-oq-01-oq-02-oq-01
**Created**: 2026-04-04T02:46:57-07:00
**Status**: Active
**Source**: buffons-needle-oq-01-oq-02 <!-- gallery-gap -->

## Problem Statement

Can the Cauchy-Crofton formula be fully formalized in Lean for general convex bodies?

The formula states: for a convex body K in ℝⁿ, the expected number of intersections
of a random line with ∂K equals 2·Vol_{n-1}(∂K) / ωₙ₋₁ where ωₙ₋₁ is the volume
of the (n-1)-sphere.

## Context

- Source: `buffons-needle-oq-01-oq-02` (Buffon's Needle: Higher-Dimensional Hyperplane Arrangements)
- Category: extension (geometric probability / integral geometry)
- Tractability: challenging (requires measure theory on spaces of lines)

## First Steps

1. Survey Mathlib for kinematic formula / measure on lines (Grassmannians)
2. Check integral geometry literature for Lean-friendly formulations
3. Start with 2D case (original Buffon formula for convex curves)
