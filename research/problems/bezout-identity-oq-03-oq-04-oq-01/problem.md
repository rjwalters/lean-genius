# Problem: CRT Generalization to Arbitrary Commutative Rings

**Slug**: bezout-identity-oq-03-oq-04-oq-01
**Created**: 2026-04-04T02:46:57-07:00
**Status**: Active
**Source**: bezout-identity-oq-03-oq-04 <!-- gallery-gap -->

## Problem Statement

Can `crtDirect` be generalized to arbitrary commutative rings (beyond ℤ) where Bézout's identity holds? Lean's type class system should support this via `IsBezout` or `GCDMonoid`.

The goal is a polymorphic CRT: given coprime ideals I₁,...,Iₙ in a Bézout ring R, the canonical map R/∩Iᵢ → ∏R/Iᵢ is an isomorphism.

## Context

- Source: `bezout-identity-oq-03-oq-04` (Efficient Verified CRT via Direct Bézout)
- Category: generalization (algebra / ring theory)
- Tractability: challenging (type class generalization in Lean 4)

## First Steps

1. Find `IsBezout` type class in Mathlib
2. Check if `ChineseRemainderTheorem` already exists in Mathlib
3. Abstract the ℤ-specific crtDirect proof
