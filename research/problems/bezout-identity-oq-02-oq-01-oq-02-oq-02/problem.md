# Problem: Gaussian Integers as Euclidean Domain in Lean

**Slug**: bezout-identity-oq-02-oq-01-oq-02-oq-02
**Created**: 2026-04-04T02:46:57-07:00
**Status**: Active
**Source**: bezout-identity-oq-02-oq-01-oq-02 <!-- gallery-gap -->

## Problem Statement

The Gaussian integers ℤ[i] form a Euclidean domain with Euclidean function N(a+bi) = a²+b².
Is there a gallery proof formalizing unique factorization in ℤ[i], including characterization of Gaussian primes?

A prime p ∈ ℤ remains prime in ℤ[i] iff p ≡ 3 (mod 4); otherwise p splits as p = π·π̄.

## Context

- Source: `bezout-identity-oq-02-oq-01-oq-02` (FTA Generalization to Euclidean Domains)
- Category: extension (algebra / number theory)
- Tractability: challenging (Mathlib.NumberTheory.GaussianInt exists — check coverage)

## First Steps

1. Check `Mathlib.NumberTheory.GaussianInt` for existing coverage
2. Identify gaps (Gaussian prime characterization, UFD proof)
3. Build on existing Mathlib Gaussian integer infrastructure
