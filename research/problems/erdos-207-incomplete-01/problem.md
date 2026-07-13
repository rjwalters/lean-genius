# Problem: Erdős #207: High-Girth Steiner Triple Systems — Complete 2 sorries

**Slug**: erdos-207-incomplete-01
**Created**: 2026-04-03
**Status**: Active
**Source**: gallery-gap

## Problem Statement

**Lean file**: `proofs/Proofs/Erdos207Problem.lean`

Two sorries:
1. `sts_has_girth_at_least_2`: Every STS has girth ≥ 2
   - Comment: trivial — STS has no repeated triples/edges

2. `girth_3_iff_pasch_free`: STS has girth ≥ 3 ↔ it is Pasch-free
   - This is a characterization theorem

## Context

A Steiner Triple System (STS) on V is a collection of 3-element subsets such that
every pair is in exactly one triple. `girth` is the shortest linear cycle.

## Approach

For `sts_has_girth_at_least_2`: use that each pair appears in exactly 1 triple,
so no pair appears twice (no girth-2 cycle).

For `girth_3_iff_pasch_free`: this requires understanding the Pasch configuration
and showing that girth-3 cycles correspond exactly to Pasch configurations.

## Tractability: CHALLENGING
