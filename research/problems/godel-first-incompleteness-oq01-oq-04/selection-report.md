# Selection Report: godel-first-incompleteness-oq01-oq-04

**Date**: 2026-05-03
**Selected by**: Seeker
**Composite Score**: 8040 (Tier B, sig=8, tract=4, knowledge=EMPTY)

## Problem
Gödel Incompleteness: Diagonal Lemma Formalization in Lean 4

Formalize the Diagonal Lemma (Fixed-Point Lemma) in Lean 4 without additional axioms.
This reduces the existing gallery proof's axiom count from 5 to 2 by constructing the
syntactic infrastructure for Gödelization computably.

## Selection Rationale

1. **Unique domain** — Logic/foundations not well-represented in the current available pool
2. **Concrete value** — Directly improves an existing gallery proof (reduces axiomCount 5→2)
3. **Tractable scope** — Targeted to Peano arithmetic diagonal only; Flypitch shows feasibility

## Suggested First Steps

1. Survey `Mathlib.Logic.Godel` for existing encoding infrastructure
2. Check Flypitch project (lean-fopl) for reusable syntax types
3. Attempt inductive `Formula` type + `subst` function; prove diagonal property

## Pool Context

Part of a 10-problem batch selection to buffer the pool from 17→27 available.
