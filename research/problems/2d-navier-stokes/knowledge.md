# Knowledge Base: 2d-navier-stokes

## Problem Summary

Prove existence and regularity for 2D Navier-Stokes equations.

## Current State

**Status**: SKIPPED

### Why Skipped

No PDE infrastructure in Mathlib. Would require defining Navier-Stokes equations, Sobolev spaces, and weak solutions from scratch.

### What Would Be Needed

1. Sobolev space H^s definitions
2. Weak solution framework
3. 2D NS equation formulation
4. Energy estimates for 2D case
5. Regularity theory

### Related Work

- `NavierStokes.lean` - Has 3D Millennium Prize statement as axiom
- 2D case is actually solvable (unlike 3D) but infrastructure is missing

### Key Difference from 3D

2D Navier-Stokes has global regularity (Ladyzhenskaya 1959). This is NOT a Millennium Prize problem - only 3D is open.

## Session Log

### Backfill Session (2026-01-01)

**Mode**: BACKFILL - Skipped problem documentation
