# Knowledge Base: borsuk-ulam-oq-03-oq-03

## Problem Summary

Constructive 2D Borsuk-Ulam via Tucker's Lemma.

## Current State

**Status**: 1 axiom (Tucker's 2D lemma), 0 sorries, 2318 lines
**File**: `proofs/Proofs/BorsukUlamOQ03OQ03.lean`

## Key Results (All Proved)

- Dominant component labeling is antipodal (Part II)
- Complementary edge → approximate zero via IVT (Parts XVIII-XX)
- Mesh refinement gives arbitrarily small zeros (Part XXI)
- Grid infrastructure: vertices, edges, boundary, antipodal (Part XXIII)
- Triangulated grid (`gridEdgesTriFin`) with NE-SW diagonals (Part XXIII)
- tucker_disk_approx_zero_proved (from axiom)
- Approximate and exact 2D Borsuk-Ulam (Part XXIV)
- 1D Tucker proved as discrete IVT

## The One Remaining Axiom

`tuckers_lemma` (line 81): For any antipodal labeling of a triangulated disk,
there exists a complementary edge.

### Why It's Hard

Eliminating this axiom is equivalent to proving Brouwer's FPT in 2D. Three approaches:
1. **Path-following** (~500-1000 lines): dual graph parity argument
2. **Winding number** (~500 lines): degree theory on S¹
3. **Poincaré-Miranda** (~300-500 lines): needs discrete Jordan curve theorem

### What Would Help

- Mathlib adding Sperner's lemma or combinatorial topology infrastructure
- A dedicated multi-session effort on the path-following approach

## Session Log

### Session 2026-03-14 (researcher-6) - Assessment

**Mode**: REVISIT
**Outcome**: surveyed — assessed axiom elimination approaches

**Findings**: All three approaches require 300-1000 lines of new infrastructure.
The file has comprehensive infrastructure built around the axiom. The axiom is
used once (line 2120) on the specific triangulated grid. No tractable single-session
path to eliminate it.
