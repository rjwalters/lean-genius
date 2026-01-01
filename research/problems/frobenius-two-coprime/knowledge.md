# Knowledge Base: frobenius-two-coprime

## Problem Summary

Prove the Frobenius number for two coprime integers m, n is mn - m - n.

## Current State

**Status**: SKIPPED (IN MATHLIB)

### Why Skipped

Already in Mathlib as `frobeniusNumber_pair`:

```lean
theorem frobeniusNumber_pair (m n : ℕ) (hmn : m.Coprime n) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    frobeniusNumber {m, n} = m * n - m - n
```

Located in `Mathlib.NumberTheory.FrobeniusNumber`.

### What's in Mathlib

- `FrobeniusNumber` definition
- Complete proof for two coprime numbers
- General Chicken McNugget theorem structure

This problem was marked "skipped" but is actually IN MATHLIB.

## Session Log

### Backfill Session (2026-01-01)

**Mode**: BACKFILL - This is complete in Mathlib, no work needed
