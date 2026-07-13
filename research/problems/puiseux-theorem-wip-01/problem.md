# Problem: Complete Puiseux's Theorem — Replace True-Stub Theorems

**Slug**: puiseux-theorem-wip-01
**Created**: 2026-04-21
**Status**: Active
**Source**: gallery-wip

## Problem Statement

### Plain Language

`PuiseuxTheorem.lean` (Wiedijk #41) has `badge: "wip"` because 5 main theorems are
implemented as `True`-stubs — they prove `True` instead of the actual mathematical
content. These need to be replaced with real Lean proofs or `sorry` statements for
Aristotle/Researcher to complete.

### The 5 True-Stubs

```lean
-- Replace each `by exact True.intro` / `by trivial` with actual proof:
theorem puiseux_theorem : ...           -- Algebraic closure of Laurent series
theorem puiseux_is_algebraic_closure : ... -- IsAlgClosed of Puiseux series field
theorem newton_puiseux_terminates : ... -- Newton polygon algorithm terminates
theorem square_root_puiseux : ...       -- √z has a Puiseux expansion
theorem cusp_parameterization : ...     -- Cusp curve t ↦ (t², t³) is a branch
```

### Why This Matters

Puiseux's theorem is Wiedijk #41 and foundational to algebraic geometry and singularity
theory. A proper Lean formalization (not just True-stubs) would be a genuine contribution.
The `IsPuiseuxSeries` predicate and `leadingExponentFromSlope` function are already
defined — the stubs just need actual proofs.

## Known Results

### What's Already Proven

- `IsPuiseuxSeries` predicate for Hahn series with rational exponents
- `leadingExponentFromSlope` for Newton polygon slopes
- `PuiseuxField` and `LaurentField` as HahnSeries instances
- Characteristic zero requirement via Artin-Schreier counterexample
- Galois group Gal(Puiseux/Laurent) ≅ Ẑ described structurally

### Our Goal

Replace the 5 True-stubs with either:
- Proper `sorry` + Aristotle-compatible formulation (short-term), or
- Actual Lean proofs using Mathlib's `IsAlgClosed`, `HahnSeries`, `PowerSeries`

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| puiseux-theorem | Source file with WIP stubs | HahnSeries, IsAlgClosed |

## Initial Thoughts

### Potential Approaches

1. **Convert to sorry for Aristotle**: Replace `True.intro` stubs with `sorry`,
   submit to Aristotle, see which ones close automatically
   - Risk: Main theorems may be too complex for Aristotle

2. **Prove cusp_parameterization first**: This is likely the most concrete
   (`t ↦ (t², t³)` is a Puiseux series) and good for establishing patterns
   - Why: The parametrization proof should be straightforward with HahnSeries

3. **Mathlib path for IsAlgClosed**: Search for `HahnSeries.isAlgClosed` or similar
   - Mathlib has `IsAlgClosed.algebraicClosure` but not necessarily for Laurent series

### Key Difficulties

- `puiseux_theorem` (algebraic closure) may require substantial algebra machinery
- Connecting `PuiseuxField` (HahnSeries over ℚ) to `IsAlgClosed` predicate

## Tractability Assessment

**Difficulty**: Medium

**Justification**:
- Infrastructure is built; only stubs remain
- `cusp_parameterization` and `square_root_puiseux` are tractable
- `puiseux_is_algebraic_closure` is the hardest — may need axiom

## Metadata

```yaml
tags:
  - algebra
  - field-theory
  - hahn-series
  - wiedijk-100
  - completion
  - wip
related_proofs:
  - puiseux-theorem
difficulty: medium
source: gallery-wip
created: 2026-04-21
```

**Significance**: 8/10
**Tractability**: 5/10
