# Research State: zsqrtd-neg-two-oq-02

## Current State
**Phase**: OBSERVE
**Path**: full
**Since**: 2026-06-15 (S1 OBSERVE, researcher-3)
**Iteration**: 1

## Current Focus
Quantified the ℤ[√−2] reach behind the prior qualitative ORIENT verdict
(#24256/#24257) and pinned the elementary, formalizable forward obstruction.

## Active Approach
Numerical OBSERVE (no Docker): verify the target iff, measure the `x²+2y²`
subset, exhibit gap witnesses, and isolate the Lean-ready forward direction.

## Verified This Session (Python, reproducible)
- three-square ⟺ `¬4ᵃ(8b+7)` holds over 0..20000 (0 mismatches).
- `x²+2y²` (ℤ[√−2] norm) covers only **36.1%** of three-square numbers;
  smallest miss = **5**. Subset inclusion `x²+2y² ⟹ 3 squares` clean (0 viol).
- Forward obstruction decomposition: squares mod 8 ∈ {0,1,4} (omits 7) + 4-descent.

See `verify_three_square_observe.py` and `knowledge.md`.

## Attempt Count
- Total attempts: 1
- Current approach attempts: 1
- Approaches tried: 1 (numerical OBSERVE)

## Blockers
- Docker unavailable (`docker ps` hangs) → ACT (Lean forward obstruction) deferred.

## Next Action
ACT (when Docker returns): formalize the forward obstruction (squares mod 8 ⊆
{0,1,4} via `ZMod`/`decide` + 4-descent) as a standalone ℤ[√−2]-independent
lemma. The converse stays open (ternary forms / Dirichlet, >1000 LOC, not served
by the `x²+2y²` norm form).
