# Erdős Problem #214: Unit Distance Free Sets and Unit Squares

**Lean file**: `proofs/Proofs/Erdos214Problem.lean`
**Sorries**: 1
**Status**: available
**Tier**: B | **Significance**: 7/10 | **Tractability**: 4/10

## Problem Statement

Erdős #214: Can every set A ⊆ ℝ² with |A| = n contain a unit square? What is the maximum size of a unit-distance-free set?

## The Sorry

```lean
theorem unit_square_exists_in_set (S : Finset (ℝ × ℝ)) (hS : ¬IsUnitDistanceFree S) :
    ∃ a b c d : ℝ × ℝ, a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ d ∈ S ∧ IsUnitSquare a b c d := by
  intro hStrong S hFree
  -- A unit square is a particular 4-point configuration
  -- Apply Juhász's stronger theorem
  sorry
```

**Context**: The sorry appeals to "Juhász's stronger theorem" about unit squares. This is a result about incidence geometry.

## Mathematical Content

This is about the relationship between unit-distance-free sets and unit squares. If a set is NOT unit-distance-free (has some unit-distance pair), does it contain a full unit square? This requires the structure of unit-distance configurations.

## Approach

1. Read `Erdos214Problem.lean` fully
2. Find the definition of `IsUnitDistanceFree` and `IsUnitSquare`
3. Check if Juhász's theorem is stated elsewhere in the file as an axiom
4. Look for simpler geometric lemmas that might suffice

## Challenge

"Juhász's stronger theorem" may not be formalized. The sorry might need:
- Either use an axiom that's already stated
- Or find a direct geometric argument for the special case

## Related Gallery Proof

- `src/data/proofs/erdos-214/` — Erdős Problem #214
- `proofs/Proofs/Erdos214Problem.lean` — file with sorry

## First Steps (OBSERVE phase)

1. Read `Erdos214Problem.lean` fully
2. Is "Juhász's theorem" axiomatized in the file? If yes, apply it.
3. What is the exact type of the sorry goal?
4. Check if a simpler direct geometric argument works
