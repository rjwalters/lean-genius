# Explicit Quintic Unsolvability via S₅ Galois Group

## Problem Statement

Construct a specific degree-5 polynomial over ℚ and prove in Lean 4 that its Galois group is isomorphic to S₅, thereby giving a concrete example of a polynomial not solvable by radicals.

## Context

The parent proof `AbelRuffiniGaloisExtensions.lean` establishes the abstract theory:
- S_n is solvable iff n ≤ 4
- A₅ is simple (the obstruction)
- If Gal(f) is not solvable, then f is not solvable by radicals

What's missing is the **constructive direction**: exhibiting a specific polynomial whose Galois group is S₅.

## Classical Approach

Standard candidates include:
- `x⁵ - 4x + 2` (irreducible by Eisenstein at p=2, exactly two complex roots → Galois group is S₅)
- `x⁵ - x - 1` (similar analysis)
- `x⁵ - 6x + 3` (Eisenstein at p=3)

The classical proof strategy for showing Gal(f/ℚ) ≅ S₅:
1. Show f is irreducible over ℚ (e.g., Eisenstein criterion)
2. Show f has exactly 3 real roots and 2 complex conjugate roots (intermediate value theorem + calculus)
3. Complex conjugation gives a transposition in Gal(f)
4. Irreducibility gives a 5-cycle (since |Gal(f)| is divisible by 5)
5. A transposition and a p-cycle generate S_p for p prime

## Mathlib Resources

- `Polynomial.IsIrreducible` — irreducibility predicates
- `Polynomial.IrreducibleOfEisensteinAt` — Eisenstein criterion
- `Mathlib.FieldTheory.Galois` — Galois group infrastructure
- `Equiv.Perm` — permutation group theory
- `Mathlib.FieldTheory.AbelRuffini` — not solvable by radicals

## Formalization Challenges

- Computing Galois groups explicitly in Lean is nontrivial
- May need to work with splitting fields concretely
- The "count real roots" argument requires real analysis
- Alternative: use discriminant + Eisenstein to characterize the group

## Success Criteria

- Define a specific polynomial (e.g., `X^5 - 4*X + 2 : ℚ[X]`)
- Prove its Galois group is isomorphic to `Equiv.Perm (Fin 5)`
- Connect to the parent proof's `not_solvable_by_rad` result
- Result: a fully concrete theorem "this specific polynomial is not solvable by radicals"
