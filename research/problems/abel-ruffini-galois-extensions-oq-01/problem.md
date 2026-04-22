# Problem: Explicit Quintic Unsolvability via S₅ Construction

**Slug**: abel-ruffini-galois-extensions-oq-01
**Created**: 2026-04-22
**Status**: Active
**Source**: gallery-gap
**Tier**: A
**Significance**: 7/10
**Tractability**: 6/10

## Problem Statement

### Formal Statement

Construct a specific degree-5 polynomial with Galois group S₅ in Lean 4, thereby formalizing an explicit instance of quintic unsolvability by radicals.

Specifically:
- Exhibit a concrete polynomial `p : Polynomial ℚ` of degree 5
- Prove `IsSolvableByRad ℚ (p.IsRootOf) → False` (or equivalent)
- Or show its Galois group is isomorphic to S₅ (non-solvable)

### Plain Language

The gallery entry `abel-ruffini-galois-extensions` proves the abstract framework: S_n is solvable iff n ≤ 4, and A₅ is simple. But it does not exhibit a *concrete* quintic whose Galois group is S₅. This problem asks for that explicit construction.

A classical candidate is `x⁵ - 5x + 12` (three real roots + two complex roots → discriminant argument → Galois group = S₅). Another is `x⁵ - 4x + 2` (Eisenstein + real root count).

### Why This Matters

- Provides a concrete witness to Abel-Ruffini, not just an abstract impossibility proof
- Demonstrates that Mathlib's Galois group API can compute Galois groups of specific polynomials
- Teaches the proof technique: irreducibility (Eisenstein) + real root count + cycle type → Galois group = S₅

## Known Results

### What's Already Proven (in `AbelRuffiniGaloisExtensions.lean`)

- S_n not solvable for n ≥ 5: `Equiv.Perm.not_solvable`
- A₅ is simple
- Sharp threshold: S_n solvable iff n ≤ 4
- `solvableByRad.isSolvable'`: radical solvability ⟹ solvable Galois group (contrapositive available)

### Key Mathlib APIs

- `Polynomial.Irreducible` via Eisenstein criterion: `Polynomial.irreducible_of_eisenstein_criterion`
- `galoisGroup p` (if available in Mathlib) or build via splitting field
- `IsSolvableByRad` and `solvableByRad.isSolvable'`
- `Equiv.Perm.not_solvable` for the solvability obstruction

### What's Still Open

- Does Mathlib have infrastructure to compute/verify Galois groups of specific polynomials?
- Can the discriminant or resolvent approach be formalized for the Galois group = S₅ claim?
- The hard part: proving a specific poly has all transpositions and 5-cycles in its Galois group

## Approach Ideas

### Approach 1: Eisenstein + Real Root Count (Classical)

For `p = X^5 - 4*X + 2`:
1. Eisenstein at p=2: irreducible over ℚ
2. Count real roots: p'(x) = 5x⁴ - 4 = 0 → x = ±(4/5)^(1/4). Three real roots (min, max, one more) since p is degree 5 → complex conjugate roots → complex automorphism gives transposition
3. Degree-5 irreducible polynomial → Galois group contains 5-cycle
4. Transposition + 5-cycle in subgroup of S₅ → generates S₅

### Approach 2: Use Mathlib's AbelRuffini theorem directly

Check if `Polynomial.AbelRuffini` or `solvableByRad` in Mathlib has instances for specific polynomials.

### Approach 3: Softer formalization

Formalize the STATEMENT that S₅ Galois group implies unsolvability (connecting the abstract result to a concrete polynomial existence), without computing the Galois group computationally.

## Related Gallery Proofs

- `abel-ruffini-galois-extensions`: Parent proof (S_n threshold, A₅ simple) — 0 sorries, fully verified
- `abel-ruffini-oq-04`: Abel-Ruffini via solvable groups
- `abel-ruffini-oq-04-oq-01`: Further extensions

## First Steps for Researcher

1. **OBSERVE**: Check `proofs/Proofs/AbelRuffiniGaloisExtensions.lean` for available lemmas. Search Mathlib for `galoisGroup`, `IsSolvableByRad`, `Polynomial.Irreducible` APIs.
2. **ORIENT**: Scout Mathlib for `Polynomial.galoisGroup` or splitting field computation for degree-5 polys. Check if there's existing Mathlib infrastructure for S₅ Galois group verification.
3. **DECIDE**: If Mathlib has `galoisGroup` API: formalize Eisenstein + root count → Galois = S₅. If not: formalize the weaker statement that the abstract Abel-Ruffini machinery applies to `x⁵ - 4x + 2` once its Galois group is assumed.
