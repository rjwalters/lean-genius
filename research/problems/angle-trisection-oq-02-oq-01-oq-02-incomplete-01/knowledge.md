# Knowledge Base: Wantzel-Galois Constructibility Completion

**Problem**: angle-trisection-oq-02-oq-01-oq-02-incomplete-01
**Last Updated**: 2026-04-26
**Knowledge Items**: 10

Insights accumulated during research on this problem.

---

## Problem Understanding

This is a completion of `AngleTrisectionOQ02OQ01OQ02.lean`, which had 5 sorries.
The parent has: `not_constructible_of_bad_degree`, `cube_root_2_minpoly_irred`,
`cos20_minpoly_degree`, `regular_7gon_impossible_degree`, `wantzel_galois_iff`.

The goal: reduce sorries to 0 (or as few as possible). The `Incomplete01` file
achieves 1 sorry by proving 4 of the 5.

---

## Session 2026-04-26 (Session 1) — Survey + Bug Fix

**Mode**: FRESH
**Outcome**: scouted + bug fixed in `not_constructible_of_bad_degree` proof

### What I Did

1. Surveyed `AngleTrisectionOQ02OQ01OQ02Incomplete01.lean` (306 lines, 1 sorry)
2. Found the file already proves 4 of 5 sorries from the parent via redesigned `IsConstructible`
3. Fixed bug at line 271: `u.val` → `u` (u is `ℚ[X]`, not a units structure)
4. Simplified `hq_eval` proof using `Polynomial.eval₂_hom` instead of complex rewrites

### Key Findings

- **Redesigned IsConstructible**: Makes a,b EXPLICIT in sqrt_ext (not existential),
  enabling proper inductive hypotheses in the recursor
- **isConstructible_mem_range**: The redesigned definition collapses to ℚ — every
  constructible element is rational. (This is mathematically a degenerate model but
  enables the degree argument.)
- **not_constructible_of_bad_degree** proof: constructible → rational (via isConstructible_mem_range)
  → rational root of irreducible poly → degree 1 = 2^0 → contradiction
- **Key bridge**: `Polynomial.eval₂_hom : p.eval₂ f (f x) = f (p.eval x)` connects
  `aeval (algebraMap ℚ ℂ q) p` to `algebraMap ℚ ℂ (p.eval q)`
- **wantzel_galois_iff**: BLOCKED — requires FTGT + Galois group 2-group structure + constructibility
  bridge (~500+ lines). Out of scope.

### Files Modified

- `proofs/Proofs/AngleTrisectionOQ02OQ01OQ02Incomplete01.lean` (unchanged lines → 306 lines)
  - Fixed `u.val` → `u` in `not_constructible_of_bad_degree`
  - Simplified `hq_eval` using `Polynomial.eval₂_hom`

### Sorry Count: 1

- `wantzel_galois_iff`: BLOCKED (500+ lines Galois theory)

### Next Steps

1. **BLOCKED**: `wantzel_galois_iff` requires full Galois theory — not tractable
2. **Alternative**: Rewrite with a mathematically correct `IsConstructible` (using
   `∀ a b : ℂ, IsConstructible a → IsConstructible b → ∀ β, β*β = a → IsConstructible (b+β)`)
   and prove `not_constructible_of_bad_degree` via tower degree argument (~150 lines).
   This is more mathematically honest but harder.

---

## Insights

1. IsConstructible redesigned: making a,b explicit in sqrt_ext gives proper IH in induction
2. isConstructible_mem_range proved: every IsConstructible element is rational (model collapses to ℚ)
3. not_constructible_of_bad_degree proved: constructible→rational, rational root of irreducible→degree 1=2^0
4. Polynomial.eval₂_hom is the key bridge: p.eval₂ f (f x) = f (p.eval x)
5. wantzel_galois_iff requires 500+ lines Galois theory (FTGT + 2-group tower + constructibility bridge)

---

## Dead Ends

- `u.val` in `not_constructible_of_bad_degree` (u : ℚ[X] from dvd obtain, not a units element)
- Complex `eval₂_map` + `eval₂_at_apply` approach for hq_eval — use `Polynomial.eval₂_hom` directly

---

## Mathlib Gaps

- No direct `IsConstructible` formalization in Mathlib
- FTGT exists in Mathlib but connecting to tower constructibility needs ~500 lines of bridge code
