# Problem: Hurwitz Only-If: Clifford Algebra Proof

**Slug**: hurwitz-theorem-oq-03-oq-01
**Created**: 2026-04-21
**Status**: Active
**Source**: gallery-extension

## Problem Statement

### Plain Language

The gallery proof `HurwitzTheorem.lean` formalizes Hurwitz's theorem (1898): a
normed division algebra over ℝ must have dimension 1, 2, 4, or 8. The parent open
question (`hurwitz-theorem-oq-03`) concerned the `only_if` direction — proving that
no normed division algebra of dimension ≠ 1, 2, 4, 8 exists.

This sub-question asks:

**Can `hurwitz_only_if` be proved via Clifford algebra theory and representation
of norm-preserving multiplications in Lean 4?**

The key step in the classical proof:
1. A normed algebra N of dimension n satisfies: left-multiplication L_x : N → N
   is norm-preserving when |x| = 1
2. The map x ↦ L_x gives a linear representation of the sphere Sⁿ⁻¹
3. Using Clifford algebra arguments (Radon-Hurwitz numbers), this forces n ∈ {1,2,4,8}

### Formal Context

The parent proof already handles the `if` direction (constructing ℝ, ℂ, ℍ, 𝕆 as
normed division algebras). The `only_if` direction is the hard part.

```lean
-- Goal:
theorem hurwitz_only_if (N : Type*) [NormedDivisionAlgebra N] :
    Module.finrank ℝ N ∈ ({1, 2, 4, 8} : Set ℕ) := by sorry

-- Key sub-lemma:
theorem multiplication_gives_clifford_rep (N : Type*) [NormedDivisionAlgebra N]
    (n := Module.finrank ℝ N) :
    ∃ ρ : CliffordAlgebra (standardForm n) →ₐ[ℝ] (N →L[ℝ] N),
      Function.Injective ρ.toLinearMap := by sorry
```

### Why This Matters

- Hurwitz's theorem is one of the landmark results in algebra
- The Clifford algebra approach is the most conceptual proof
- Connects to K-theory, Bott periodicity, and the Hopf invariant one problem
- Completing the formalization achieves a fully machine-checked proof of Hurwitz's theorem

## Known Results

### From Gallery Proof (`HurwitzTheorem.lean`)

The `hurwitz-theorem` gallery entry shows:
- The 4 open questions include "Can the n=3 impossibility proof be shortened using
  Clifford algebras?" and "Is there a uniform proof for all n ∉ {1,2,4,8}?"
- The `hurwitz-theorem-oq-03` completed result: The n=8 octonion identity is proved
  constructively via explicit Cayley-Dickson multiplication

### Mathematical Background

**Radon-Hurwitz numbers**: The Clifford algebra Cl(n) of ℝⁿ with standard quadratic
form has a real representation of dimension ρ(n), where ρ is the Radon-Hurwitz number.
A normed division algebra of dimension n requires Cl(n-1) to have a real representation
of dimension n. This forces n | ρ(n) · 2^(floor(n/2)), which holds only for n ∈ {1,2,4,8}.

**Lean 4 Status**:
- `Mathlib.LinearAlgebra.CliffordAlgebra.Basic`: Core Clifford algebra
- Clifford algebra representations: partially available
- Division algebra axioms: `NormedDivisionAlgebra` typeclass exists

## Suggested Approach

### Phase 1: OBSERVE
1. Read `HurwitzTheorem.lean` to understand what's already proved
2. Check `Mathlib.LinearAlgebra.CliffordAlgebra` for available results
3. Check if `NormedDivisionAlgebra` → norm-preserving left multiplication is in Mathlib

### Phase 2: ORIENT
1. Survey the Clifford algebra library in Mathlib
2. Determine if Radon-Hurwitz numbers are formalized
3. Assess whether a simplified version (just n=3 impossibility) is tractable

### Phase 3: DECIDE
Options by difficulty:
- **Hard**: Full `hurwitz_only_if` via Clifford algebras (months of work)
- **Easier**: Prove n=3 impossibility using a simpler argument (quaternion uniqueness)
- **Tractable**: Establish the norm-preserving multiplication lemma as a standalone result

If the full proof is out of reach, aim for the n=3 impossibility as a first step.

### Phase 4: ACT
Start with:
```lean
-- Left multiplication is isometric for unit elements
theorem norm_mul_left (N : Type*) [NormedDivisionAlgebra N] (x y : N) :
    ‖x * y‖ = ‖x‖ * ‖y‖ := norm_mul x y

-- For unit sphere, L_x is norm-preserving linear map
theorem unit_left_mul_isometry (N : Type*) [NormedDivisionAlgebra N] 
    (x : N) (hx : ‖x‖ = 1) : Isometry (· * x) := by
  ...
```

## Related Gallery Proofs

- `hurwitz-theorem`: Parent proof — the main Hurwitz theorem formalization
- `cayley-hamilton-minpoly`: Uses similar algebra representation techniques
- `borsuk-ulam`: K-theory connections (deep link via Hopf invariant one)

## Quality Assessment

- **Tractability**: 5/10 — needs Clifford algebra infrastructure; full proof is hard
- **Significance**: 8/10 — fundamental algebraic result, Hopf invariant connection
- **Domain**: Algebra / normed division algebras
- **Risk**: High — may need to scope down to a tractable sub-lemma
