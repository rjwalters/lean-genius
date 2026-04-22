# Knowledge Base: pascals-hexagon-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

### Session 3 (researcher-4, 2026-03-30)
- Proved `stdConicPoint_covers`: every point on stdConic with p₀+p₂≠0 is a scalar
  multiple of stdConicPoint(p₁/(p₀+p₂)) — uses half-angle substitution + conic equation
- Proved `stdConic_infinity_char`: if p₀+p₂=0 on stdConic, then p₁=0 (point is (1,0,-1))
- Added `stdConicInfinity` definition and `stdConicInfinity_on_conic` theorem
- Updated roadmap: 7 of ~10 steps complete, remaining are Sylvester + infinity case + assembly
- File stats: 581 lines, 11 theorems, 1 axiom, 27 defs, 0 sorries

---

### Session 4 (researcher-13, 2026-04-13)
- Proved `threeVectorMatrix_projTransform`: `det(M·u, M·v, M·w) = det(M) * det(u, v, w)` via matrix multiplication factorization `threeVectorMatrix (M·u) (M·v) (M·w) = threeVectorMatrix u v w * M.transpose`
- Proved `crossProduct_projTransform`: `cross(M·u, M·v) = adj(M)ᵀ · cross(u,v)` using `Matrix.adjugate_fin_three` explicit expansion + `ring` at `maxHeartbeats 2000000`
- Proved `projTransform_valid_of_det_ne_zero` helper via `Matrix.adjugate_mul` chain
- Eliminated 6 valid-transform sorries using the helper lemma
- Proved `pascal_std_conic` (all valid hexagons on stdConic satisfy Pascal constraint) via 22-case early-stop dispatch tree — NO backtracking search needed
- `pascal_std_conic_normalized`: key dispatch theorem routing to 7 single-vertex-infinity and 15 coincident-vertex lemmas
- Restructured from `all_goals first | exact ...` (timeout at 2M heartbeats) to explicit nested rcases with early-stop — O(1) per case, no search
- 1 sorry remaining: Sylvester's law only (was 8+ sorries at start of session)
- File: 1165 lines, 40 theorems, 1 axiom, 27 defs, 1 sorry (Sylvester's law)

---

### Session 5 (researcher-5, 2026-04-22)
- Added `import Mathlib.LinearAlgebra.QuadraticForm.Real` to PascalsHexagon.lean
- Proved `conicQF_eq_dotProduct`: `conicQuadraticForm C p = p ⬝ᵥ (C *ᵥ p)` via sum expansion
- Proved `mathlibQF_eq_dotProduct`: `Matrix.toQuadraticMap' C p = p ⬝ᵥ (C *ᵥ p)` via `toLinearMap₂'_apply'`
- Proved `conicQF_eq_mathlibQF`: bridge between our `conicQuadraticForm` and Mathlib's `Matrix.toQuadraticMap'`
- Proved `mathlibQF_separatingLeft`: for symmetric non-degenerate C, `(associated (toQuadraticMap' C)).SeparatingLeft`
  - Key chain: symmetry → `associated_left_inverse` gives `associated Q = toLinearMap₂' ℝ C`
  - Then `nondegenerate_of_det_ne_zero + Nondegenerate.toLinearMap₂'`
- Updated `proof_sketch_conic_implies_pascal` to add `hC_sym : C.symmetric` and `hC_nd : Conic.nondegenerate C`
  - Without these, the statement is FALSE for degenerate/asymmetric conics
- Documented complete proof plan for remaining sorry (matrix extraction + 6-case weight analysis ~100 lines)
- File: 1278 lines, 1 axiom, 1 sorry (HARD: Sylvester matrix extraction)

---

## Dead Ends

- Mathlib lacks Bezout/Cayley-Bacharach — must use direct algebraic approach
- Proving Sylvester's law fully from scratch may be ~200-300 lines
- `all_goals first | exact lemma _ _ _ _ _` with 22 alternatives on 63 goals times out at 2M heartbeats; must use explicit nested case tree instead
