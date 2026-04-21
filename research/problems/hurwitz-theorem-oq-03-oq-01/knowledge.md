# Knowledge: hurwitz-theorem-oq-03-oq-01

## Key Facts

### Mathematical Background
- **Hurwitz's theorem** (1898): Only normed division algebras over ℝ are ℝ, ℂ, ℍ, 𝕆
- **Clifford algebra approach**: Cl(n-1) = Clifford algebra of ℝⁿ⁻¹ with standard form
- **Radon-Hurwitz numbers**: ρ(n) = number of independent unit vectors in Cl(n-1) real rep
- **Key constraint**: A normed division algebra of dimension n requires n | 2^⌊n/2⌋ · ρ(n)
  → This holds only for n ∈ {1, 2, 4, 8}

### Radon-Hurwitz Numbers
| n | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | ... |
|---|---|---|---|---|---|---|---|---|---|-----|
| ρ(n) | 1 | 2 | 2 | 4 | 4 | 4 | 4 | 8 | 9 | ... |

### Lean 4 Status (updated 2026-04-21)
- `Mathlib.LinearAlgebra.CliffordAlgebra.Basic`: Available
- `Mathlib.LinearAlgebra.CliffordAlgebra.Equivs`: Clifford ≅ ℂ, ℍ — available
- `NormedDivisionAlgebra`: Does NOT exist as a typeclass; use `NormedDivisionRing + NormedAlgebra ℝ`
- `NormedAlgebra.Real.nonempty_algEquiv_or` (Gelfand-Mazur, Stoll 2025): AVAILABLE — proves field case!
- `Complex.finrank_real_complex : finrank ℝ ℂ = 2`: Available
- `CommSemiring.finrank_self : finrank R R = 1`: Available
- Radon-Hurwitz numbers: NOT in Mathlib (as of 2026-04)

### Session 2026-04-21 Results
- Created `proofs/Proofs/HurwitzOnlyIf.lean` (115 lines, 1 sorry)
- Proved: `hurwitz_field_case` — commutative case via Gelfand-Mazur (0 sorries)
- Proved: `finrank_normed_field_eq_one_or_two` — helper (0 sorries)
- Sorry: `hurwitz_only_if_ring` — non-commutative case, documented NSquareIdentity reduction path
- Created gallery entry: `src/data/proofs/hurwitz-theorem-oq-03-oq-01/meta.json`

## Open Questions
- Can the NSquareIdentity reduction (NormedDivisionRing A → NSquareIdentity n) be formalized?
- Is Frobenius' theorem (associative case: dim ∈ {1,2,4}) easier to prove than full Hurwitz?
- Does Mathlib have enough InnerProductSpace support for orthonormal basis construction?

## References
- Hurwitz, A. (1898): "Über die Komposition der quadratischen Formen"
- Adams, J.F. (1960): "On the Non-Existence of Elements of Hopf Invariant One" — K-theory connection
- Baez, J.C. (2002): "The Octonions" — readable survey

---

## Session 2026-04-21 (Session 1) - Commutative Case via Gelfand-Mazur

**Mode**: FRESH
**Outcome**: progress — proved commutative subcase (0 sorries), created gallery entry, documented non-commutative path

### What I Did

1. Surveyed Mathlib for NormedDivisionAlgebra: does NOT exist; use `NormedDivisionRing + NormedAlgebra ℝ`
2. Found `NormedAlgebra.Real.nonempty_algEquiv_or` (Gelfand-Mazur, Stoll 2025): immediately proves the commutative case
3. Confirmed `Complex.finrank_real_complex`, `CommSemiring.finrank_self`, `LinearEquiv.finrank_eq` in Mathlib
4. Wrote `proofs/Proofs/HurwitzOnlyIf.lean` with:
   - `finrank_normed_field_eq_one_or_two` (proved): finrank ℝ F = 1 ∨ 2 for NormedField
   - `hurwitz_field_case` (proved): finrank ℝ F ∈ {1,2,4,8} for commutative case
   - `hurwitz_only_if_ring` (sorry): general NormedDivisionRing case with documented plan
5. Created gallery entry `src/data/proofs/hurwitz-theorem-oq-03-oq-01/`
6. Updated listings.json, research problem JSON, knowledge files

### Key Findings

**Gelfand-Mazur handles the commutative case completely**: `NormedAlgebra.Real.nonempty_algEquiv_or` is a 2025 Mathlib addition by Stoll that directly gives us `F ≃ₐ[ℝ] ℝ ∨ F ≃ₐ[ℝ] ℂ` for any NormedField over ℝ. No finite-dimensionality assumption needed.

**Key gap**: The `hurwitz_only_if_ring` sorry requires:
- Choosing an orthonormal basis of A (as an ℝ-vector space)
- Transporting multiplication to get an NSquareIdentity
- Calling `HurwitzTheorem.hurwitz_only_if` (axiom in parent file)
The orthonormal basis step needs Gram-Schmidt or isometric isomorphism infrastructure.

**Frobenius theorem** (associative only case): For `NormedDivisionRing` (associative), the only possibilities are ℝ, ℂ, ℍ — dim ∈ {1,2,4}. Octonions are non-associative. This means the sorry only needs to cover {1,2,4} for the associative case, but closing it still requires the NSquareIdentity construction.

### Files Modified
- `proofs/Proofs/HurwitzOnlyIf.lean` (created, 115 lines, 1 sorry)
- `src/data/proofs/hurwitz-theorem-oq-03-oq-01/` (created gallery entry)
- `src/data/proofs/listings.json` (added entry)
- `src/data/research/problems/hurwitz-theorem-oq-03-oq-01.json` (updated knowledge + phase)

### Next Steps
1. Formalize the NSquareIdentity reduction: `NormedDivisionRing A` → `NSquareIdentity (finrank ℝ A)`
2. Check Mathlib for `GramSchmidt` or `IsometryEquiv` that gives orthonormal basis for finite-dim normed spaces
3. Alternative: prove Frobenius' theorem directly (dim = 1 or 2 when commutative; dim = 4 when non-commutative)
