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

### Lean 4 Status
- `Mathlib.LinearAlgebra.CliffordAlgebra.Basic`: Available
- `Mathlib.LinearAlgebra.CliffordAlgebra.Spinor`: Some content
- `NormedDivisionAlgebra`: Typeclass exists in Mathlib
- Radon-Hurwitz numbers: NOT in Mathlib (as of early 2026)

## Open Questions
- Is there a Mathlib path that avoids computing Radon-Hurwitz numbers explicitly?
- Can the n=3 impossibility be proved more directly (no Clifford needed for n=3)?

## References
- Hurwitz, A. (1898): "Über die Komposition der quadratischen Formen"
- Adams, J.F. (1960): "On the Non-Existence of Elements of Hopf Invariant One" — K-theory connection
- Baez, J.C. (2002): "The Octonions" — readable survey
