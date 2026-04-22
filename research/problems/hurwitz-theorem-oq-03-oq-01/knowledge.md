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
- Can n=5,6,7 impossibility be proved by elementary matrix arguments (like n=3)?

## References
- Hurwitz, A. (1898): "Über die Komposition der quadratischen Formen"
- Adams, J.F. (1960): "On the Non-Existence of Elements of Hopf Invariant One" — K-theory connection
- Baez, J.C. (2002): "The Octonions" — readable survey

---

## Session 2026-04-21 (Session 1) — Polarization Identities + n=3 Case Proved

**Mode**: FRESH
**Outcome**: PROGRESS — 3 new proved lemmas, `hurwitz_only_if` converted from axiom to theorem

### What I Did

1. Read `HurwitzTheorem.lean` (1731 lines) — understood full structure
2. Found `no_three_square_identity` (line 1226) was already proved (0 sorries)  
3. Proved 3 polarization lemmas for any `NSquareIdentity n`:
   - `left_polarization`: ⟨mul(a,x), mul(b,x)⟩ = ⟨a,b⟩·‖x‖²
   - `right_polarization`: ⟨mul(x,a), mul(x,b)⟩ = ‖x‖²·⟨a,b⟩
   - `cross_polarization` (Pfister identity): ⟨mul(x,a), mul(y,b)⟩ + ⟨mul(x,b), mul(y,a)⟩ = 2⟨x,y⟩⟨a,b⟩
4. Converted `hurwitz_only_if` from `axiom` to `theorem`:
   - n=3 case: `exact no_three_square_identity nsi` (proved!)
   - n ∉ {1,2,3,4,8}: 1 sorry (needs Clifford/Radon-Hurwitz)

### Key Findings

**Polarization proof strategy**: The Pfister identity follows by polarizing left_polarization with `(a+b)` as the right argument and expanding bilinearly. All three lemmas proved via `linarith` from quadratic expansion.

**No `set` tactic needed**: Tried `set nax := normSq a * normSq x` but `ring` doesn't unfold `set` definitions. Used explicit `have` terms instead with products as atoms for `linarith`.

**`rw [← nsi.norm_mul]; ring` pattern**: Clean way to prove `normSq (nsi.mul x a) = normSq x * normSq a` (norm_mul states the reverse direction).

**Axiom count reduction**: From 1 axiom (covering ALL n ∉ {1,2,4,8}) to 0 axioms + 1 sorry (covering n ∉ {1,2,3,4,8} — the n=3 case is now a theorem).

**Remaining blocker**: The sorry covers n=5,6,7 and n>8. These need either:
1. Individual direct proofs (like n=3, but harder — ~500 lines for n=5 alone)
2. Full Clifford/Radon-Hurwitz machinery (not in Mathlib)

### Files Modified

- `proofs/Proofs/HurwitzTheorem.lean` (+112 lines: 3 new proved lemmas + converted axiom)
- `research/problems/hurwitz-theorem-oq-03-oq-01/knowledge.md`

### Next Steps

1. Consider proving n=5 impossibility directly (similar to n=3 but with 5-frame constraints)
2. Search for Mathlib Clifford algebra representations (to get Radon-Hurwitz without building from scratch)
3. Check if Adams' theorem on vector fields on spheres is accessible in Lean 4

---

## Session 2026-04-22 (Session 2) — Odd n Impossibility Proved via Matrix Det Argument

**Mode**: REVISIT (continuing claimed problem)
**Outcome**: PROGRESS — proved `no_odd_nsquare` covering all odd n ≥ 3 (except n=3 already done)

### What I Did

1. Developed matrix-determinant argument for odd n impossibility
2. Built infrastructure lemmas (`colMat`, `crossMat`, orthogonality proofs)
3. Proved `no_odd_nsquare`: odd n ≥ 3 → NSquareIdentity n → False
4. Updated `hurwitz_only_if` to dispatch odd n case to `no_odd_nsquare`

### Key Findings

**Matrix det argument**: 
- `colMat(nsi, j₀)`: the j₀-th "column multiplication matrix" — (i,k) entry = (nsi.mul eₖ e_{j₀})ᵢ
- `colMat(j₀)ᵀ × colMat(j₀) = I`: orthogonality_constraint gives column orthonormality
- `crossMat(j₁,j₂) = colMat(j₁)ᵀ × colMat(j₂)`: for j₁ ≠ j₂:
  - **Orthogonal**: crossMat^T × crossMat = I (proved via Matrix.mul_assoc + colMat_mulTrans)
  - **Skew-symmetric**: crossMat^T = -crossMat (proved via cross_polarization for off-diagonal, row ortho for diagonal)
- **Key contradiction**: M skew+orthogonal → M² = M^T×M after sign flip = -I → det(M)² = (-1)^n = -1 < 0

**Matrix.mul_eq_one_comm**: For square matrices over commutative ring, A×B=1 ↔ B×A=1.
Used to convert `colMat_transMul` (Mᵀ×M=I) to `colMat_mulTrans` (M×Mᵀ=I).

**Odd.neg_one_pow**: `(-1:R)^n = -1` for Odd n — key final step.

**Tactic `haveI : NeZero n := ⟨by omega⟩`**: needed to instantiate type class for Fin.card arithmetic.

### Current sorry count: 1

The remaining sorry covers **even non-admissible n** (n = 6, 10, 12, 14, 16, ...):
- n=6: no 6-square identity (needs Clifford Cl(5) rep theory)
- n=10, 12, ...: same Clifford algebra constraint
- **Mathematical obstacle**: need Radon-Hurwitz number ρ(n) < n for even n ∉ {2,4,8}

### Files Modified

- `proofs/Proofs/HurwitzTheorem.lean` (+153 lines: colMat, crossMat lemmas, no_odd_nsquare, updated hurwitz_only_if)
- `src/data/research/problems/hurwitz-theorem-oq-03-oq-01.json`

### Next Steps

1. **Even n approach**: For even n, the halving argument: if n-sq identity exists, then (n/2)-sq identity exists. Use this recursively: 6→3 (impossible!), 10→5 (odd, impossible), 12→6→3, etc. May handle all even non-admissible n without Clifford algebra.
2. **Submit current sorry to Aristotle** (likely HARD, not OPEN — mathematical argument exists via halving or Clifford)
3. If halving argument works, `hurwitz_only_if` could be fully proved.
