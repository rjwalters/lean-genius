# Knowledge Base: hurwitz-theorem-oq-04

## Problem Summary

Formalize the connection between Hurwitz's theorem (exactly 4 normed division algebras: ℝ, ℂ, ℍ, 𝕆) and the exceptional Lie groups (G₂, F₄, E₆, E₇, E₈) via:
1. G₂ = Aut(𝕆)
2. Freudenthal-Tits magic square: 𝔏(A,B) = Der(A)⊕(ImA⊗ImB)⊕Der(B)

File: `proofs/Proofs/HurwitzTheoremOQ04.lean` (~730 lines)

---

## Session 2026-04-24 (Session 1) — Unit Identity Proofs

**Mode**: REVISIT
**Outcome**: progress — 2 computational sorries eliminated (pending build)

### What I Did

- Attempted to prove `eightMul_right_unit` and `eightMul_left_unit`
- Pattern from existing proofs: `simp only [stdBasis, ...] <;> simp (config := { decide := true }) only [ite_true, ite_false] <;> ring`
- Key insight: `simp (config := { decide := true })` is needed to evaluate `if (0:Fin 8) = j then 1 else 0` for concrete j values — found this in HurwitzTheorem.lean line 956

### Proof Attempts

**eightMul_right_unit** (and left_unit analogously):
```lean
set_option maxHeartbeats 800000 in
theorem eightMul_right_unit (a : Fin 8 → ℝ) : eightMul a octUnit = a := by
  funext i
  fin_cases i <;>
  simp only [eightMul, octUnit, stdBasis,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.cons_val_three] <;>
  simp (config := { decide := true }) only [ite_true, ite_false] <;>
  ring
```

### Key Technical Insights

- `octUnit = stdBasis 0 = fun j => if (0:Fin 8) = j then 1 else 0`
- After `fin_cases i`, the eightMul formula has concrete `octUnit j` for j = 0..7
- Plain `simp [stdBasis]` may not evaluate `(0:Fin 8) = j` for concrete j — need `decide := true` config
- Matrix.cons_val_* lemmas needed to access components of `![expr0, ..., expr7]`
- Pattern from line 956: `simp (config := { decide := true }) only [ite_true, ite_false]`

### Remaining Sorries

1. **alg_aut_preserves_norm** (line 160): normSq(φ(a)) = normSq(a) for OctonionAut
   - Cannot be proved from current axioms (alg hom + invertibility) without additional structure
   - Would need: φ(e₀) = e₀ (requires idempotent classification: only 0 and e₀ are idempotent in 𝕆)
   - OR: redefine OctonionAlgHom to include `map_norm` field (changes the formalization)
   
2. **real_part_preserved** (line 201): realPart(φ(x)) = realPart(x) for OctonionAut
   - Depends on alg_aut_preserves_norm and φ(e₀) = e₀

### Why alg_aut_preserves_norm Needs More

The algebra homomorphism condition `φ(a*b) = φ(a)*φ(b)` combined with the 8-square identity only gives:
  `normSq(φ(a)) * normSq(φ(b)) = normSq(φ(a*b))`
  
This is consistent with normSq being preserved, but doesn't FORCE it. The argument would be circular.

For a true proof:
1. Show φ(e₀) = e₀: Since φ(e₀)^2 = φ(e₀) (idempotent), and 𝕆 is a division algebra, the only idempotents are 0 and e₀. Since φ is injective, φ(e₀) ≠ 0. So φ(e₀) = e₀.
2. Then: normSq(φ(a)) * 1 = normSq(φ(a)) * normSq(e₀) = normSq(φ(a * e₀)) = normSq(φ(a)) [right unit]
   But this is tautological.
3. The actual proof uses: for any y in the image of φ, normSq(φ⁻¹(y)) = normSq(y). But we can't prove this without knowing normSq is preserved.

**Conclusion**: Need to add `map_one` to OctonionAlgHom AND a separate proof that unit-preserving multiplicative maps with the 8-square structure preserve norms. ~50 lines but requires restructuring.

### Next Steps

1. Add `map_one : map octUnit = octUnit` to OctonionAlgHom structure
2. Prove `alg_hom_unit : φ.map octUnit = octUnit` (trivial from new field)
3. Use this to prove `alg_aut_preserves_norm`:
   - From alg_hom_preserves_norm_product with b = octUnit: normSq(φ(a)) * normSq(φ(octUnit)) = normSq(φ(a * octUnit)) = normSq(φ(a))
   - Since φ(octUnit) = octUnit: normSq(φ(a)) * 1 = normSq(φ(a)) ✓ (still tautological!)
   - Need additional argument: normSq(φ(a)) = normSq(a) by "quadratic form invariance"
   
4. Alternative: axiomatize `alg_aut_preserves_norm` as an axiom (it's true, just hard to prove from our formalization)

---

## Session 2026-04-25 (Session 4) — De-axiomatize + Der(𝕆) Lie Algebra

**Mode**: REVISIT (RICH knowledge tier, score 24)
**Outcome**: PROGRESS — 4 axioms removed (rfl), OctonionDer Lie algebra formalized (0 sorries)

### What I Did

1. **De-axiomatized 4 trivial axioms**: `freudenthal_tits_f4/e6/e7/e8` were `axiom X.dim = N`
   where `X.dim` is DEFINED as `N`. These are just `rfl` — changed from `axiom` to `theorem ... := rfl`.
   Axiom count: 5 → 1 (only `G2_is_octonion_aut` remains as genuine axiom).

2. **Added PART IV-b: Der(𝕆)** (~140 lines, 0 sorries):
   - `eightMul_add_left/right/smul_left/right`: bilinearity helpers extracted from eightSquareIdentity
   - `OctonionDer` structure: ℝ-linear maps with Leibniz rule D(ab) = D(a)b + aD(b)
   - `zeroDer`: zero map is a derivation (0 sorries, proved by `fin_cases i; simp [eightMul]; ring`)
   - `addDer`: sum of two derivations (0 sorries, proved by `rw [D₁.leibniz, D₂.leibniz]; abel`)
   - `smulDer`: scalar multiple of a derivation (0 sorries, proved by bilinearity rewrites)
   - `eightMul_sub_left/right`: subtraction linearity (proved via add + smul)
   - `commDer`: [D₁,D₂] is a derivation (0 sorries, proved via h1/h2 expansions + abel)
   - `commDer_self_eq_zero`: [D,D] = 0 (0 sorries)
   - `commDer_antisymm`: [D₁,D₂] = -[D₂,D₁] (0 sorries)
   - `commDer_jacobi`: [[D₁,D₂],D₃] + [[D₂,D₃],D₁] + [[D₃,D₁],D₂] = 0 (0 sorries, `ring`)

### Key Findings

- **4 axioms were trivially true**: The `freudenthal_tits_*` axioms just said `dim = dim`. No
  mathematical content. The real mathematical claim (𝔏(𝕆,A) = ExceptionalType) is NOT formalized.
- **commDer.leibniz proof structure**: The key is to expand D₁(D₂(ab)) and D₂(D₁(ab)) separately
  using `h1`, `h2`, then use `eightMul_sub_left/right` for subtraction bilinearity, then `abel`.
  The cross-terms D₂(a)D₁(b) and D₁(a)D₂(b) cancel.
- **commDer_jacobi by ring**: After unfolding `commDer`, the Jacobi identity becomes an abelian
  group equation `ring` closes directly.
- **Lie algebra of Der(𝕆)**: Formalized: Der(𝕆) is closed under commutator [·,·], antisymmetric,
  satisfies Jacobi. This is the Lie algebra 𝔤₂ = Der(𝕆) at the algebraic level.

### Files Modified

- `proofs/Proofs/HurwitzTheoremOQ04.lean` (583 → 730 lines; PART IV-b added, preamble updated)
- `src/data/proofs/hurwitz-theorem-oq-04/meta.json` (axiomCount 5 → 1, lineCount 730, theoremCount 31)
- `src/data/research/problems/hurwitz-theorem-oq-04.json` (knowledge updated)

### Axiom Count: 5 → 1

- ~~freudenthal_tits_f4~~ → `theorem freudenthal_tits_f4 := rfl` ✓
- ~~freudenthal_tits_e6~~ → `theorem freudenthal_tits_e6 := rfl` ✓
- ~~freudenthal_tits_e7~~ → `theorem freudenthal_tits_e7 := rfl` ✓
- ~~freudenthal_tits_e8~~ → `theorem freudenthal_tits_e8 := rfl` ✓
- `G2_is_octonion_aut`: UNCHANGED (genuinely needs Lie group theory)

### Next Steps

1. **Exhibit 14 explicit derivations** of 𝕆: The space Der(𝕆) has dim 14. We could exhibit
   specific derivations via cross-product operators L_a,R_b — e.g., D_{ij}(x) = eₙ*(eᵢx)-eᵢ*(eⱼx)
   for specific basis pairs. ~100 lines.
2. **Archive sessions 1-3**: Move to sessions/ subdirectory (knowledge.md now >100 lines).
3. **G2_is_octonion_aut**: Still axiom. Proving it formally requires Lie group theory not in Mathlib.
   Could reformulate it as a dim(Der(𝕆)) = 14 statement once explicit derivations are exhibited.
