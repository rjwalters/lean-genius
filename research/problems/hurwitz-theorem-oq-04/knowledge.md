# Knowledge Base: hurwitz-theorem-oq-04

## Problem Summary

Formalize the connection between Hurwitz's theorem (exactly 4 normed division algebras: ℝ, ℂ, ℍ, 𝕆) and the exceptional Lie groups (G₂, F₄, E₆, E₇, E₈) via:
1. G₂ = Aut(𝕆)
2. Freudenthal-Tits magic square: 𝔏(A,B) = Der(A)⊕(ImA⊗ImB)⊕Der(B)

File: `proofs/Proofs/HurwitzTheoremOQ04.lean` (~430 lines)

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

## Session 2026-04-24 (Session 2) — Prove alg_aut_preserves_norm and real_part_preserved

**Mode**: REVISIT
**Outcome**: progress — eliminated 2 sorries (alg_aut_preserves_norm, real_part_preserved)

### What I Did

Added `phi_unit_eq_unit` (proved via invertibility of φ + eightMul_left_unit):
- φ(e₀) is a left identity (via surjectivity: φ(e₀)·y = φ(e₀)·φ(φ⁻¹(y)) = φ(e₀·φ⁻¹(y)) = y)
- Only element that is a left identity in a unital algebra = the unit → φ(e₀) = e₀

Added `imag_sq_eq_neg_norm`: For pure imaginary y (y 0 = 0), eightMul y y = -(normSq y)·e₀

Added `phi_imag_props`: For pure imaginary y, φ(y) is pure imaginary with same norm
- Step 1: φ(y)² = -(normSq y)·e₀ (via map_mul + imag_sq_eq_neg_norm)
- Step 2: normSq(φ(y))² = (normSq y)² via 8-square identity
- Step 3: normSq(φ(y)) = normSq(y) since both nonneg
- Step 4: (φ(y)) 0 = 0 from component 0 of φ(y)²

From these, proved `alg_aut_preserves_norm` (decompose a = r·e₀ + w, apply phi_imag_props)
and `real_part_preserved` (follows from phi_unit_eq_unit + decomposition).

---

## Session 2026-04-24 (Session 3 - researcher-7) — Prove alg_aut_preserves_inner, imag_closed_under_aut

**Mode**: REVISIT
**Outcome**: progress — 2 new theorems added (unlocked by alg_aut_preserves_norm)

### What I Did

Added `alg_aut_preserves_inner`: Aut(𝕆) preserves the inner product.
- Proof: `innerProd x y = (normSq(x+y) - normSq x - normSq y) / 2` (polarization)
- Using `alg_aut_preserves_norm` for each norm term + linearity (`map_add`)
- Clean: `simp only [innerProd_eq_normSq]; rw [← φ.map_add]; rewrite norm terms`

Added `imag_closed_under_aut`: φ maps Im(𝕆) to Im(𝕆) (public wrapper for private `phi_imag_props`).
- Direct: `(phi_imag_props φ x hx).1`

These two together formalize "Aut(𝕆) ⊆ O(7)" in the sense that:
- φ fixes real part (real_part_preserved)
- φ maps Im(𝕆) to Im(𝕆) (imag_closed_under_aut)
- φ preserves norm on Im(𝕆) (from alg_aut_preserves_norm + imag_closed_under_aut)
- φ preserves inner product on Im(𝕆) (from alg_aut_preserves_inner)

### Sorry Status

0 sorries, 5 axioms (unchanged):
1. `G2_is_octonion_aut`: G₂ = Aut(𝕆) (dim = 14)
2-5. `freudenthal_tits_f4/e6/e7/e8`: magic square exceptional types

### Next Steps

1. Define `Der(𝕆)` as the space of derivations and attempt to show its dimension is 14
2. If Lean gets Lie group theory, replace `G2_is_octonion_aut` axiom with proof
3. Could formalize the 7-dim cross product preservation constraint (~100 lines)
