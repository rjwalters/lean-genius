# Knowledge Base: hurwitz-three-square-impossibility

Insights accumulated during research on this problem.

---

## Problem Understanding

### The Setup (from HurwitzTheorem.lean)

An `NSquareIdentity 3` provides a bilinear multiplication `mul : ℝ³ × ℝ³ → ℝ³` satisfying:
```
‖mul(a, b)‖² = ‖a‖² · ‖b‖²
```

Let `e₁, e₂, e₃` be the standard basis. Define 9 unit vectors:
```
m_ij = mul(e_i, e_j)   for i, j ∈ {1, 2, 3}
```

### Already Proven Constraints

1. **All m_ij are unit vectors** (from norm equation with basis vectors)

2. **Column orthonormality**: For fixed j, {m₁ⱼ, m₂ⱼ, m₃ⱼ} is orthonormal
   - Derived from: `⟨mul(e_i, e_j), mul(e_k, e_j)⟩ = ⟨e_i, e_k⟩` when i ≠ k

3. **Row orthonormality**: For fixed i, {mᵢ₁, mᵢ₂, mᵢ₃} is orthonormal
   - Derived similarly from right multiplication

4. **Cross-term equations** (from `(a+b, c+d)` expansions):
   - `hcross_zero: ⟨m₁₁, m₂₃⟩ + ⟨m₁₃, m₂₁⟩ = 0`
   - `hcross_zero2: ⟨m₁₂, m₂₃⟩ + ⟨m₂₂, m₁₃⟩ = 0`
   - `hcross_zero3: ⟨m₂₁, m₃₃⟩ + ⟨m₃₁, m₂₃⟩ = 0`

---

## Insights

### Insight 1: Missing Diagonal Constraint (2025-12-30)

**Discovery**: There's a crucial constraint not currently used in the proof.

From `|mul(e₁ + e₂, e₁ + e₂)|² = |e₁ + e₂|² · |e₁ + e₂|² = 4`:

Expanding the left side:
```
|mul(e₁ + e₂, e₁ + e₂)|² = |m₁₁ + m₁₂ + m₂₁ + m₂₂|²
= |m₁₁|² + |m₁₂|² + |m₂₁|² + |m₂₂|²     (all = 1)
  + 2⟨m₁₁, m₁₂⟩ + 2⟨m₁₁, m₂₁⟩          (both = 0, row/col orthogonality)
  + 2⟨m₁₂, m₂₂⟩ + 2⟨m₂₁, m₂₂⟩          (both = 0, row/col orthogonality)
  + 2⟨m₁₁, m₂₂⟩ + 2⟨m₁₂, m₂₁⟩          (DIAGONAL TERMS!)
= 4 + 2(⟨m₁₁, m₂₂⟩ + ⟨m₁₂, m₂₁⟩)
```

For this to equal 4:
**⟨m₁₁, m₂₂⟩ + ⟨m₁₂, m₂₁⟩ = 0**

This "diagonal constraint" is NOT in the current proof!

### Insight 2: Rotation Characterization (2025-12-30)

**Key Observation**: In ℝ³, both column 1 {m₁₁, m₂₁, m₃₁} and row 1 {m₁₁, m₁₂, m₁₃} are orthonormal bases sharing m₁₁.

**Geometric Fact**: Two orthonormal bases sharing one vector are related by a rotation about that shared vector.

Let R_θ be a rotation by angle θ about m₁₁. Then:
- m₁₂ = cos(θ) · m₂₁ + sin(θ) · m₃₁
- m₁₃ = -sin(θ) · m₂₁ + cos(θ) · m₃₁

This parametrizes the entire structure by a single angle θ!

### Insight 3: Complete Proof Strategy (2025-12-30)

**Case Analysis on sin(θ)**:

**Case 1: sin(θ) = 0**
- Then m₁₂ = ±m₂₁ and m₁₃ = ±m₃₁
- Column 2 {m₁₂, m₂₂, m₃₂} is orthonormal
- Since m₁₂ = ±m₂₁, and m₂₁ ⊥ m₂₂ (column 1), we get m₁₂ ⊥ m₂₂
- Row 2 {m₂₁, m₂₂, m₂₃} is orthonormal, so m₂₂ ⊥ m₂₃
- From cross-term: ⟨m₁₁, m₂₃⟩ + ⟨m₁₃, m₂₁⟩ = 0
- With sin(θ) = 0: m₁₃ = ±m₃₁, and ⟨m₃₁, m₂₁⟩ = 0, so ⟨m₁₁, m₂₃⟩ = 0
- But m₂₃ must be orthogonal to both m₂₁ and m₂₂
- In 3D, this means m₂₃ = ±m₁₁ (only direction left)
- But ⟨m₁₁, m₂₃⟩ = 0 contradicts m₂₃ = ±m₁₁!

**Case 2: sin(θ) ≠ 0**
- Column 2: {m₁₂, m₂₂, m₃₂} orthonormal, m₁₂ = cos(θ)m₂₁ + sin(θ)m₃₁
- m₂₂ must be orthogonal to m₁₂
- Using the parametrization and orthonormality...
- This forces m₂₂ = ±m₁₁ (detailed calculation needed)
- But diagonal constraint: ⟨m₁₁, m₂₂⟩ + ⟨m₁₂, m₂₁⟩ = 0
- ⟨m₁₁, ±m₁₁⟩ = ±1
- ⟨m₁₂, m₂₁⟩ = cos(θ) (from parametrization)
- So ±1 + cos(θ) = 0, meaning cos(θ) = ∓1
- But cos(θ) = ±1 implies sin(θ) = 0, contradiction!

**Both cases lead to contradiction. QED.**

### Insight 4: Mathlib Resources (2025-12-30)

Relevant Mathlib theorems found:
- `Orthonormal.inner_eq_zero` - orthonormal implies inner product zero
- `orthonormal_iff_ite` - characterization of orthonormality
- `OrthonormalBasis` - type for orthonormal bases with bundled proofs
- `basisOfOrthonormalOfCardEqFinrank` - constructing bases from orthonormal families
- `inner_self_eq_one` - characterization of unit vectors

---

## Dead Ends

### Approach: Pure coordinate computation
**Why it might fail**: The existing proof is ~700 lines without coordinates. Introducing explicit ℝ³ coordinates could require significant Mathlib machinery for conversions.

### Approach: Determinant argument
**Status**: Untried but may be more complex than rotation approach. Would need matrix formulation infrastructure.

---

## Implementation Attempt (2025-12-30)

### Attempt 01: Diagonal Constraint Approach

**File**: `approaches/approach-01-diagonal-constraint/attempts/attempt-01.lean`

**Status**: Compiles with strategic sorries. Key structure proven.

**What Works**:
- Basic lemmas: `normSq_nonneg`, `normSq_neg`, `innerProd_neg_right`
- Unit vector characterization: `unit_inner_one_eq`, `unit_inner_neg_one_eq`
- Cauchy-Schwarz-like bounds: `inner_unit_le_one`, `inner_unit_ge_neg_one`
- Key theorem structure: `unit_ortho_two_eq_pm_third` (assuming Parseval)

**Key Sorry**: `inner_expansion_three` (Parseval identity for orthonormal triples)
- Statement: For orthonormal {v₁, v₂, v₃}, any w satisfies:
  `|w|² = ⟨w, v₁⟩² + ⟨w, v₂⟩² + ⟨w, v₃⟩²`
- This requires proving orthonormal vectors in ℝ³ span the space
- Options to fill:
  1. Use Mathlib's OrthonormalBasis and its Parseval theorem
  2. Explicit 3×3 matrix determinant argument
  3. Direct coordinate computation for Fin 3 → ℝ

**Proof Structure Discovered**:
1. Derive diagonal constraint (follows hcross_zero pattern)
2. Show m₁₂ = ±m₂₁ using diagonal + orthogonality
3. Show m₁₃ = ±m₃₁ similarly
4. Use hcross_zero to get ⟨m₁₁, m₂₃⟩ = 0
5. Apply `unit_ortho_two_eq_pm_third` to get m₂₃ = ±m₃₁
6. col3 orthogonality ⟨m₂₃, m₁₃⟩ = 0 contradicts both being ±m₃₁

### Attempt 02: Parseval Identity (2025-12-30)

**File**: `approaches/approach-01-diagonal-constraint/attempts/attempt-02-parseval.lean`

**Status**: Compiles with 1 sorry! Major progress!

**Proof Structure**:
1. Define `proj3 v₁ v₂ v₃ w = ⟨w,v₁⟩v₁ + ⟨w,v₂⟩v₂ + ⟨w,v₃⟩v₃`
2. Prove `diff = w - proj3` is orthogonal to each vᵢ ✓
3. Prove `diff = 0` using linear algebra (sorry - matrix invertibility)
4. Therefore `w = proj3` and `|w|² = |proj3|²`
5. Compute `|proj3|² = ⟨w,v₁⟩² + ⟨w,v₂⟩² + ⟨w,v₃⟩²` ✓

**Proven Lemmas**:
- `normSq_smul`, `normSq_add`, `innerProd_smul_smul` - helper lemmas for projection ✓
- `normSq_proj3` - expanding |c₁v₁ + c₂v₂ + c₃v₃|² ✓
- `diff_ortho_v1`, `diff_ortho_v2`, `diff_ortho_v3` - all complete! ✓
- `inner_expansion_three` - Parseval identity, complete modulo 1 sorry ✓

**Remaining Sorry**:
`ortho_to_orthonormal_triple_eq_zero` - in ℝ³, orthogonal to 3 orthonormal vectors ⟹ zero

This requires showing the matrix M = [v₁|v₂|v₃] is invertible (det ≠ 0 because Mᵀ M = I
implies det(M)² = 1). The proof is mathematically complete but requires Mathlib matrix
machinery to formalize. Could alternatively use `basisOfOrthonormalOfCardEqFinrank` from
Mathlib if we switch to using Mathlib's inner product space structure.

### Remaining Work

1. **Fill 1 Parseval sorry**: `ortho_to_orthonormal_triple_eq_zero` (matrix invertibility)
2. ~~**Derive diagonal constraint in main proof**~~: ✓ Added to HurwitzTheorem.lean (lines 546-601)
3. **Complete case analysis**: Apply the Parseval lemmas to finish the proof
4. **Remove axiom**: Replace `no_three_square_identity_contradiction` with proof

### Integration Progress (2025-12-30)

**Diagonal constraint successfully added to HurwitzTheorem.lean!**

The proof now has 4 cross-term constraints:
- `hcross_zero: ⟨m₁₁, m₂₃⟩ + ⟨m₁₃, m₂₁⟩ = 0`
- `hdiag_zero: ⟨m₁₁, m₂₂⟩ + ⟨m₁₂, m₂₁⟩ = 0` ← NEW!
- `hcross_zero2: ⟨m₁₂, m₂₃⟩ + ⟨m₂₂, m₁₃⟩ = 0`
- `hcross_zero3: ⟨m₂₁, m₃₃⟩ + ⟨m₃₁, m₂₃⟩ = 0`

To complete the proof, we need to:
1. Import the Parseval lemmas from attempt-02-parseval.lean
2. Use `unit_ortho_two_eq_pm_third` to show m₂₃ = ±m₃₁
3. Derive contradiction from col3_12 (⟨m₂₃, m₁₃⟩ = 0 but m₂₃ = ±m₃₁, m₁₃ = ±m₃₁)

---

## Next Steps

1. ~~Create approach directory for "rotation-case-analysis"~~ Done: using diagonal constraint approach
2. ~~Implement the diagonal constraint derivation~~ Done: pattern identified
3. Fill the Parseval identity sorry
4. Integrate helper lemmas into HurwitzTheorem.lean
5. Complete the proof and remove the axiom
