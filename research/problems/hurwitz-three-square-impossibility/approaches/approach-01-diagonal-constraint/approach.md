# Approach 01: Diagonal Constraint

## Strategy

The key insight is that the existing proof is missing one crucial constraint - the "diagonal constraint" that comes from `|mul(e₁+e₂, e₁+e₂)|² = 4`.

## Proof Outline

1. **Derive diagonal constraint**: `⟨m₁₁, m₂₂⟩ + ⟨m₁₂, m₂₁⟩ = 0`
   - From `|mul(e₁+e₂, e₁+e₂)|² = |e₁+e₂|² · |e₁+e₂|² = 4`
   - Expand using bilinearity and norm formula

2. **Show m₁₂ = ±m₂₁**:
   - m₁₂ ⊥ m₁₁ (row 1 orthogonality) ⟹ m₁₂ ∈ span{m₂₁, m₃₁}
   - m₂₂ ⊥ m₁₂ (column 2) and m₂₂ ⊥ m₂₁ (column 1)
   - If m₁₂ is not parallel to m₂₁, then span{m₁₂, m₂₁} = span{m₂₁, m₃₁}
   - Then m₂₂ ⊥ this 2D space ⟹ m₂₂ = ±m₁₁
   - Diagonal constraint gives ±1 + ⟨m₁₂, m₂₁⟩ = 0
   - For unit vectors in span{m₂₁, m₃₁}, |⟨m₁₂, m₂₁⟩| = 1 only if m₁₂ = ±m₂₁

3. **From m₁₂ = ±m₂₁, derive m₁₃ = ±m₃₁**:
   - m₁₃ ⊥ m₁₂ = ±m₂₁ (row 1)
   - m₁₃ ⊥ m₁₁ (row 1)
   - Only direction orthogonal to both is ±m₃₁

4. **Use hcross_zero to get ⟨m₁₁, m₂₃⟩ = 0**:
   - hcross_zero: ⟨m₁₁, m₂₃⟩ + ⟨m₁₃, m₂₁⟩ = 0
   - ⟨m₁₃, m₂₁⟩ = ⟨±m₃₁, m₂₁⟩ = 0 (column 1)
   - So ⟨m₁₁, m₂₃⟩ = 0

5. **Derive m₂₃ = ±m₃₁**:
   - m₂₃ ⊥ m₂₁ (row 2)
   - m₂₃ ⊥ m₁₁ (just derived)
   - So m₂₃ ∈ span{m₃₁}, hence m₂₃ = ±m₃₁

6. **Contradiction from column 3**:
   - m₂₃ ⊥ m₁₃ (column 3)
   - But m₂₃ = ±m₃₁ and m₁₃ = ±m₃₁
   - So ⟨m₂₃, m₁₃⟩ = ⟨±m₃₁, ±m₃₁⟩ = 1 ≠ 0
   - Contradiction!

## Key Mathlib Lemmas Needed

- Working with inner products and orthogonality
- Subspace characterization in finite dimensions
- Possibly: OrthonormalBasis for ℝ³ characterization

## Status

Ready to implement.
