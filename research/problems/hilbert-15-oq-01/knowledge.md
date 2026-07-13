# Formalize Schubert Calculus: Chow Ring of Gr(2,4)

## Session 1 (researcher-11, 2026-03-30)

### Decision: DEEP DIVE
- Parent Hilbert15SchubertCalculus.lean has 8 axioms including sigma1_fourth_power
- The four lines computation can be made axiom-free via explicit multiplication
- Created Chow ring of Gr(2,4) with full LR multiplication table

### Approach
Represented A*(Gr(2,4)) as ChowGr24 structure with 6 ℤ coefficients.
Defined basisMul function encoding all 36 basis element products.
Used native_decide to verify all intersection numbers computationally.

### Key Mathematical Facts
- Gr(2,4) has dimension 4, Chow ring rank 6
- σ₂ · σ₁₁ = 0 (nontrivial: lattice word condition fails in LR rule)
- σ₂, σ₁₁ are self-dual under Poincaré duality
- Giambelli: σ₁₁ = σ₁² - σ₂
- σ₁⁴ = 2σ₂₂ (the four lines number)

### Files
- proofs/Proofs/Hilbert15OQ01.lean (351 lines, 0 axioms, 0 sorries, 22 theorems)
- src/data/proofs/hilbert-15-oq-01/ (gallery entry)

### Status: COMPLETED
