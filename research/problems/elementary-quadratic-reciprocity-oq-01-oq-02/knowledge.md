# Problem: elementary-quadratic-reciprocity-oq-01-oq-02

**Title**: Can the character uniqueness argument be generalized to prove cubic or quartic reciprocity?

**Status**: in-progress  
**Phase**: ACT

## Problem Summary

For primes p ≡ 1 (mod 3), the group (ZMod p)ˣ is cyclic of order p-1 with 3 | (p-1). The cubic Euler criterion: a is a cube mod p iff a^((p-1)/3) = 1. The cubic character χ₃(a) = a^((p-1)/3) is a group homomorphism analogous to the Legendre symbol. Cubic reciprocity (Eisenstein 1844) states (ρ/π)₃ = (π/ρ)₃ for primary Eisenstein primes in ℤ[ω]. The quartic case uses (ZMod p)ˣ for p ≡ 1 (mod 4).

## Session 2026-05-03 (Session 1) - Cubic/Quartic Character Construction

**Mode**: FRESH  
**Outcome**: progress

### What I Did

- Claimed the problem atomically via `mkdir research/claims/<id>.lock`
- Created `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ02.lean` (391 lines)
- Constructed cubic character χ₃ = powMonoidHom((p-1)/3) as group hom (ZMod p)ˣ →* (ZMod p)ˣ
- Proved χ₃(a)³ = 1 via Fermat's little theorem for units
- Proved easy Euler criterion: x³ = a → χ₃(a) = 1 (using Units.mk0 lift + pow_mul + units_pow_card_sub_one_eq_one)
- Constructed quartic character χ₄ = powMonoidHom((p-1)/4) in parallel
- Axiomatized cubicEuler_hard (hard direction of Euler criterion)
- Axiomatized cubic_reciprocity (Eisenstein's law)
- Proved closure: cubic residues closed under 0, 1, cubing, multiplication, squaring, inverse
- Created gallery entry: src/data/proofs/elementary-quadratic-reciprocity-oq-01-oq-02/meta.json

### Key Findings

- `powMonoidHom (n : ℕ) : α →* α` works for CommMonoid — (ZMod p)ˣ qualifies
- The key unit-lifting pattern: `Units.mk0 x hx0` + `Units.ext; simp [Units.val_pow_eq_pow_val, Units.val_mk0]`
- `pow_mul` is needed instead of `ring` for group/monoid goals
- `ZMod.units_pow_card_sub_one_eq_one p xu` gives Fermat for units
- Cyclic group kernel cardinality API: `IsCyclic.exists_unique_subgroup_of_dvd` doesn't exist in Mathlib 4.26 — left as sorry
- Eisenstein integers ℤ[ω] not in Mathlib 4.26 → cubic reciprocity axiomatized

### Files Modified

- `proofs/Proofs/ElementaryQuadraticReciprocityOQ01OQ02.lean` (NEW, 391 lines)
- `proofs/Proofs.lean` (added import)
- `src/data/proofs/elementary-quadratic-reciprocity-oq-01-oq-02/meta.json` (NEW)

### Current State

- 3 axioms: cubicEuler_hard, cubicResidueSymbol, cubic_reciprocity
- 1 sorry: cubicChar_kernel_card (cyclic group kernel cardinality)
- 24 theorems proved, 6 defs
- Docker build submitted; awaiting result

### Next Steps

1. If Docker build passes: commit, push, PR with `research` label
2. Future: prove cubicChar_kernel_card using `Subgroup.card_eq_iff_eq_top` or similar
3. Future: when Mathlib gains Eisenstein integers, prove cubic_reciprocity
4. Future: submit cubicEuler_hard to Aristotle (needs cyclic group theory)
