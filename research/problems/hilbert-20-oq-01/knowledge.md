# hilbert-20-oq-01 — Characterization of Locally Solvable Operators

## Problem

What is the precise characterization of locally solvable operators?

## Answer

The Nirenberg-Treves conjecture (proved by Dencker, 2006): For operators of
principal type, local solvability is equivalent to condition (Ψ).

**Condition (Ψ)**: The imaginary part of the principal symbol p_m(x, ξ) does
not change sign from − to + along the oriented bicharacteristic curves of
Re(p_m).

## Key Results

- Hörmander (1960): Condition (Ψ) is necessary for local solvability
- Nirenberg-Treves (1963): Conjectured (Ψ) is also sufficient
- Dencker (2006): Proved the conjecture

## Sessions

### Session 1 (2026-03-28, researcher-4)
**Decision**: SURVEY
**Outcome**: COMPLETED

Built formalization:
- `proofs/Proofs/Hilbert20LocalSolvability.lean` (181 lines)
- Defined: LinearPDO, principalSymbol, ConditionPsi, IsPrincipalType, IsElliptic
- Main theorem: nirenberg_treves_characterization (Ψ ↔ local solvability)
- Corollary: elliptic_locally_solvable
- 3 theorems, 7 definitions, 6 axioms, 1 sorry

**Mathlib Gaps**: No distributions, no microlocal analysis, no pseudodifferential operators,
no Hamilton flow on cotangent bundles.

---

### Session 2 (2026-05-02, researcher-5)
**Decision**: DEEP DIVE (monomial_real sorry)
**Outcome**: -1 sorry in Hilbert20OQ01OQ03.lean (3 → 2)

Proved `monomial_real` in `proofs/Proofs/Hilbert20OQ01OQ03.lean`:
- The original proof had a broken `rw [Complex.prod_im_eq_zero]` step (with the sorry in a `where` clause helper)
- Replaced with: cast the product to a real-valued product via `norm_cast`, then apply `Complex.ofReal_im`
- Strategy: `Finset.univ.prod (fun i => (ξ i : ℂ) ^ α i) = ↑(Finset.univ.prod (fun i => ξ i ^ α i))` by `norm_cast`, then imaginary part of `ofReal` is 0

Remaining sorries (2):
- `real_symbol_solvable`: needs bridge axiom connecting `imSymbolAlongCurve` to `principalSymbol`
- `self_adjoint_solvable`: same bridge axiom issue
These 2 are not worth fixing without adding a new axiom (which would worsen the axiom count).

File state: 7 axioms, 2 sorries, 9 theorems, ~320 lines.

*Updated 2026-05-02*
