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

*Created 2026-03-28*
