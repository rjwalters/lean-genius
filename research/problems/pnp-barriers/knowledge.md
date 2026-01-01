# Knowledge Base: pnp-barriers

## Problem Summary

Formalize the major barriers to proving P ≠ NP:
1. Relativization Barrier (Baker-Gill-Solovay, 1975)
2. Natural Proofs Barrier (Razborov-Rudich, 1997)
3. Algebrization Barrier (Aaronson-Wigderson, 2009)

## Current State

**Status**: Surveyed (has axioms, full proofs for consequences)

### What's Proven (no sorries)
- `P_subset_NP_relative` - P^A ⊆ NP^A for any oracle A (full 40-line proof)
- `relativization_barrier_eq` - Cannot prove P=NP by relativizing
- `relativization_barrier_neq` - Cannot prove P≠NP by relativizing
- `relativization_barrier` - Combined barrier
- `natural_proof_breaks_crypto` - Natural proofs contradict OWFs
- `relativization_insight` - Key insight about barrier
- `P_subset_NP` - Unrelativized P ⊆ NP
- `all_barriers_constrain_proofs` - Combined constraint

### Axioms (would require ~10,000+ lines each)
- `exists_oracle_P_eq_NP` - Baker-Gill-Solovay Part 1
- `exists_oracle_P_neq_NP` - Baker-Gill-Solovay Part 2
- `P_subset_Ppoly` - P ⊆ P/poly
- `owf_implies_prf` - OWF implies PRF
- `natural_proofs_barrier` - Main theorem
- `algebrization_barrier_pos/neg` - Aaronson-Wigderson

## Mathlib Infrastructure

### Available in Mathlib
- `Mathlib.Computability.TuringMachine` - TM0, TM1, TM2 models
- `Mathlib.Computability.TMComputable` - `TM2ComputableInPolyTime`, `TM2Computable`
- `Mathlib.Computability.Halting` - Halting problem, Rice's theorem
- `Polynomial ℕ` - Proper polynomial type

### Missing in Mathlib
- Oracle Turing machines
- Complexity classes P, NP, PSPACE
- Circuit complexity
- Cryptographic primitives (OWFs, PRFs)

## Session Log

### 2025-12-31 Session 1

**What we did**:
- Searched for Mathlib TM infrastructure
- Found `TM2ComputableInPolyTime` in Mathlib
- Added Part 8: Connection to Mathlib Infrastructure
- Added `P_unrelativized`, `NP_unrelativized`, `P_subset_NP`
- Added `P_eq_NP_Question` formal statement
- Added `all_barriers_constrain_proofs` combining all three barriers

**Outcome**:
- Extended from 443 to 511 lines
- 7 new definitions/theorems
- Documented connection to Mathlib's TM formalization

**Key findings**:
- Mathlib has substantial TM infrastructure but no oracle TMs
- Our abstract oracle model is compatible with Mathlib's approach
- Could potentially bridge by showing our `P_relative emptyOracle` matches Mathlib's `TM2ComputableInPolyTime`

## Next Steps (Increasing Difficulty)

1. **Add more consequences** - Prove more corollaries from barrier axioms
2. **Connect to Mathlib TM** - Prove equivalence between our P_unrelativized and Mathlib's polytime
3. **Formalize diagonalization** - Prove exists_oracle_P_neq_NP from first principles
4. **Circuit complexity basics** - Prove P ⊆ P/poly from Mathlib TMs

## Technical Notes

### Oracle TM Abstraction

Our oracle TM is abstract: just a function from (Oracle × Input) → (Result × Steps).
This is sufficient for barrier theorems since they're about the logical structure
of proofs, not the computational details.

### Why Barriers Work

1. **Relativization**: If a proof only uses facts true for all oracles,
   it would give the same answer for P^A=NP^A and P^B≠NP^B oracles.

2. **Natural Proofs**: Large, constructive circuit properties include PRFs,
   which have small circuits, so such properties can't prove lower bounds.

3. **Algebrization**: Even non-relativizing techniques like arithmetization
   fail because algebraic extensions also flip the answer.

## File Location

`proofs/Proofs/PNPBarriers.lean`
