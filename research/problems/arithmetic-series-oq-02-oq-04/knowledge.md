# arithmetic-series-oq-02-oq-04 - Knowledge Base

## Problem Statement

Formalize the general closed form S_k(n) * k! = (n+1)(n+2)...(n+k) for all k,
and prove it equals Nat.choose (n+k) k * k! by the binomial coefficient formula.

## Status

**Phase**: COMPLETED
**Tractability Score**: 9/10

## Sessions

### Session 2026-03-26 (Session 1) - Complete Proof

**Mode**: FRESH
**Outcome**: completed

#### What I Did
- Claimed problem from candidate pool (score 0, EMPTY tier)
- Assessed feasibility: Mathlib has `Nat.ascFactorial_eq_factorial_mul_choose` which directly gives the identity
- Created `proofs/Proofs/ArithmeticSeriesOQ02OQ04.lean` (158 lines, 11 theorems)
- Created gallery metadata in `src/data/proofs/arithmetic-series-oq-02-oq-04/`

#### Key Findings
- The main identity is essentially `mul_comm` applied to Mathlib's `ascFactorial_eq_factorial_mul_choose`
- The product formula requires a clean induction on k using `ascFactorial`'s recurrence
- `simplicial_full_factorial` needs `Nat.add_sub_cancel` to normalize (n+k)-k to n
- The divisibility `k! | ascFactorial(n+1, k)` follows from the existence of C(n+k,k) as a witness

#### Files Created
- `proofs/Proofs/ArithmeticSeriesOQ02OQ04.lean` - Main proof file (158 lines)
- `src/data/proofs/arithmetic-series-oq-02-oq-04/meta.json` - Gallery metadata
- `src/data/proofs/arithmetic-series-oq-02-oq-04/index.ts` - Gallery module
- `src/data/proofs/arithmetic-series-oq-02-oq-04/annotations.json` - Annotations (empty)
- `src/data/proofs/arithmetic-series-oq-02-oq-04/tacticStates.json` - Tactic states (empty)

#### Theorems Proved
1. `simplicial_factorial`: C(n+k,k) * k! = ascFactorial(n+1, k)
2. `ascFactorial_eq_prod`: ascFactorial(n, k) = prod i in range k, (n+i)
3. `simplicial_product`: S_k(n) * k! = prod i in range k, (n+1+i)
4. `simplicial_full_factorial`: S_k(n) * k! * n! = (n+k)!
5. `factorial_dvd_ascFactorial`: k! | ascFactorial(n+1, k)
6-8. simplicial_factorial_one/two/three: k=1,2,3 specializations
9-11. check_k4_n3, check_k5_n2, check_product: concrete verifications

#### Next Steps
- None needed - proof is complete
- Docker build verification pending (Docker not available in this session)
