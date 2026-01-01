# Knowledge Base: p-vs-np

## Problem Understanding

### Core Statement
Does P = NP? Or equivalently: can every problem whose solution can be verified quickly also be solved quickly?

### Formalization Requirements
1. Definition of Turing machines
2. Definition of polynomial time (P)
3. Definition of nondeterministic polynomial time (NP)
4. Definition of NP-completeness
5. Example NP-complete problem (SAT, 3-SAT, etc.)

## Blockers

### Primary Blocker: Computational Complexity Framework
**Status**: BLOCKED
**Severity**: Critical

Mathlib does not have:
- [ ] Turing machine formalization
- [ ] Time complexity classes
- [ ] Polynomial-time reductions
- [ ] NP-completeness definitions
- [ ] Cook-Levin theorem (SAT is NP-complete)

### Secondary Blocker: Barrier Results
Even formalizing what we know requires:
- [ ] Oracle Turing machines (for relativization)
- [ ] Circuit complexity (for natural proofs)
- [ ] Algebraic computation models (for algebrization)

## Tractable Partial Work

We could formalize:
1. **Barrier results** (pnp-barriers project is attempting this)
   - Relativization barrier: ∃ oracles A, B with P^A = NP^A and P^B ≠ NP^B
   - Natural proofs barrier: Natural properties can't prove P ≠ NP if OWFs exist
   - Algebrization barrier: Algebraic techniques insufficient

2. **Specific algorithms**
   - P algorithms for matching, primality, etc.
   - SAT solvers (without proving NP-completeness)

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| pnp-barriers | Formalizing why standard techniques fail |

## Scouting Log

### Initial Assessment: 2026-01-01

**Current Status**: BLOCKED - Requires computational complexity framework

**Blocker Tracking**:
| Infrastructure | In Mathlib | Last Checked |
|----------------|------------|--------------|
| Turing machines | Minimal | 2026-01-01 |
| Time complexity | No | 2026-01-01 |
| NP-completeness | No | 2026-01-01 |
| Reductions | No | 2026-01-01 |

**Active Work**: pnp-barriers is formalizing barrier results instead of the main conjecture

**Next Scout**: Check for computational complexity Mathlib proposals
