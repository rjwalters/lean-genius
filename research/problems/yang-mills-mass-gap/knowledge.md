# Knowledge Base: yang-mills-mass-gap

## Problem Understanding

### Core Statement
Prove that for any compact simple gauge group G, a non-trivial quantum Yang-Mills theory exists on R^4 and has a mass gap Δ > 0.

### Formalization Requirements
1. Quantum field theory framework
2. Yang-Mills Lagrangian
3. Path integral formulation
4. Mass gap definition
5. Axiomatic QFT (Wightman or Haag-Kastler)

## Blockers

### Primary Blocker: QFT Foundations
**Status**: BLOCKED
**Severity**: Critical

Mathlib has essentially none of:
- [ ] Quantum field theory axioms
- [ ] Path integrals
- [ ] Gauge theory
- [ ] Yang-Mills equations

### Secondary Blocker: Analysis Requirements
The rigorous construction needs:
- [ ] Functional integrals
- [ ] Renormalization
- [ ] Constructive QFT techniques

## Tractable Partial Work

1. **Classical Yang-Mills** - The PDE without quantization
2. **2D Yang-Mills** - Solvable exactly
3. **Lattice gauge theory** - Discrete approximation
4. **Gauge group theory** - Lie groups and connections

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| (none yet) | - |

## Scouting Log

### Initial Assessment: 2026-01-01

**Current Status**: BLOCKED - Requires QFT framework not in Mathlib

**Blocker Tracking**:
| Infrastructure | In Mathlib | Last Checked |
|----------------|------------|--------------|
| Lie groups | Yes | 2026-01-01 |
| Connections | Partial | 2026-01-01 |
| QFT axioms | No | 2026-01-01 |
| Path integrals | No | 2026-01-01 |

**Next Scout**: Long-term - QFT formalization is a major project
