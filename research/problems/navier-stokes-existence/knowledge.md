# Knowledge Base: navier-stokes-existence

## Problem Understanding

### Core Statement
Prove existence and smoothness of solutions to the 3D Navier-Stokes equations, or provide a counterexample.

### Formalization Requirements
1. Navier-Stokes equations in 3D
2. Sobolev spaces and weak solutions
3. Energy estimates
4. Regularity theory

## Blockers

### Primary Blocker: Advanced PDE Theory
**Status**: BLOCKED
**Severity**: Critical

Mathlib lacks:
- [ ] Navier-Stokes equations
- [ ] Sobolev spaces (limited)
- [ ] Energy methods for fluids
- [ ] Regularity for nonlinear PDE

### Secondary Blocker: 3D Specific Challenges
The 3D case uniquely requires:
- [ ] Ladyzhenskaya inequality (3D only)
- [ ] Enstrophy estimates
- [ ] Vortex stretching analysis

## Tractable Partial Work

1. **2D Navier-Stokes** - Global existence IS known (2d-navier-stokes project)
2. **Weak solutions** - Leray's existence theorem
3. **Partial regularity** - Caffarelli-Kohn-Nirenberg
4. **Stokes equations** - Linear case

## Related Gallery Proofs

| Proof | Relevance |
|-------|-----------|
| 2d-navier-stokes | Simpler case where existence is known |

## Scouting Log

### Initial Assessment: 2026-01-01

**Current Status**: BLOCKED - Heavy PDE/analysis requirements

**Blocker Tracking**:
| Infrastructure | In Mathlib | Last Checked |
|----------------|------------|--------------|
| Basic PDEs | Yes | 2026-01-01 |
| Sobolev spaces | Limited | 2026-01-01 |
| Navier-Stokes | No | 2026-01-01 |
| Fluid mechanics | No | 2026-01-01 |

**Related Active Work**: 2d-navier-stokes attempts the tractable 2D case

**Next Scout**: Check Mathlib PDE development
