# Knowledge Base: Navier-Stokes Existence and Smoothness

## The Problem

The Navier-Stokes problem asks whether smooth, physically reasonable solutions exist for all time for the equations governing fluid flow in three dimensions.

### Core Statement

> In 3D, prove global existence and smoothness of Navier-Stokes solutions for all smooth initial data, or provide a counterexample showing finite-time blowup.

The equations describe how velocity and pressure of a fluid evolve:

∂u/∂t + (u·∇)u = ν∆u - ∇p + f
∇·u = 0

where u is velocity, p is pressure, ν is viscosity, and f is external force.

### Why It Matters

1. **Fluid Dynamics**: Governs everything from weather to blood flow
2. **Engineering**: Aircraft design, turbulence modeling, oceanography
3. **Physics**: Fundamental understanding of fluids
4. **Turbulence**: Connected to one of the last major unsolved physics problems

## Historical Context

| Year | Mathematician | Contribution |
|------|--------------|--------------|
| 1822 | Navier | Derived equations with molecular assumptions |
| 1845 | Stokes | Rigorous continuum derivation |
| 1934 | Leray | Weak solutions exist globally |
| 1962 | Ladyzhenskaya | 2D global regularity |
| 1977 | Scheffer | Partial regularity results |
| 1982 | Caffarelli-Kohn-Nirenberg | Singular set has dimension ≤ 1 |

The 3D problem remains open despite 90+ years of effort since Leray.

## The Key Difficulty: 3D vs 2D

### 2D: Solved!

In 2D, global smooth solutions exist. Key facts:
- Vorticity ω = curl(u) satisfies a nice transport equation
- Enstrophy ∫|ω|² is bounded for all time
- No vortex stretching term
- Global regularity follows from energy estimates

### 3D: Open

In 3D, the vortex stretching term (ω·∇)u can potentially cause:
- Vorticity concentration
- Energy cascade to small scales
- Possible finite-time singularity

The Ladyzhenskaya inequality ||u||_4 ≤ C||u||_{H¹}^{3/4}||u||_2^{1/4} only works in 2D.

## What We Could Build

### In Mathlib Now

| Component | Status | Notes |
|-----------|--------|-------|
| Vector calculus | ✅ | div, curl, grad |
| Sobolev spaces | ⚠️ Limited | Basic definitions |
| PDEs | ⚠️ Limited | Linear theory |
| Lebesgue spaces | ✅ | Well-developed |
| Functional analysis | ✅ | Strong foundation |

### Tractable Partial Work

1. **2D Navier-Stokes** (see 2d-navier-stokes project)
   - Global existence IS known
   - Would be a major formalization achievement
   - ~3000-5000 lines estimated

2. **Stokes Equations** (linear case)
   - ∆u = ∇p, ∇·u = 0
   - Linear theory, more tractable
   - Foundation for full N-S

3. **Leray Solutions** (weak solutions)
   - Energy inequality
   - Existence without uniqueness
   - Fundamental theory

4. **Partial Regularity**
   - Caffarelli-Kohn-Nirenberg
   - Singular set is small (dimension ≤ 1)

## Formalization Challenges

### Primary Blocker: Advanced PDE Infrastructure

Formalizing even 2D N-S requires:

1. **Sobolev Spaces** (~1000 lines)
   - H^s spaces on domains
   - Trace theorems
   - Embeddings

2. **Energy Methods** (~1500 lines)
   - A priori estimates
   - Weak formulations
   - Galerkin approximations

3. **Regularity Theory** (~2000 lines)
   - Bootstrapping
   - Schauder estimates
   - Maximum principles

### The 3D-Specific Challenges

3D uniquely requires handling:
- **Enstrophy growth**: ∫|∇u|² can grow in 3D
- **Vortex stretching**: (ω·∇)u term
- **Critical scaling**: Equations are borderline in 3D

## Current State of Knowledge

### What's Known

- **Weak solutions exist** (Leray 1934)
- **Strong solutions exist locally** (Fujita-Kato)
- **Small data ⟹ global existence** (for ||u₀|| small)
- **Partial regularity** (singularities rare)
- **Unique for 2D** and for small 3D data

### What's Open

- Do 3D solutions stay smooth forever?
- Do finite-time singularities exist?
- If blowup occurs, what does it look like?

## Related Work

| File | Relevance |
|------|-----------|
| `2d-navier-stokes` | The tractable 2D case |

## Key References

- Leray, J. (1934). "Sur le mouvement d'un liquide visqueux"
- Ladyzhenskaya, O. (1969). "The Mathematical Theory of Viscous Incompressible Flow"
- Caffarelli, L., Kohn, R., Nirenberg, L. (1982). "Partial regularity"
- Constantin, P., Foias, C. (1988). "Navier-Stokes Equations"
- Fefferman, C. (2006). "Existence and Smoothness of the Navier-Stokes Equation" (Clay Problem Statement)

## Scouting Log

### Assessment: 2026-01-01

**Current Status**: BLOCKED - Heavy PDE/analysis infrastructure required

**Blocker Tracking**:
| Infrastructure | In Mathlib | Last Checked |
|----------------|------------|--------------|
| Basic PDEs | Yes | 2026-01-01 |
| Sobolev spaces | Limited | 2026-01-01 |
| Navier-Stokes | No | 2026-01-01 |
| Fluid mechanics | No | 2026-01-01 |

**Path Forward**:
1. Build Sobolev space infrastructure
2. Formalize 2D Navier-Stokes (known result)
3. Add partial regularity for 3D weak solutions
4. State the Millennium Problem precisely

**Related Active Work**: `2d-navier-stokes` attempts the tractable 2D case

**Next Scout**: Check Mathlib PDE development; 2D case is the near-term goal
