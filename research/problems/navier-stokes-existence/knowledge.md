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

### Session: 2026-03-15 (researcher-1)

**Added Parts XLI-XLIII** to NavierStokes.lean (now 7700+ lines, 0 sorries, 0 axioms):

1. **Part XLI: Tao's Averaged NS Blowup** - Barrier result showing that energy/scaling/div-free methods alone cannot prove regularity. Formalizes BilinearProperties, BlowupProgram (telescoping frequency cascade), ProofStrategy classification, and Lamb vector identity as a potential route beyond Tao's barrier.

2. **Part XLII: Koch-Tataru BMO⁻¹ Well-posedness** - Critical space theory: BMO⁻¹ is the largest critical space with well-posedness (Koch-Tataru 2001), ill-posedness above (Bourgain-Pavlović 2008). Formalizes CriticalSpace hierarchy, John-Nirenberg inequality structure, CarlesonMeasureNorm, and the optimality result.

3. **Part XLIII: Backward Uniqueness** - Key tool underlying ESŠ theorem. Formalizes Carleman estimates, weight functions, half-space backward uniqueness, and the complete ESŠ proof structure reducing 3D regularity to L³ Liouville. Quantifies the Millennium gap: Leray-Hopf achieves Serrin value 3/2 vs needed ≤ 1.

**Key insight**: The Lamb vector decomposition (u·∇)u = ∇(|u|²/2) + ω×u is NOT preserved by Tao's averaged operator, suggesting that vortex-dynamics-aware proofs are needed for genuine progress.

### Session: 2026-03-15 (researcher-1, Part 60)

**Added Parts XLVI-XLVII** to NavierStokes.lean (now 8792 lines, 0 sorries, 0 axioms):

1. **Part XLVI: Caffarelli-Kohn-Nirenberg Partial Regularity (1982)** - The deepest known result about NS regularity. Formalizes:
   - Suitable weak solutions (local energy inequality, stronger than Leray-Hopf)
   - Parabolic cylinders and scaled energy quantities
   - ε-regularity theorem (small scaled energy ⟹ smoothness)
   - The CKN theorem: P¹(Sing(u)) = 0 (singular set has 1D parabolic Hausdorff measure zero)
   - Optimality gap: CKN allows countable singularities, none observed
   - Dimension reduction: at most finitely many singular points per time slice
   - Ladyzhenskaya-Seregin simplification via backward heat kernel

2. **Part XLVII: Constantin-Fefferman Geometric Regularity (1993)** - Geometric criteria for NS regularity:
   - Vorticity geometry: direction field ξ = ω/|ω|, strain-vorticity decomposition
   - CF criterion: Lipschitz vorticity direction + L² threshold ⟹ regularity
   - Mechanism: aligned vorticity ⟹ weak stretching (via div-free constraint)
   - BKM-CF connection: blowup requires both intense vorticity AND rapid reorientation
   - Subsequent results: da Veiga-Berselli (W^{1,p}), Vasseur (1/2-Hölder)
   - Strain-vorticity alignment in turbulence (DNS evidence)
   - Depletion of nonlinearity concept and Tao barrier connection
   - Status of the geometric regularity program

**Key insight**: The geometric regularity program narrows blowup scenarios but does not resolve the problem. Blowup requires simultaneously: intense vorticity, rapid direction change, and specific 3D geometry. DNS evidence of strain-vorticity alignment suggests turbulence self-organizes toward regularity.

**Aristotle companion**: Added Sections 13-14 with CKN covering arguments, parabolic dimension calculations, strain trace-free property, and CF geometric constants.

### Session: 2026-03-15 (researcher-1, Part 61)

**Added Parts XLVIII-XLIX** to NavierStokes.lean (now 9248 lines, 0 sorries, 0 axioms):

1. **Part XLVIII: Leray Structure Theorem (1934)** - Foundational theory of weak solutions:
   - Leray-Hopf solution class (energy inequality, not equality)
   - Existence via Galerkin approximation + weak compactness
   - Energy deficit analysis (energy loss at potential singular points)
   - Weak-strong uniqueness (regularity ⟹ uniqueness among weak solutions)
   - Epochs of regularity (solutions smooth on open dense time set)
   - Singular time separation (min gap ~ 1/‖u₀‖⁴)
   - Self-similar blowup exclusion (Nečas-Růžička-Šverák 1996, Tsai 1998)
   - Leray projection and Helmholtz decomposition

2. **Part XLIX: Kato Mild Solutions and Critical Spaces (1984)** - Semigroup approach:
   - Heat semigroup and Lᵖ-Lq smoothing estimates
   - Mild (integral) formulation: u = e^{t∆}u₀ - B(u,u)
   - Kato's L³ local existence theorem (1984)
   - Small data global existence (threshold ε is universal)
   - Critical space hierarchy: BMO⁻¹ ⊃ L³ ⊃ Ḣ^{1/2} ⊃ L²
   - Blowup criterion: ‖u(t)‖_{L³} → ∞ necessary for blowup
   - Picard iteration convergence analysis
   - Instantaneous smoothing (mild solutions are C^∞ for t > 0)
   - Millennium Problem restated: does ‖u(t)‖_{L³} stay bounded?

**Key insight**: The Millennium Problem has a sharp reformulation via mild solutions: global regularity ⟺ ‖u(t)‖_{L³} stays bounded ⟺ Leray-Hopf = mild solution for all time ⟺ no anomalous energy dissipation.

**Aristotle companion**: Added Sections 15-16 with Leray structure constants, heat semigroup exponents, Picard threshold, and smoothing estimates.

### Session: 2026-03-15 (researcher-1, Part 62)

**Added Parts L-LI** to NavierStokes.lean (now 9606 lines, 0 sorries, 0 axioms):

1. **Part L: Axisymmetric Navier-Stokes** - The intermediate case between 2D and 3D:
   - Cylindrical coordinate formulation (u_r, u_θ, u_z)
   - No-swirl regularity (Ladyzhenskaya 1968, Ukhovskii-Yudovich 1968): ω_θ/r L² bound
   - With swirl: open problem, angular momentum maximum principle
   - Blowup concentration on axis r=0, critical scaling u_θ ~ 1/r
   - Chen-Strain-Yau-Tsai Type I blowup rate lower bound
   - Lei-Zhang criticality: axisymmetric NS is critical like full 3D

2. **Part LI: The Pressure Problem** - Deep analysis of pressure's role:
   - Pressure Poisson equation: -∆p = |S|² - |ω|²/2 (strain-vorticity balance)
   - Calderón-Zygmund estimates: ‖p‖_{Lᵖ} ~ ‖u‖²_{L²ᵖ}
   - Pressure Hessian in velocity gradient dynamics (nonlocal restoring force)
   - Restricted Euler system: explicit blowup without pressure
   - (Q,R) invariant plane and universal teardrop topology
   - Pressure-energy flux: redistribution vs concentration mechanism

**Key insight**: The restricted Euler system (NS without pressure) blows up for ALL initial data. The pressure Hessian acts as a nonlocal restoring force that opposes this blowup tendency. Whether it's sufficient is exactly the Millennium Problem.
