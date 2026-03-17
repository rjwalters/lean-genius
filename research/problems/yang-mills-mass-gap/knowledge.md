# Knowledge Base: Yang-Mills Existence and Mass Gap

## The Problem

The Yang-Mills problem asks for a rigorous mathematical foundation for quantum field theory - specifically, proving that the strong nuclear force has a "mass gap."

### Core Statement

> Prove that for any compact simple gauge group G, a non-trivial quantum Yang-Mills theory exists on R⁴ and has a mass gap Δ > 0.

The mass gap means the lightest particle in the theory has positive mass - there are no massless particles besides the vacuum.

### Why It Matters

1. **Physics Foundation**: Explains why nuclear force is short-range
2. **Quantum Field Theory**: Would put QFT on rigorous mathematical footing
3. **Standard Model**: Yang-Mills is the framework for particle physics
4. **Confinement**: Related to why quarks are never seen in isolation

## Historical Context

| Year | Physicist/Mathematician | Contribution |
|------|------------------------|--------------|
| 1954 | Yang, Mills | Introduced non-abelian gauge theories |
| 1960s | Glashow, Weinberg, Salam | Electroweak unification |
| 1973 | Gross, Wilczek, Politzer | Asymptotic freedom in QCD |
| 1974 | Wilson | Lattice gauge theory formulation |
| 2000 | Clay Institute | Named as Millennium Problem |

The theory works phenomenally well for physics - the issue is mathematical rigor.

## What This Means

### Yang-Mills Theory (Classical)

The classical Yang-Mills equations are:
- D*F = 0 (Yang-Mills equation)
- DF = 0 (Bianchi identity)

where F is the curvature of a connection A on a principal G-bundle, and D is the covariant derivative.

### Quantum Yang-Mills

Quantizing this theory means:
1. Defining a probability measure on field configurations
2. Making sense of path integrals
3. Proving existence in the continuum limit
4. Showing the mass gap property

### The Mass Gap

If the theory exists, the Hamiltonian H has:
- Ground state energy E₀ = 0 (vacuum)
- First excited state energy E₁ > 0
- Mass gap Δ = E₁ - E₀ > 0

This explains why nuclear force is short-range (unlike electromagnetism).

## What We Could Build

### In Mathlib Now

| Component | Status | Notes |
|-----------|--------|-------|
| Lie groups | ✅ | Well-developed |
| Principal bundles | ⚠️ Partial | Building |
| Connections | ⚠️ Partial | Some foundations |
| Curvature | ⚠️ Partial | Riemannian case |
| QFT axioms | ❌ | Not available |
| Path integrals | ❌ | Not available |

### Tractable Partial Work

1. **Classical Yang-Mills**
   - Define connections on principal bundles
   - State classical Yang-Mills equations
   - Prove basic gauge-theoretic facts

2. **2D Yang-Mills** (Exactly Solvable)
   - In 2D, the theory is exactly solvable
   - Migdal's formula gives explicit answers
   - Much simpler than 4D

3. **Lattice Gauge Theory**
   - Wilson's discrete approximation
   - Well-defined mathematically
   - Convergence to continuum is the hard part

4. **Gauge Group Theory**
   - SU(2), SU(3) structures
   - Representation theory
   - Lie algebra aspects

## The Mathematical Challenges

### Primary Blocker: Rigorous QFT

Constructive QFT is one of mathematics' hardest problems:

1. **Functional integrals** - "∫ e^{-S[φ]} Dφ" isn't defined rigorously
2. **Renormalization** - Removing infinities consistently
3. **Continuum limit** - Lattice → continuous space
4. **Non-perturbative effects** - Can't just Taylor expand

### What Constructive QFT Has Achieved

| Theory | Dimension | Status |
|--------|-----------|--------|
| φ⁴ | 2D | Constructed |
| φ⁴ | 3D | Constructed |
| φ⁴ | 4D | Not constructed |
| Pure Yang-Mills | 2D | Constructed |
| Pure Yang-Mills | 4D | Not constructed |

The 4D case is qualitatively harder.

## Why This Is So Hard

1. **Non-abelian** - Unlike electromagnetism, gluons interact with each other
2. **4 dimensions** - Critical dimension where UV divergences are marginal
3. **Asymptotic freedom** - Easy at high energy, hard at low energy
4. **Confinement** - Non-perturbative phenomenon

Even defining what "quantum Yang-Mills" means requires substantial work.

## Related Physics

The mass gap is connected to:
- **Quark confinement** - Why we never see free quarks
- **Glueballs** - Bound states of gluons (predicted but hard to detect)
- **Asymptotic freedom** - Interaction weakens at high energy

## Key References

- Yang, C.N., Mills, R. (1954). "Conservation of Isotopic Spin and Isotopic Gauge Invariance"
- Wilson, K. (1974). "Confinement of Quarks"
- Jaffe, A., Witten, E. (2000). "Quantum Yang-Mills Theory" (Clay Problem Statement)
- Glimm, J., Jaffe, A. (1987). "Quantum Physics: A Functional Integral Point of View"

## Scouting Log

### Assessment: 2026-01-01

**Current Status**: BLOCKED - Requires QFT framework not in Mathlib

**Blocker Tracking**:
| Infrastructure | In Mathlib | Last Checked |
|----------------|------------|--------------|
| Lie groups | Yes | 2026-01-01 |
| Connections | Partial | 2026-01-01 |
| QFT axioms | No | 2026-01-01 |
| Path integrals | No | 2026-01-01 |

**Path Forward**:
1. Classical Yang-Mills on principal bundles
2. 2D Yang-Mills (exactly solvable case)
3. Lattice gauge theory foundations
4. Long-term: constructive QFT

**Reality Check**: This is arguably the hardest Millennium Problem mathematically. Even stating it precisely requires substantial infrastructure.

**Next Scout**: Long-term project - QFT formalization is a major undertaking

---

## Session 2026-02-21 (Session 1) - SU(2) Representation Theory and Center Symmetry

**Mode**: REVISIT (pool status correction + fresh work on in-progress problem)
**Outcome**: progress

### What I Did
- Fixed pool status inconsistencies (2d-navier-stokes, navier-stokes-existence, bounded-prime-gaps marked as skipped but were completed)
- Claimed yang-mills-mass-gap for fresh iteration
- Added Part XVIII: SU(2) Representation Theory (Casimir values)
- Added Part XIX: Center Symmetry Z_N
- Fixed 3 pre-existing build errors (migdal_area_law, correlation_decay_rate, partition_dominated_by_ground_state)
- All new theorems proved with 0 sorries

### Key Findings
- SU(2) spin-j Casimir: C₂(j) = j(j+1); for j=1/2 gives 3/4, j=1 gives 2
- SU(2) string tension from Migdal formula: σ = g²·(3/4)/(2·2) = 3g²/16
- Z_2 center classification: ω²=1 and |ω|=1 gives ω ∈ {1, -1} via polynomial factoring
- Confinement ↔ center symmetry unbroken: confined phase has ω·P = 0 = P for all P
- Deconfinement → center symmetry broken: ∃P with -P ≠ P when P ≠ 0

### Files Modified
- `proofs/Proofs/YangMillsMassGap.lean`: 1133 → 1365 lines (+232), 0 sorries, fixed 3 build errors
- `src/data/research/problems/yang-mills-mass-gap.json`: Updated knowledge fields
- `research/problems/yang-mills-mass-gap/knowledge.md`: This session log

### Next Steps
- Add SU(2) heat kernel expansion: Z = Σ (2j+1)² exp(-j(j+1)·A/β)
- Instantiate MigdalFormula with concrete SU(2) values
- Add center symmetry group structure (CenterElement forms a group under multiplication)
- Explore SU(3) Z_3 center with complex cube roots of unity

---

## Session 2026-03-16 (Session 2) - Schwinger Model, Gradient Flow, Polyakov Loop, Glueball Spectrum

**Mode**: REVISIT (building on Parts I-LVII, 6545 lines)
**Outcome**: progress

### What I Did
- Added Part LVIII: Schwinger Model (QED₂) — exact mass gap m = e/√π
- Added Part LIX: Yang-Mills Gradient Flow (Lüscher 2010) — smoothing framework
- Added Part LX: Polyakov Loop — finite temperature deconfinement order parameter
- Added Part LXI: Glueball Spectrum — lightest state (0⁺⁺) IS the mass gap
- All new theorems proved with 0 sorries, 0 new build errors

### Key Theorems Proved (non-trivial)
- `schwinger_mass_positive`: m = e/√π > 0 for the Schwinger model
- `schwinger_mass_sq_eq`: m² = e²/π verified algebraically
- `schwinger_tension_mass_relation`: σ = m²/2 connecting confinement to mass gap
- `eta_prime_mass_positive`: Multi-flavor η' mass > 0
- `eta_prime_one_flavor_mass_sq`: N_f=1 reduces to standard Schwinger mass
- `smoothing_radius_pos`: Gradient flow smoothing radius positive at t > 0
- `su3_energy_coefficient`: SU(3) coefficient = 3/(16π²) verified
- `potential_below_Tc`/`potential_above_Tc`: Polyakov potential curvature changes sign at T_c
- `deconfined_minimum_pos`: Deconfined phase minimum |P| > 0
- `mass_gap_is_scalar_glueball`: 0⁺⁺ lighter than 2⁺⁺ and 0⁻⁺
- `glueball_mass_hierarchy`: Complete mass ordering proved

### Files Modified
- `proofs/Proofs/YangMillsMassGap.lean`: 6545 → 7248 lines (+703), 0 new sorries
- `src/data/research/problems/yang-mills-mass-gap.json`: Updated knowledge
- `research/problems/yang-mills-mass-gap/knowledge.md`: This session log

### Next Steps
- Add Witten's theta vacuum and large-N volume independence
- Add 't Hooft anomaly matching (constrains IR spectrum)
- Add Banks-Zaks conformal window analysis
- Explore dimensional reduction: 4D → 3D EQCD at high T
