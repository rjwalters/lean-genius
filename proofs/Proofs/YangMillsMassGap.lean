import Proofs.YangMills.Core
import Proofs.YangMills.Classical
import Proofs.YangMills.Quantum
import Proofs.YangMills.Exploration

/-
# Yang-Mills Existence and Mass Gap

This is a backward-compatibility wrapper. The formalization is split into modules:

## Rigorous Foundation (~450 lines)
- **Core**: Gauge groups, Lie algebras, Spacetime, Minkowski metric [RIGOROUS]
- **Classical**: Field strength, YM action, gauge invariance, Maxwell [RIGOROUS + 1 axiom]
- **Quantum**: WightmanQFT (simplified), mass gap definition, Millennium Problem [AXIOMATIC]

## Exploratory Content (~28K lines)
- **Exploration**: Wilson loops, lattice gauge theory, 2D exact solutions, transfer matrix,
  confinement mechanisms, anomalies, SUSY, AdS/CFT, constructive QFT, and more [MIXED]

## What Is Proven vs Open

| Component | Status |
|-----------|--------|
| Gauge group / Lie algebra | PROVEN (Mathlib) |
| Minkowski metric properties | PROVEN |
| Field strength antisymmetry | PROVEN |
| Gauge transformation group | PROVEN |
| Maxwell as U(1) Yang-Mills | DEFINED |
| Lattice plaquette gauge invariance | PROVEN |
| 2D Yang-Mills (Migdal formula) | PROVEN |
| Transfer matrix mass gap (finite vol) | PROVEN |
| Quantum Yang-Mills existence (4D) | **OPEN CONJECTURE** |
| Mass gap positivity (4D) | **OPEN CONJECTURE** |

## Axiom Count: 16

1 explicit `axiom` declaration (gaugeTransform — definitional).
~15 structure-encoded assumptions in CompactSimpleGaugeGroup, GaugeLieAlgebra,
WightmanQFT, YangMillsAction, FieldStrength, Instanton, EnergyMomentumTensor.

## Key Limitations

- WightmanQFT uses bounded Hamiltonian (should be unbounded)
- Mass gap is expectation-value based (should be spectral)
- No fiber bundles, connections, or Sobolev spaces
- ~23% of theorems in Exploration are trivial (numerology, tautologies)
- ~64% of Exploration is heuristic/speculative physics
-/
