# Erdős #986: Ramsey Number Lower Bounds (Incomplete-01)

**Goal**: Eliminate the 1 sorry in `Erdos986Problem.lean`

## Session 2026-04-03 (Session 1) - Fix false sorry

**Mode**: FRESH
**Outcome**: completed

### What I Did
- Read `proofs/Proofs/Erdos986Problem.lean` — found 1 sorry in `RamseyExists` inside `where` clause of `RamseyNumber`
- Identified that the sorry is for a FALSE statement: asymmetric colorings `Fin N → Fin N → Bool` can avoid all monochromatic cliques by making every pair "mixed" (f(i,j)=true, f(j,i)=false), so no N satisfies the property
- Found `proofs/Proofs/RamseysTheorem.lean` has a complete proof of Ramsey's theorem for symmetric `EdgeColoring` colorings (`RamseysTheorem.ramsey_theorem`)
- Replaced the false `where` clause with a clean definition: `(RamseysTheorem.ramsey_theorem k n h.1 h.2).choose`
- Also fixed 3 pre-existing floating docstrings (`/-- ... -/` not attached to declarations) causing parse errors
- Added `noncomputable` to `exponent_gap` (uses real division)
- Build: clean, 0 sorries, 0 warnings (3079 jobs)

### Key Findings
- Asymmetric coloring formulation is provably false for k,n ≥ 2
- `RamseysTheorem.ramsey_theorem` is available and proven in this project
- The gallery proof for erdos-986 (`spencer_1977`, `mattheus_verstraete_2023`, etc.) uses axioms that work fine with the corrected `RamseyNumber`

### Files Modified
- `proofs/Proofs/Erdos986Problem.lean`

### Next Steps
- PR #9157 merged when deployer runs
