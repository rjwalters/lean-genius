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

## Session 2026-05-08 (Session 2) — Bookkeeping update (researcher-3)

**Mode**: REVISIT
**Outcome**: completed (no new mathematical work)

### What I Did
- Verified `proofs/Proofs/Erdos986Problem.lean` on `origin/main`: 224 lines, 0 sorries, 3 axioms (`spencer_1977`, `mattheus_verstraete_2023`, `bohman_keevash_2010`)
- Verified `src/data/proofs/erdos-986/meta.json` already reflects accurate state (`status: "axiomatized"`, `badge: "axiom"`, `sorries: 0`, `axiomCount: 3`)
- Updated `src/data/research/problems/erdos-986-incomplete-01.json` `phase`/`status`/`currentState.phase` from `NEW`/`active` → `COMPLETED`/`completed` (S1 work was done but JSON bookkeeping was never advanced)
- Did NOT add new theorems or attempt to prove existing axioms — see classification below

### Axiom Classification (per role guidance)
- `spencer_1977`: Probabilistic alterations + Lovász Local Lemma; major Mathlib gap, deep result. NOT provable in a single session.
- `mattheus_verstraete_2023`: Pseudorandom hypergraph construction from a 2023 breakthrough paper (arXiv:2306.04007). NOT in Mathlib. NOT provable in a single session.
- `bohman_keevash_2010`: H-free process analysis with martingale concentration. NOT in Mathlib. NOT provable in a single session.

All three are genuine research-level open contributions to the Lean record; they cannot be discharged from Mathlib. Conversion to `theorem ... := by sorry` would be lossy (loses provenance) and would not constitute progress.

### Files Modified
- `src/data/research/problems/erdos-986-incomplete-01.json` (phase/status bookkeeping)

### Outcome (honest)
This is a tracker-correction session, not a proof advance. The "incomplete-01" goal (eliminate 1 sorry) was already done in S1. The pool entry is now correctly marked `COMPLETED` so future researchers won't reclaim it.

The full Erdős #986 conjecture for k ≥ 5 remains a genuinely open mathematical problem and is out of scope for this slug.
