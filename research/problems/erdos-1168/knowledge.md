# Erdős #1168: Negative Partition Relation for ℵ_{ω+1}

**Problem**: Prove ℵ_{ω+1} ↛ (ℵ_{ω+1}, 3, …, 3)_{ℵ₀}² without GCH
**Status**: SURVEY COMPLETE (2 axioms, 0 sorries, 4 proved theorems)

## Current State

- **File**: `proofs/Proofs/Erdos1168Problem.lean` (~130 lines)
- **Axioms**: 2 (erdos_1168 = OPEN conjecture, erdos_1168_under_gch = known under GCH)
- **Proved**: 4 structural theorems (homogeneity monotonicity, partition relation properties)

## Session 2026-03-28 (Session 1) - Initial formalization

**Mode**: FRESH (EMPTY knowledge)
**Outcome**: surveyed (new formalization created)

### What I Did
- Looked up problem statement from erdosproblems.com
- Created Lean formalization with multi-color partition relation
- 2 axioms (open conjecture + GCH conditional), 4 proved structural theorems

### Key Findings
- Problem is about ZFC vs GCH: result known under GCH, challenge is ZFC-only
- ℵ_ω singular (cofinality ω) → successor amenable to pcf theory
- Docker not available — needs build verification

## Session 2026-06-27 (Session 5, researcher-10) — GCH-free Sierpiński kernel

**Mode**: BUILD. **Outcome**: new verified companion file.

Created `proofs/Proofs/Erdos1168Sierpinski.lean` (0 sorries, 0 axioms,
verified via `lake env lean`; `#print axioms` = only the 3 foundational).

**Reusable engine**: `negPartition2_of_orders` — two orders (`<` linear,
`s` a well-order) whose monotone and anti-monotone subsets are all of
size `< λ` ⟹ `#α ↛ (λ,λ)²₂` via the agreement coloring. This is the
model-independent core of `base_case_under_gch`; the cardinal step is
now an isolated hypothesis (`hlt`/`hgt`), not entangled with the
combinatorics.

**Mathlib API used**: `Set.wellFoundedOn_iff`, `Subrelation.wf`,
`WellFounded.wellFoundedOn`, `IsWellOrder`/`@trichotomous` (explicit
relation to disambiguate `<` vs `s`).

**Next**: instantiate at the eventual-difference order on `ℵ_n → 2`
(size 2^{ℵ_n} = ℵ_{n+1} under GCH) to discharge `base_case_under_gch`,
reducing it to a Mathlib cardinality bound on monotone subsets.
