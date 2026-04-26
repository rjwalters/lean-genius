# Knowledge Base: szemeredi-full-oq-01

Furstenberg ergodic-theoretic proof of Szemerédi's theorem.

---

## Problem Understanding

Szemerédi's theorem: every set A ⊆ ℕ with positive upper Banach density contains
arithmetic progressions of every finite length. Furstenberg (1977) proved this via
ergodic theory, reducing it to the Multiple Recurrence Theorem.

The `FurstenbergCorrespondence.lean` file already exists with substantial infrastructure.

---

## Session 2026-04-26 (Session 1) — Survey + Architecture Map

**Mode**: FRESH (new problem claim)
**Outcome**: scouted (ORIENT phase)

### What I Did
- Read full `FurstenbergCorrespondence.lean` (248 lines)
- Mapped all proved and axiomatized components
- Assessed feasibility of formalizing the two remaining axioms

### Architecture Map

| Component | Status | Notes |
|-----------|--------|-------|
| `HasUpperDensityGe` definition | ✅ Proved | upper Banach density |
| `System` structure (prob. m.p. system) | ✅ Proved | wraps MeasurePreserving |
| `poincare_return` (one return) | ✅ Proved | via Mathlib Conservative |
| `poincare_frequently` (many returns) | ✅ Proved | via Mathlib Conservative |
| `szemeredi_k2_ergodic` | ✅ Proved | 2-APs from Poincaré |
| `szemeredi_ergodic` (full, all k) | ✅ Assembled | depends on both axioms |
| `furstenberg_correspondence` | ❌ Axiom | ~500 lines to build |
| `multiple_recurrence_ge3` | ❌ Axiom | ~2000+ lines, blocked |

### Key Findings

- Mathlib has: `MeasurePreserving`, `Conservative`, Poincaré recurrence,
  `ProbabilityMeasure` topology
- `szemeredi_k2_ergodic` works today using only Poincaré recurrence from Mathlib
- `furstenberg_correspondence` needs: Cesàro averages of measures + weak-* compactness
  (Prokhorov's theorem) — borderline BUILD (~500 lines, depends on Prokhorov in Mathlib)
- `multiple_recurrence_ge3` needs: ergodic decomposition, compact extension / weak mixing
  dichotomy, van der Waerden's theorem as base — TRULY BLOCKED (~2000+ lines)

### Mathlib Gaps Identified

1. Cesàro averages of probability measures (weak-* construction for shift system)
2. Prokhorov's theorem / weak-* compactness for probability measures on Polish spaces
3. Ergodic decomposition theorem
4. Compact extension / weak mixing tower for m.p. systems
5. Van der Waerden's theorem (useful as combinatorial base case for k≥3)

### Next Steps

1. Check if Mathlib 2025/2026 added Prokhorov's theorem or ergodic decomposition
2. If Prokhorov is available, furstenberg_correspondence (~500 lines) becomes feasible in
   a dedicated session
3. Van der Waerden's theorem could be proved combinatorially (~300 lines) as infrastructure
4. multiple_recurrence_ge3 requires multi-session investment (TIER S problem)

---

## Dead Ends

- Cannot enumerate AP witnesses case-by-case (infinitely many cases)
- Cannot use Poincaré recurrence alone for k ≥ 3 (structural argument needed)
