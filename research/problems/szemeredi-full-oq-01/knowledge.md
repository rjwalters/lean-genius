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

## Session 2026-04-26 (Session 2) — Cesàro Infrastructure Build

**Mode**: FRESH (continuing claim on szemeredi-full-oq-01)
**Outcome**: progress (ACT phase — meaningful infrastructure built)

### What I Did
- Extended `FurstenbergCorrespondenceOQ01.lean` from 285 to 529 lines
- Built complete Cesàro measure infrastructure in new Parts VIII and IX
- Proved the elementary half of the Furstenberg correspondence without compactness
- Isolated Prokhorov sequential compactness as the minimal remaining local axiom

### Infrastructure Built (all fully proved, 0 sorries)

| Item | Type | Location |
|------|------|----------|
| `HasUpperDensityGe` | Definition | OQ01.lean:308 |
| `finsetDirac_apply` | Theorem | OQ01.lean:316 |
| `cesaroMeasure` | Definition | OQ01.lean:334 |
| `cesaroMeasure_isProbability` | Theorem | OQ01.lean:340 |
| `mem_cylinderZero_shifted` | Theorem | OQ01.lean:364 |
| `cesaroMeasure_cylinderZero` (orbit-density formula) | Theorem | OQ01.lean:372 |
| `density_lower_bound` (elementary half of correspondence) | Theorem | OQ01.lean:404 |
| `seqCompact_probabilityMeasure_cantor` | Local axiom | OQ01.lean:484 |

### Key Mathematical Findings

- `finsetDirac_apply`: sum of Dirac measures applied to a measurable set equals the
  cardinality of the fiber; proved via `Finset.sum_boole` + `simp_rw`
- `cesaroMeasure_isProbability`: uses `ENNReal.inv_mul_cancel` with `Finset.card_range`
- `density_lower_bound` (the non-trivial part): proved via Finset bijection `n ↦ n-a`
  mapping Ico-filter to range-filter, then ENNReal arithmetic via
  `ENNReal.le_div_iff_mul_le` + `ENNReal.ofReal_mul` + `ENNReal.ofReal_natCast`
- The `furstenberg_correspondence` axiom in `FurstenbergCorrespondence.lean` now reduces to:
  1. `seqCompact_probabilityMeasure_cantor` (local axiom, ~150-200 lines to prove)
  2. ~50 lines: T-invariance of limit measures (telescoping integral estimate)
  3. ~30 lines: density preservation at limit (lower semi-continuity of measures)

### Lessons on ENNReal API
- `ENNReal.le_div_iff_mul_le` (not `le_div_iff₀`) needed for ENNReal division
- `ENNReal.ofReal_mul` + `ENNReal.ofReal_natCast` for ℝ→ENNReal conversion chains
- `open Classical` required for `DecidablePred` in `Finset.filter` with set predicates
- Bijection `card_bij` with `n ↦ n-a` (not `n ↦ n+a`) for Ico→range filter cardinality

### Next Steps
1. Prove T-invariance: |∫f d(T_*(μ_{a,N})) - ∫f dμ_{a,N}| ≤ 2‖f‖_sup/N → 0 (~50 lines)
2. Prove density lower semi-continuity at limit: μ(B₀) ≥ δ from density_lower_bound (~30 lines)
3. Prove `seqCompact_probabilityMeasure_cantor` via Mathlib Prokhorov ingredients (~150-200 lines)
4. Assemble into a clean proof of `furstenberg_correspondence` (replaces the axiom)

---

## Session 2026-04-27 (Session 5) — `limit_invariant_on_cylinder` Proof + File Build Blocker

**Mode**: REVISIT (continuing claim on szemeredi-full-oq-01)
**Outcome**: progress (proof structure written, but file build is BLOCKED)

### What I Did

1. Wrote a complete proof for the remaining sorry `limit_invariant_on_cylinder`
   in `FurstenbergCorrespondenceOQ01.lean:748` (replaces the ~30-line analysis sorry).
2. Discovered the file has **35 pre-existing Mathlib API drift errors** that prevent
   local Docker build validation.

### Proof Structure for `limit_invariant_on_cylinder` (60 lines)

The proof uses standard Mathlib weak-convergence machinery:

- `ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'` (ENNReal-level Portmanteau)
- For clopen S: `frontier S = ∅` ⟹ `μ(frontier S) = 0`, so the lemma applies.
- `ENNReal.tendsto_nat_nhds_top` + `ENNReal.continuous_inv` ⟹ `(Ns k + 1)⁻¹ → 0`.
- `ENNReal.Tendsto.add` (with `μ S ≠ ⊤` from `IsProbabilityMeasure`).
- `le_of_tendsto_of_tendsto'` to pass telescoping bounds to limits.

Both directions: `μ(shift⁻¹S) ≤ μ(S)` (from `cesaroMeasure_preimage_le`) and
`μ(S) ≤ μ(shift⁻¹S)` (from `cesaroMeasure_preimage_ge`), then `le_antisymm`.

### CRITICAL BLOCKER: File Does Not Build

The `FurstenbergCorrespondenceOQ01.lean` file has 35 errors when built with
the pinned Mathlib `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0).

Sample errors (Mathlib API drift):
- `error: Proofs/FurstenbergCorrespondenceOQ01.lean:101:10: Unknown identifier`
  `isOpen_eq_of_isOpen_singleton`
- `error: Proofs/FurstenbergCorrespondenceOQ01.lean:239:39: Unknown constant`
  `Finite.instCompactSpace`
- `error: Proofs/FurstenbergCorrespondenceOQ01.lean:71:14: unsolved goals` (in
  `shift_iterate`, originally proved by `Function.iterate_succ'` + `ring_nf`)
- `error: Proofs/FurstenbergCorrespondenceOQ01.lean:146:2: Tactic split failed`
  (in `shift_indicator_zero` — `simp` no longer reduces to `if`)

The recent fix PR #13069 ("omega → rwa+ring") only checked one local fix; its test
plan checkbox was unchecked when merged. The repo has no Lean CI (only labeling
workflows run on PRs). So the file has been silently broken since the last successful
build (likely #12847 from 2026-03-17 with an earlier Mathlib pin).

### Implication for the Project

`FurstenbergCorrespondenceOQ01.lean` cannot be added to until the file is
upgraded to current Mathlib. Adding more sorry-eliminations on top of broken
code is fake formalization. The right next step is a **dedicated Mathlib upgrade
session** to repair all 35 errors before any further axiom-elimination work.

The proof I wrote is structurally sound (uses well-known Mathlib lemmas) and should
work once the file's surrounding context is repaired. Until then, my contribution
is: (a) the proof structure documented above, and (b) this blocker discovery.

### Next Steps (Updated)

1. **PRIORITY**: Mathlib upgrade session to fix all 35 errors in
   `FurstenbergCorrespondenceOQ01.lean`. Categories:
   - Renamed lemmas (e.g., `isOpen_eq_of_isOpen_singleton`)
   - Removed instances (`Finite.instCompactSpace` — likely now via `instCompactSpaceFinite`)
   - Tactic behavior changes (`split` no longer applicable; need `by_cases` or pattern match)
   - `simp` lemma set changes (causing `setIndicator` simplification to fail)
2. After file builds: the `limit_invariant_on_cylinder` proof I wrote replaces the sorry.
3. Then prove `seqCompact_probabilityMeasure_cantor` to fully eliminate the
   Prokhorov axiom (~150-200 lines).

### Lessons

- **Local build validation is essential** — but is BLOCKED when the surrounding
  file has pre-existing errors from upstream API drift.
- **CI must run Lean builds on PRs** to prevent silent rot. The repo currently
  has no Lean build workflow (only labeling). Recommend adding one.
- For files with no CI coverage, recent commits cannot be trusted to actually
  build, regardless of the commit message.

---

## Dead Ends

- Cannot enumerate AP witnesses case-by-case (infinitely many cases)
- Cannot use Poincaré recurrence alone for k ≥ 3 (structural argument needed)
- Cannot add new theorems on top of broken file (fake formalization;
  Mathlib upgrade required first)
