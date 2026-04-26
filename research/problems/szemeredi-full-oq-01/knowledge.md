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

## Session 2026-04-26 (Session 3) — T-Invariance + Assembly Skeleton

**Mode**: REVISIT (continuing Session 2 work)
**Outcome**: progress (Parts X-XII added, assembly theorem structurally complete)

### What I Did
- Extended `FurstenbergCorrespondenceOQ01.lean` from 529 to 674 lines
- Added Parts X (T-invariance), XI (density at limit), XII (assembly)
- The `furstenberg_correspondence` theorem is now structured with all components assembled

### Infrastructure Added (sorries for the hard analytic steps)

| Item | Type | Location | Status |
|------|------|----------|--------|
| `cesaroMeasure_map_shift` | Theorem | OQ01.lean:531 | sorry (~15L to prove) |
| `shift_invariant_of_limit` | Local axiom | OQ01.lean:550 | axiom |
| `density_preserved_at_limit` | Theorem | OQ01.lean:572 | sorry (~30L to prove) |
| `furstenberg_correspondence` | Theorem | OQ01.lean:594 | 1 sorry in density step |

### Key Mathematical Findings

**`cesaroMeasure_map_shift` is exact** (not approximate):
- T_*(cesaroMeasure x N) = cesaroMeasure (shift x) N
- Proof: T_*(Σ δ_{T^n x}) = Σ δ_{T^{n+1} x} = Σ δ_{T^n (Tx)} via `Function.iterate_succ_apply'`
- No approximation/boundary terms needed — the telescoping is exact

**T-invariance argument**: If μ_k → μ weak-* and N_k → ∞, then T_*(μ) = μ:
- T_*(μ_k) = cesaroMeasure(shift x_k, N_k) by `cesaroMeasure_map_shift`
- |∫f d(cesaroMeasure x N) - ∫f d(cesaroMeasure shift x N)| = (1/N)|f(x) - f(T^N x)| ≤ 2‖f‖/N → 0
- Hence T_*(μ_k) ≈ μ_k, and both tend to μ, so T_*(μ) = μ

**`density_preserved_at_limit`** uses Portmanteau for closed sets:
- `cylinderZero` is clopen (open and closed) in Cantor space
- Portmanteau: if μ_k → μ and F closed, then `limsup_k μ_k(F) ≤ μ(F)`
- Since all μ_k(F) ≥ δ, limsup ≥ δ, so μ(F) ≥ δ
- Relevant Mathlib lemma: `ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`

**Assembly structure** in `furstenberg_correspondence`:
1. For each k, `density_lower_bound A hδ hd (k+1)` gives (a_k, N_k) with N_k ≥ k+1
2. N_k ≥ k+1 implies N_k → ∞ (proved via `Filter.tendsto_atTop_atTop.mpr`)
3. Prokhorov extracts φ, μ with μ_seq(φ k) → μ
4. T-invariance: `shift_invariant_of_limit` applied to subsequence
5. Density: `density_preserved_at_limit` applied to subsequence

### Remaining Sorries

1. **`cesaroMeasure_map_shift`** (~15 lines): `Measure.map_smul`, `Measure.map_sum` (with measurability),
   `Measure.map_dirac shift_measurable`, `Function.iterate_succ_apply'`
2. **`density_preserved_at_limit`** (~30 lines): `ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`
   (or Portmanteau equivalent) for clopen `cylinderZero`
3. **Assembly density sorry** (~5-10 lines): `hdensity (φ k)` matches `(μ_seq (φ k) : Measure _) cylinderZero`
   by unfolding the let-binding (likely closes with `simp only [μ_seq]`)

### Next Steps
1. Prove `cesaroMeasure_map_shift`: use `Measure.map_smul`, `Measure.map_sum` with measurability,
   `Measure.map_dirac`, `Function.iterate_succ_apply'` (15 lines)
2. Prove `density_preserved_at_limit`: check Mathlib for `ProbabilityMeasure.limsup_measure_closed_le_of_tendsto`
   or equivalent Portmanteau lemma for closed sets (30 lines)
3. Close the assembly density sorry: unfold `μ_seq` def to match `hdensity`
4. Attempt `seqCompact_probabilityMeasure_cantor` via `LevyProkhorov` metrization (~150-200 lines)

---

## Dead Ends

- Cannot enumerate AP witnesses case-by-case (infinitely many cases)
- Cannot use Poincaré recurrence alone for k ≥ 3 (structural argument needed)
