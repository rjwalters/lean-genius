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

## Session 2026-04-27 (Session 4) — Mathlib Gap Audit for `seqCompact_probabilityMeasure_cantor`

**Mode**: REVISIT (RICH knowledge tier, score 30)
**Outcome**: SPEC — disk pressure (1.4 GiB free) blocks Docker verification, so this session
contributes a Mathlib API map only. No Lean source modifications.

### What's Available in Mathlib v4.26 (Verified by Source Inspection)

| Mathlib Theorem | Module | Use |
|-----------------|--------|-----|
| `instance MetrizableSpace (ProbabilityMeasure X)` | `LevyProkhorovMetric.lean:717` | metrizability ⇒ first-countable |
| `instance FirstCountableTopology.seq_compact_of_compact` | `Topology/Sequences.lean:273` | compact + first-countable ⇒ SeqCompactSpace |
| `IsTightMeasureSet.of_compactSpace` | `Tight.lean:101` | every set tight on compact space |
| `LevyProkhorov.probabilityMeasureHomeomorph` | `LevyProkhorovMetric.lean:695` | `ProbabilityMeasure X ≃ₜ LevyProkhorov (ProbabilityMeasure X)` |
| `WeakDual.isCompact_closedBall` | `Analysis/Normed/Module/WeakDual.lean:47` | Banach-Alaoglu (Path B alternative) |

### What is **MISSING** in Mathlib v4.26 (Confirmed by Search)

- **No instance `CompactSpace (ProbabilityMeasure X)`** for compact metrizable separable X.
  Searched: `grep -rn "CompactSpace.*ProbabilityMeasure"` returns 0 hits in Mathlib MeasureTheory.
- **No direct sequential Prokhorov theorem**: `tight + complete second-countable ⇒ sequentially
  compact set of finite measures` is not stated as a lemma.

### Two Construction Paths

#### Path A — Levy-Prokhorov metric (RECOMMENDED, ~150-200 lines)

Pre-conditions on `CantorSpace = ℕ → Bool`:
- `[CompactSpace CantorSpace]` ✓ (already proved in OQ01.lean)
- `[MetrizableSpace CantorSpace]` ✓ (Pi.metrizable on countable product)
- `[SeparableSpace CantorSpace]` ✓ (compact metrizable ⇒ separable)
- `[BorelSpace CantorSpace]` ✓ (set up automatically with `borelize`)

Construction outline:
```lean
-- Step 1: Use Mathlib instances to get the metric structure
instance : MetrizableSpace (ProbabilityMeasure CantorSpace) := inferInstance  -- from Mathlib

-- Step 2: Prove compactness directly via tightness + completeness
-- Mathlib gives every set tight (of_compactSpace), but does NOT directly give compactness.
-- We need the converse direction of Prokhorov: tight + closed ⇒ compact.

-- Approach 2a: Via Levy-Prokhorov metric completeness
-- The Levy-Prokhorov metric on ProbabilityMeasure(compact metric) is:
--   (a) total (induces the weak topology)
--   (b) complete (Mathlib likely has this; SEARCH MISSING)
--   (c) totally bounded (consequence of tightness; needs proof)
-- (b) + (c) ⇒ compact (standard metric argument).

-- Approach 2b: Via embedding to a compact subset of C(X)*
-- ProbabilityMeasure CantorSpace embeds continuously into the unit ball of C(CantorSpace, ℝ)*.
-- That ball is weak-* compact by Banach-Alaoglu (`WeakDual.isCompact_closedBall`).
-- The image is closed (positive functionals normalized to 1 are weak-* closed).
-- Thus ProbabilityMeasure is the continuous image of a compact set, hence compact.

-- Step 3: Apply FirstCountableTopology.seq_compact_of_compact
example : SeqCompactSpace (ProbabilityMeasure CantorSpace) := inferInstance
-- Then `seqCompact_probabilityMeasure_cantor` follows from `SeqCompactSpace.tendsto_subseq`.
```

**Recommendation**: Approach 2b (via `WeakDual.isCompact_closedBall`) is more direct because:
- Banach-Alaoglu is fully formalized in Mathlib
- The embedding `μ ↦ (f ↦ ∫f dμ)` is well-studied
- The image of `ProbabilityMeasure` in `C(X, ℝ)*` is the "positive unit ball", a closed subset
  of the unit ball

#### Path B — Direct sequence extraction (NOT RECOMMENDED, ~300+ lines)

Use Riesz representation to convert each `ProbabilityMeasure` to a positive linear functional
on `C(CantorSpace, ℝ)`, apply Banach-Alaoglu directly, extract a weak-* convergent subsequence,
and prove the limit is again a probability measure (uses Riesz+positivity preserved at limit).
This duplicates work since Path A's `instance` derivation gives the same result with less code.

### Concrete Mathlib API for Path A (Approach 2b)

```lean
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani  -- for Riesz embedding

-- The continuous embedding (already implicit in Mathlib's ProbabilityMeasure topology):
-- μ ↦ (f ↦ (∫f dμ).toReal) : ProbabilityMeasure X → WeakDual ℝ C(X, ℝ)

-- Key Mathlib lemmas to chain:
#check @WeakDual.isCompact_closedBall          -- ‖·‖ ≤ R is weak-* compact
#check @MeasureTheory.ProbabilityMeasure.continuous_integral_continuousMap  -- the embedding is continuous
#check @IsCompact.image                         -- continuous image of compact is compact
#check @FirstCountableTopology.seq_compact_of_compact  -- compact + first-countable ⇒ seq compact
```

### Recommended Next Concrete Steps

1. **Search Mathlib for `LevyProkhorov.completeSpace` or similar**: confirm whether the
   Levy-Prokhorov metric on `ProbabilityMeasure(compact)` is recognized as `CompleteSpace`.
   If yes, Path A Approach 2a becomes a 5-line proof: complete + totally bounded ⇒ compact.

2. **Inspect Mathlib `Riesz` / `RieszMarkovKakutani`**: confirm whether the Riesz
   representation theorem (probability measures ↔ positive normalized functionals) is
   formalized, which is needed for Path A Approach 2b.

3. **Single-session attempt**: ~150 lines for Approach 2b, ~50 lines for Approach 2a if (1)
   confirms completeness.

### Unblocking the Density Preservation Step (~30 lines remaining)

Per Session 3 notes, density preservation at the limit is "~30 lines" but unblocked. The key
observation: `B₀ = cylinderZero` is **clopen** (line 96-100 of OQ01.lean confirms via
`cylinder_isClopen`). For a weak-* convergent sequence `μ_k → μ`, we have `μ(C) ≤ liminf μ_k(C)`
for closed C and `μ(O) ≥ limsup μ_k(O)` for open O — and for clopen sets, we get equality:
`μ(B₀) = lim μ_k(B₀)`. Mathlib API to use:

```lean
#check @MeasureTheory.ProbabilityMeasure.le_liminf_measure_closed_of_tendsto
#check @MeasureTheory.ProbabilityMeasure.tendsto_measure_of_tendsto_of_isClopen
-- or: derive from the integral formulation since 1_{B₀} is continuous on a clopen
```

If `tendsto_measure_of_tendsto_of_isClopen` exists, the density preservation is a one-liner.
**TODO**: search Mathlib for this lemma name (or its content).

### Files NOT Modified This Session

Disk pressure (1.4 GiB) prevented compile verification. All contributions are documentation
in `knowledge.md`. The state.md and meta.json remain at Session 3 values.

### Sorry Count: 0; Local Axiom Count: 1 (unchanged)

- `seqCompact_probabilityMeasure_cantor`: now has a concrete 2-path construction plan with
  precise Mathlib API references for each step.

---

## Dead Ends

- Cannot enumerate AP witnesses case-by-case (infinitely many cases)
- Cannot use Poincaré recurrence alone for k ≥ 3 (structural argument needed)
