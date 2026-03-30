/-
# Furstenberg Correspondence OQ-02: Ergodic Decomposition Feasibility

## What This File Contains

A **feasibility survey** of formalizing the ergodic decomposition theorem
using Mathlib's existing infrastructure. We demonstrate the key building
blocks already available and state the decomposition theorem, identifying
the precise gap.

## What is the Ergodic Decomposition Theorem?

Every T-invariant probability measure μ on a standard Borel probability
space can be uniquely written as an integral of ergodic measures:

  μ = ∫ μ_x dμ(x)

where μ_x is ergodic for μ-a.e. x. This is the measure-theoretic
analogue of the spectral decomposition.

## Key Finding: Mathlib Has the Foundations

| Component | Status | Mathlib Module |
|-----------|--------|----------------|
| Ergodic measures | ✅ | Dynamics.Ergodic.Ergodic |
| Ergodic = extreme point of invariant measures | ✅ | Dynamics.Ergodic.Extreme |
| Krein-Milman (extreme points exist) | ✅ | Analysis.Convex.KreinMilman |
| Measure disintegration | ✅ | Probability.Kernel.Disintegration |
| Radon-Nikodym derivatives | ✅ | MeasureTheory.Measure.Decomposition |
| RN derivative is T-invariant | ✅ | Dynamics.Ergodic.RadonNikodym |
| Invariant functions are a.e. constant | ✅ | Dynamics.Ergodic.Function |
| Conditional expectation | ✅ | Probability.ConditionalExpectation |

## What's Missing (The Gap)

1. **Choquet representation**: integral representation of measures via
   extreme points (Choquet's theorem on simplices)
2. **Ergodic σ-algebra**: the σ-algebra of T-invariant sets
3. **Conditional measures w.r.t. ergodic σ-algebra**: the decomposition
   kernel mapping points to ergodic measures
4. **Birkhoff ergodic theorem**: pointwise convergence of Cesàro averages
   (needed for the conditional measure construction)

## Estimated Effort

~2000–2500 lines, distributed as:
- Choquet theory for measure simplices: ~400–600 lines
- Ergodic σ-algebra and conditional measures: ~600–800 lines
- Birkhoff ergodic theorem: ~500–700 lines
- Assembly and uniqueness: ~400–500 lines

## Conclusion

**FEASIBLE**: The decomposition theorem is within reach using existing
Mathlib infrastructure. The characterization of ergodic measures as
extreme points (already in Mathlib) provides the mathematical backbone.
The main technical challenge is the Birkhoff ergodic theorem and
conditional measure construction.

## References

- Einsiedler & Ward, "Ergodic Theory with a View Towards Number Theory" (2011)
- Furstenberg, "Recurrence in Ergodic Theory" (1981)
- Glasner, "Ergodic Theory via Joinings" (2003)
-/
import Mathlib

namespace FurstenbergOQ02

open MeasureTheory Set Topology Filter MeasurableSpace

/-! ═══════════════════════════════════════════════════════════════════════════════
PART I: MATHLIB'S ERGODIC THEORY — WHAT EXISTS
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Building Block 1: Ergodic Measures

Mathlib defines ergodic maps via `Ergodic` and `PreErgodic`:
- `PreErgodic f μ`: every measurable T-invariant set has measure 0 or full
- `Ergodic f μ`: `MeasurePreserving f μ μ ∧ PreErgodic f μ`

Key theorem: `Ergodic.ae_empty_or_univ` — for ergodic systems, every
invariant set is null or co-null.
-/

-- Demonstrate Mathlib's ergodic infrastructure
example {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α}
    (hE : Ergodic T μ) (s : Set α) (hs : MeasurableSet s)
    (hTs : T ⁻¹' s = s) : μ s = 0 ∨ μ sᶜ = 0 :=
  hE.preErgodic.ae_empty_or_univ hs hTs

/-!
### Building Block 2: Ergodic = Extreme Point of Invariant Measures

This is the critical link for the decomposition. Mathlib proves in
`Dynamics.Ergodic.Extreme`:

  μ is ergodic for T ↔ μ is an extreme point of
    {ν : Measure α | MeasurePreserving T ν ν ∧ IsProbabilityMeasure ν}

This means the ergodic decomposition is a decomposition of a convex
set into extreme points — exactly Choquet's theorem!
-/

-- The set of T-invariant probability measures
def invariantProbs {α : Type*} [MeasurableSpace α] (T : α → α) :
    Set (Measure α) :=
  {ν | MeasurePreserving T ν ν ∧ IsProbabilityMeasure ν}

/-!
### Building Block 3: Poincaré Recurrence (Conservative Systems)

Mathlib provides the full Poincaré recurrence theorem via the
`Conservative` typeclass. Every measure-preserving map on a
finite measure space is conservative:

  `MeasurePreserving.conservative : ... → Conservative T μ`
  `Conservative.exists_gt_measure_inter_ne_zero : ...`
-/

-- Demonstrate: finite measure-preserving → conservative → recurrence
example {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α}
    [IsFiniteMeasure μ] (hMP : MeasurePreserving T μ μ)
    {s : Set α} (hs : NullMeasurableSet s μ) (hpos : μ s ≠ 0) :
    ∃ n : ℕ, n > 0 ∧ μ (s ∩ T^[n] ⁻¹' s) ≠ 0 :=
  hMP.conservative.exists_gt_measure_inter_ne_zero hs hpos 0

/-!
### Building Block 4: Radon-Nikodym Derivative is T-invariant

Mathlib proves that the Radon-Nikodym derivative of T-invariant measures
is itself T-invariant a.e. This is needed for the decomposition
construction. From `Dynamics.Ergodic.RadonNikodym`:

  `MeasurePreserving.rnDeriv_comp_eq` :
    If T preserves both μ and ν, then `rnDeriv μ ν ∘ T =ᵐ[ν] rnDeriv μ ν`
-/

-- Demonstrate the T-invariance of RN derivatives
example {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {T : α → α}
    (hμ : MeasurePreserving T μ μ) (hν : MeasurePreserving T ν ν)
    [SigmaFinite μ] [SigmaFinite ν] :
    μ.rnDeriv ν ∘ T =ᵐ[ν] μ.rnDeriv ν :=
  hμ.rnDeriv_comp_eq hν

/-!
### Building Block 5: Invariant Functions Are Constant (for Ergodic Systems)

From `Dynamics.Ergodic.Function`:
  For ergodic T, any measurable T-invariant function is a.e. constant.

This is key because the Birkhoff ergodic theorem produces T-invariant
limit functions, which are then a.e. constant under ergodic measures.
-/

-- Demonstrate: ergodic + invariant function → a.e. constant
example {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α}
    (hE : Ergodic T μ) {g : α → ℝ} (hg : Measurable g)
    (hinv : g ∘ T =ᵐ[μ] g) :
    ∃ c, g =ᵐ[μ] Function.const α c :=
  hE.ae_eq_const hg hinv

/-!
### Building Block 6: Measure Disintegration

Mathlib provides disintegration of measures and kernels in
`Probability.Kernel.Disintegration`:
  - Conditional kernels: `ProbabilityTheory.Kernel.condKernel`
  - Recovery: `ρ.fst ⊗ₘ ρ.condKernel = ρ`

This could potentially be adapted for the ergodic decomposition
by disintegrating along the ergodic σ-algebra.
-/

/-!
### Building Block 7: Krein-Milman Theorem

From `Analysis.Convex.KreinMilman`:
  A compact convex set in a locally convex space is the closed convex
  hull of its extreme points.

Combined with Building Block 2 (ergodic = extreme), this tells us
the invariant probability measures form the closed convex hull of
the ergodic measures. The missing step is the **integral representation**
(Choquet's theorem).
-/

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II: THE GAP — WHAT'S NEEDED
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Gap 1: Ergodic Decomposition Statement

The theorem we want to formalize:

  For a measure-preserving system (α, μ, T) on a standard Borel space,
  there exists a measurable family {μ_x}_{x∈α} of probability measures such that:
  (a) μ_x is ergodic for T, for μ-a.e. x
  (b) μ = ∫ μ_x dμ(x) (integral in the sense of measure-valued integration)
  (c) μ_x-a.e. y, μ_y = μ_x (consistency/uniqueness)

The decomposition is essentially "conditioning on the invariant σ-algebra."
-/

/-- The invariant σ-algebra of a measurable map T.
    This is the σ-algebra of sets satisfying T⁻¹(s) = s.
    **Not yet in Mathlib** — this is the first gap. -/
def invariantSigmaAlgebra {α : Type*} [m : MeasurableSpace α] (T : α → α) :
    MeasurableSpace α where
  MeasurableSet' s := @MeasurableSet α m s ∧ T ⁻¹' s = s
  measurableSet_empty := ⟨MeasurableSet.empty, preimage_empty⟩
  measurableSet_compl s ⟨hs, hTs⟩ := ⟨hs.compl, by rw [preimage_compl, hTs]⟩
  measurableSet_iUnion f hf := by
    refine ⟨MeasurableSet.iUnion (fun i => (hf i).1), ?_⟩
    ext x
    simp only [mem_preimage, mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      rw [← (hf i).2] at hi
      exact ⟨i, hi⟩
    · rintro ⟨i, hi⟩
      rw [← (hf i).2]
      exact ⟨i, mem_preimage.mpr hi⟩

/-- The invariant σ-algebra is a sub-σ-algebra of the ambient one. -/
theorem invariantSigmaAlgebra_le {α : Type*} [m : MeasurableSpace α] (T : α → α) :
    invariantSigmaAlgebra T ≤ m :=
  fun _ hs => hs.1

/-!
### Gap 2: Birkhoff Ergodic Theorem

The pointwise ergodic theorem: for f ∈ L¹(μ) and T measure-preserving,

  (1/n) Σ_{k=0}^{n-1} f(T^k(x)) → E[f | I](x)  μ-a.e.

where I is the invariant σ-algebra.

Mathlib has Birkhoff sums (`BirkhoffSum`) but NOT the convergence theorem.
This is needed because the conditional expectation E[f | I] defines the
decomposition: μ_x = "the ergodic component at x."

**Estimated effort**: ~500–700 lines (L¹ maximal inequality + convergence).
-/

/-!
### Gap 3: Choquet Representation

The Choquet integral representation theorem for simplices:

  Every point in a metrizable simplex K is the barycenter of a unique
  probability measure supported on the extreme points of K.

Applied to K = invariant probability measures (which is a Choquet simplex):
  μ = ∫_{ext(K)} ν dλ(ν)
  where λ is a probability measure on the ergodic measures.

Mathlib has Krein-Milman (extreme points exist in compact convex sets)
but not the full Choquet representation.

**Estimated effort**: ~400–600 lines.
-/

/-! ═══════════════════════════════════════════════════════════════════════════════
PART III: ROADMAP — THE PATH TO ERGODIC DECOMPOSITION
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Approach A: Via Conditional Expectation (Most Natural)

1. Define the invariant σ-algebra I (done above: `invariantSigmaAlgebra`)
2. Prove Birkhoff ergodic theorem (~600 lines)
3. Define conditional measures μ_x = E[· | I](x) (~400 lines)
4. Show μ_x is ergodic for μ-a.e. x (~300 lines)
5. Show μ = ∫ μ_x dμ (~200 lines)
6. Uniqueness (~200 lines)

**Total: ~1700 lines** (optimistic, assuming Mathlib conditional expectation works)

### Approach B: Via Choquet Theory

1. Show invariant probability measures form a metrizable simplex (~400 lines)
2. Formalize Choquet representation theorem (~600 lines)
3. Apply to get decomposition (~300 lines)
4. Identify with conditional measures (~400 lines)

**Total: ~1700 lines** (different bottleneck: Choquet theory is non-trivial)

### Approach C: Via Disintegration (Leveraging Existing Mathlib)

1. Use Mathlib's `condKernel` from Kernel.Disintegration
2. Construct the graph measure (α × MeasureSpace)
3. Disintegrate along the invariant σ-algebra
4. Show fibers are ergodic

**Total: ~1200 lines** (most efficient, leverages most Mathlib infrastructure)

### Recommended: Approach C

Approach C is most feasible because:
- Mathlib already has measure disintegration on standard Borel spaces
- The conditional kernel machinery handles the technical measure theory
- Only need to connect disintegration to invariant σ-algebra and ergodicity
-/

/-! ═══════════════════════════════════════════════════════════════════════════════
PART IV: INFRASTRUCTURE DEMONSTRATION
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Demonstrating the Invariant σ-algebra

We prove basic properties of the invariant σ-algebra to show it's
well-behaved in Lean 4.
-/

/-- The preimage of an invariant set under T is the set itself. -/
theorem invariant_preimage_eq {α : Type*} [MeasurableSpace α] {T : α → α}
    {s : Set α} (hs : @MeasurableSet α (invariantSigmaAlgebra T) s) :
    T ⁻¹' s = s :=
  hs.2

/-- Finite intersections of invariant sets are invariant. -/
theorem invariant_inter {α : Type*} [m : MeasurableSpace α] {T : α → α}
    {s t : Set α}
    (hs : @MeasurableSet α (invariantSigmaAlgebra T) s)
    (ht : @MeasurableSet α (invariantSigmaAlgebra T) t) :
    @MeasurableSet α (invariantSigmaAlgebra T) (s ∩ t) := by
  refine ⟨hs.1.inter ht.1, ?_⟩
  rw [preimage_inter, hs.2, ht.2]

/-- The full space is invariant. -/
theorem invariant_univ {α : Type*} [m : MeasurableSpace α] (T : α → α) :
    @MeasurableSet α (invariantSigmaAlgebra T) Set.univ :=
  ⟨MeasurableSet.univ, preimage_univ⟩

/-!
### Multiple Recurrence: What Ergodic Decomposition Would Give Us

The ergodic decomposition reduces multiple recurrence for general
measure-preserving systems to the ergodic case:

  If μ = ∫ μ_x dμ(x) with μ_x ergodic, then
  μ(B ∩ T⁻ⁿB ∩ ... ∩ T⁻⁽ᵏ⁻¹⁾ⁿB) = ∫ μ_x(B ∩ T⁻ⁿB ∩ ... ∩ T⁻⁽ᵏ⁻¹⁾ⁿB) dμ(x)

  If μ_x(B) > 0 for positive-measure set of x (which holds when μ(B) > 0),
  then multiple recurrence for ergodic measures (a simpler problem)
  gives the result.

This shows why ergodic decomposition is THE key stepping stone.
-/

/-! ═══════════════════════════════════════════════════════════════════════════════
PART V: FEASIBILITY ASSESSMENT
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
## Summary: Feasibility Assessment

### Question
Is it feasible to formalize the ergodic decomposition theorem in Mathlib
as a stepping stone toward proving the multiple recurrence theorem?

### Answer: YES, with caveats

**Strengths of Mathlib's current state:**
1. Ergodic measures are well-defined (`Ergodic` structure)
2. Ergodic = extreme point of invariant measures (key characterization)
3. Krein-Milman theorem available (extreme points exist)
4. Full measure disintegration on standard Borel spaces
5. Radon-Nikodym derivatives of invariant measures are invariant
6. Invariant functions are a.e. constant for ergodic maps
7. Conditional expectation framework exists

**What's missing:**
1. Birkhoff ergodic theorem (convergence of Cesàro averages)
2. Choquet representation for measure simplices
3. Connection between disintegration and invariant σ-algebra

**Estimated effort: 1200–2500 lines** (depending on approach)
- Approach C (via existing disintegration): ~1200 lines
- Approach A (via conditional expectation): ~1700 lines
- Full standalone approach: ~2500 lines

**Risk assessment:**
- LOW risk: The mathematical foundations are solid and well-understood
- MEDIUM risk: Lean 4 / Mathlib API may require adaptation
- The disintegration approach (C) minimizes risk by building on existing code

**Recommendation**: Start with Approach C, building the invariant σ-algebra
(demonstrated above) and connecting Mathlib's disintegration to it.
The Birkhoff ergodic theorem is independently valuable and could be
contributed to Mathlib separately.

### Impact on Furstenberg Program

Completing the ergodic decomposition would:
1. Enable proving the multiple recurrence theorem (eliminating Axiom 2)
2. Reduce Szemerédi's theorem to just the correspondence axiom (~500 lines)
3. Make the full Furstenberg-Szemerédi proof achievable in ~3000 total lines
-/

-- Final summary: what we demonstrated
#check @Ergodic                    -- Ergodic maps (Mathlib)
#check @MeasurePreserving          -- Measure-preserving maps (Mathlib)
#check @Conservative               -- Conservative systems (Mathlib)
#check invariantSigmaAlgebra       -- Invariant σ-algebra (new, this file)
#check invariant_preimage_eq       -- Preimage stability (new, this file)
#check invariant_inter             -- Intersection closure (new, this file)

end FurstenbergOQ02
