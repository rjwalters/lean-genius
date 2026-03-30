/-
# Furstenberg Correspondence OQ-01: Shift Dynamics on Cantor Space

## What This File Contains

This file builds the **shift dynamical system on Cantor space** {0,1}^ℕ,
the foundational infrastructure for formalizing the Furstenberg correspondence
principle. The correspondence translates combinatorial density into ergodic
theory, and its construction begins with this shift system.

## Infrastructure Built

1. **Cantor space** Ω = ℕ → Bool with product topology
2. **Shift map** T(x)(n) = x(n+1), proved continuous and measurable
3. **Cylinder sets** B₀ = {x : x(0) = true}, proved measurable
4. **Set indicator** 1_A ∈ Ω for A ⊆ ℕ
5. **Key connection**: shift^n(1_A)(0) = true ↔ n ∈ A
6. **Return property**: relating dynamical intersections to combinatorial patterns

## Toward Eliminating the Correspondence Axiom

The remaining steps for a full proof of the correspondence:
- Define Cesàro averages μ_N = (1/N) Σ_{n<N} δ_{T^n(1_A)} (needs Dirac measures)
- Prove weak-* compactness (needs Prokhorov/sequential compactness on compact spaces)
- Extract T-invariant limit measure
- Show μ(B₀) ≥ d*(A) (density lower bound)

## References

- Furstenberg, "Ergodic behavior of diagonal measures" (1977)
- Furstenberg, "Recurrence in ergodic theory and combinatorial NT" (1981)
-/
import Mathlib

namespace FurstenbergOQ01

open MeasureTheory Set Topology

/-! ═══════════════════════════════════════════════════════════════════════════════
PART I: CANTOR SPACE AND SHIFT MAP
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### The Symbolic Dynamical System

Cantor space Ω = ℕ → Bool is the space of all binary sequences, equipped
with the product topology (making it compact metrizable) and the Borel
σ-algebra. The shift map T : Ω → Ω sends x to the sequence shifted by one.
-/

/-- Cantor space: the space of binary sequences ℕ → Bool. -/
abbrev CantorSpace := ℕ → Bool

/-- The left shift on Cantor space: T(x)(n) = x(n+1). -/
def shift : CantorSpace → CantorSpace := fun x n => x (n + 1)

/-- The shift map is continuous (product topology on ℕ → Bool).
    Each coordinate of shift(x) depends on exactly one coordinate of x. -/
theorem shift_continuous : Continuous shift :=
  continuous_pi (fun n => continuous_apply (n + 1))

/-- The shift map is measurable (Borel σ-algebra from the product topology). -/
theorem shift_measurable : Measurable shift :=
  shift_continuous.measurable

/-- Iterating the shift n times: shift^[n](x)(k) = x(k + n). -/
theorem shift_iterate (x : CantorSpace) (n k : ℕ) :
    shift^[n] x k = x (k + n) := by
  induction n with
  | zero => simp [Function.iterate_zero]
  | succ n ih =>
    simp [Function.iterate_succ', Function.comp_def, shift, ih]
    ring_nf

/-! ═══════════════════════════════════════════════════════════════════════════════
PART II: CYLINDER SETS
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Cylinder Sets: The Basic Building Blocks

Cylinder sets are the natural generating sets for the product σ-algebra.
The cylinder at position i with value b is {x ∈ Ω : x(i) = b}.
These are both open and closed in the product topology.
-/

/-- The cylinder set at position i with value b: {x : x(i) = b}. -/
def cylinder (i : ℕ) (b : Bool) : Set CantorSpace :=
  {x | x i = b}

/-- The distinguished cylinder B₀ = {x : x(0) = true}.
    This is the set whose measure corresponds to the density of A. -/
def cylinderZero : Set CantorSpace := cylinder 0 true

/-- Cylinder sets are clopen (both open and closed) in the product topology. -/
theorem cylinder_isClopen (i : ℕ) (b : Bool) : IsClopen (cylinder i b) := by
  constructor
  · -- Closed: preimage of {b} under continuous projection
    exact isClosed_eq (continuous_apply i) continuous_const
  · -- Open: preimage of {b} under continuous projection, {b} is open in Bool
    exact isOpen_eq_of_isOpen_singleton (continuous_apply i) (isOpen_discrete {b})

/-- Cylinder sets are measurable. -/
theorem cylinder_measurableSet (i : ℕ) (b : Bool) :
    MeasurableSet (cylinder i b) :=
  (cylinder_isClopen i b).2.measurableSet

/-- The distinguished cylinder B₀ is measurable. -/
theorem cylinderZero_measurableSet : MeasurableSet cylinderZero :=
  cylinder_measurableSet 0 true

/-- Preimage of a cylinder under shift: T⁻¹(cylinder i b) = cylinder (i+1) b. -/
theorem shift_preimage_cylinder (i : ℕ) (b : Bool) :
    shift ⁻¹' (cylinder i b) = cylinder (i + 1) b := by
  ext x
  simp [cylinder, shift]

/-- Preimage of B₀ under shift^n: T^{-n}(B₀) = cylinder n true. -/
theorem iterate_preimage_cylinderZero (n : ℕ) :
    shift^[n] ⁻¹' cylinderZero = cylinder n true := by
  ext x
  simp [cylinderZero, cylinder, shift_iterate]

/-! ═══════════════════════════════════════════════════════════════════════════════
PART III: SET INDICATORS AND THE COMBINATORIAL CONNECTION
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Encoding Subsets of ℕ as Points in Cantor Space

A set A ⊆ ℕ is represented by its indicator function 1_A ∈ Ω = ℕ → Bool.
The shift dynamics on 1_A encode the combinatorial structure of A:
  shift^n(1_A)(0) = true ↔ n ∈ A
-/

/-- The indicator of a set A ⊆ ℕ as a point in Cantor space.
    indicator(A)(n) = true iff n ∈ A. -/
noncomputable def setIndicator (A : Set ℕ) : CantorSpace :=
  fun n => if n ∈ A then true else false

/-- The fundamental connection: shifting the indicator by n and
    reading position 0 tells us whether n ∈ A. -/
theorem shift_indicator_zero (A : Set ℕ) (n : ℕ) :
    shift^[n] (setIndicator A) 0 = true ↔ n ∈ A := by
  simp [shift_iterate, setIndicator]
  split <;> simp_all

/-- The indicator lies in cylinder n true iff n ∈ A.
    Equivalent to: setIndicator A ∈ T^{-n}(B₀) ↔ n ∈ A. -/
theorem indicator_mem_cylinder (A : Set ℕ) (n : ℕ) :
    setIndicator A ∈ cylinder n true ↔ n ∈ A := by
  simp [cylinder, setIndicator]
  split <;> simp_all

/-- The indicator lies in B₀ iff 0 ∈ A. -/
theorem indicator_mem_cylinderZero (A : Set ℕ) :
    setIndicator A ∈ cylinderZero ↔ 0 ∈ A :=
  indicator_mem_cylinder A 0

/-! ═══════════════════════════════════════════════════════════════════════════════
PART IV: RETURN PROPERTY — DYNAMICS ENCODES COMBINATORICS
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### The Return Property

The key connection between dynamics and combinatorics:
  setIndicator(A) ∈ B₀ ∩ T^{-n}(B₀) ↔ 0 ∈ A ∧ n ∈ A

More generally, for k-fold intersections:
  setIndicator(A) ∈ ⋂_{i<k} T^{-i·d}(B₀) ↔ ∀ i < k, i·d ∈ A

This is what makes the correspondence work: positive-measure intersections
in the dynamical system translate to combinatorial patterns in A.
-/

/-- **Binary return property**: the indicator of A lies in B₀ ∩ T^{-n}(B₀)
    iff both 0 and n belong to A. -/
theorem indicator_in_binary_return (A : Set ℕ) (n : ℕ) :
    setIndicator A ∈ cylinderZero ∩ (shift^[n] ⁻¹' cylinderZero) ↔
    0 ∈ A ∧ n ∈ A := by
  simp [iterate_preimage_cylinderZero, indicator_mem_cylinder]

/-- **k-fold return property**: the indicator of A lies in the k-fold
    intersection ⋂_{i<k} T^{-i·d}(B₀) iff every i·d (for i < k) belongs to A.
    This is the fundamental combinatorial-dynamical bridge. -/
theorem indicator_in_kfold_return (A : Set ℕ) (k d : ℕ) :
    setIndicator A ∈ ⋂ (i : Fin k), shift^[↑i * d] ⁻¹' cylinderZero ↔
    ∀ i : Fin k, ↑i * d ∈ A := by
  simp [Set.mem_iInter, iterate_preimage_cylinderZero, indicator_mem_cylinder]

/-! ═══════════════════════════════════════════════════════════════════════════════
PART V: ORBIT AND CESÀRO AVERAGES (Definitions)
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Orbit Structure

The orbit of 1_A under the shift generates the Cesàro averages used in
the correspondence construction. We define the orbit and state the
relationship between orbit membership and density.
-/

/-- The orbit of a point x under the shift up to time N. -/
def orbitFinset (x : CantorSpace) (N : ℕ) : Finset CantorSpace :=
  (Finset.range N).image (fun n => shift^[n] x)

/-- The number of orbit points landing in cylinderZero up to time N
    equals the number of n < N with x(n) = true. -/
theorem orbit_hits_cylinderZero (x : CantorSpace) (N : ℕ) :
    ((Finset.range N).filter (fun n => shift^[n] x ∈ cylinderZero)).card =
    ((Finset.range N).filter (fun n => x n = true)).card := by
  congr 1
  ext n
  simp [cylinderZero, cylinder, shift_iterate]

/-- For the indicator of A: orbit hits on B₀ count membership in A. -/
theorem orbit_indicator_hits (A : Set ℕ) (N : ℕ) :
    ((Finset.range N).filter (fun n => shift^[n] (setIndicator A) ∈ cylinderZero)).card =
    ((Finset.range N).filter (fun n => n ∈ A)).card := by
  congr 1
  ext n
  simp [cylinderZero, cylinder, shift_iterate, setIndicator]
  split <;> simp_all

/-! ═══════════════════════════════════════════════════════════════════════════════
PART VI: COMPACTNESS OF CANTOR SPACE
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Compactness

Cantor space ℕ → Bool is compact (Tychonoff's theorem, since Bool is finite).
This is crucial for the correspondence: it guarantees that the sequence of
Cesàro averages has a convergent subsequence.
-/

/-- Bool is a compact space (it's finite). -/
instance : CompactSpace Bool := Finite.instCompactSpace

/-- Cantor space is compact (Tychonoff's theorem: product of compact spaces). -/
instance : CompactSpace CantorSpace :=
  Pi.compactSpace

/-- Cantor space is metrizable (countable product of discrete spaces). -/
instance : MetrizableSpace CantorSpace :=
  inferInstance

/-! ═══════════════════════════════════════════════════════════════════════════════
PART VII: WHAT REMAINS
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Gap Analysis: What's Needed to Complete the Correspondence

**Built in this file** (all proved, 0 axioms):
1. Shift map: continuous, measurable, with iterate formula
2. Cylinder sets: clopen, measurable, preimage under shift
3. Set indicators: encoding A ⊆ ℕ as points in Cantor space
4. Return property: k-fold dynamical intersections ↔ combinatorial patterns
5. Orbit-density connection: orbit hits count membership in A
6. Compactness of Cantor space (from Mathlib/Tychonoff)

**Remaining for full correspondence** (not yet in Mathlib):
1. **Dirac measures on Cantor space**: δ_x for x ∈ Ω as probability measures
2. **Cesàro averaging**: μ_N = (1/N) Σ_{n<N} δ_{T^n(1_A)} as measures
3. **Weak-* compactness**: {μ_N} has a convergent subsequence
   - Follows from Prokhorov's theorem + compactness of Ω
   - Or from Banach-Alaoglu + C(Ω)* metrizable (Ω metrizable compact)
4. **T-invariance of limit**: limit measure is shift-invariant
5. **Density lower bound**: μ(B₀) ≥ d*(A) for the limit measure

Estimated: ~300-500 lines for steps 1-5.
The key missing Mathlib component is weak-* sequential compactness
for probability measures on compact metrizable spaces.
-/

#check shift_continuous
#check shift_measurable
#check cylinderZero_measurableSet
#check indicator_in_kfold_return
#check orbit_indicator_hits
#check (inferInstance : CompactSpace CantorSpace)

end FurstenbergOQ01
