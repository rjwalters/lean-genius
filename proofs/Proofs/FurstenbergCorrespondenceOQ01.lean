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

open MeasureTheory Set Topology Classical
open scoped ENNReal NNReal

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
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ', Function.comp_apply, shift, ih]
    congr 1; omega

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
  -- cylinder i b is the preimage of the clopen set {b} under the continuous projection
  have h : cylinder i b = (fun x : CantorSpace => x i) ⁻¹' {b} := rfl
  rw [h]
  exact (isClopen_discrete {b}).preimage (continuous_apply i)

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
  simp only [shift_iterate, setIndicator, zero_add, Set.mem_setOf_eq]
  split_ifs with h <;> simp [h]

/-- The indicator lies in cylinder n true iff n ∈ A.
    Equivalent to: setIndicator A ∈ T^{-n}(B₀) ↔ n ∈ A. -/
theorem indicator_mem_cylinder (A : Set ℕ) (n : ℕ) :
    setIndicator A ∈ cylinder n true ↔ n ∈ A := by
  simp only [cylinder, Set.mem_setOf_eq, setIndicator]
  split_ifs with h <;> simp [h]

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
  simp [iterate_preimage_cylinderZero, indicator_mem_cylinder, indicator_mem_cylinderZero]

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
noncomputable def orbitFinset (x : CantorSpace) (N : ℕ) : Finset CantorSpace :=
  (Finset.range N).image (fun n => shift^[n] x)

/-- The number of orbit points landing in cylinderZero up to time N
    equals the number of n < N with x(n) = true. -/
theorem orbit_hits_cylinderZero (x : CantorSpace) (N : ℕ) :
    ((Finset.range N).filter (fun n => shift^[n] x ∈ cylinderZero)).card =
    ((Finset.range N).filter (fun n => x n = true)).card := by
  have h : (Finset.range N).filter (fun n => shift^[n] x ∈ cylinderZero) =
      (Finset.range N).filter (fun n => x n = true) :=
    Finset.filter_congr fun n _ => by simp [cylinderZero, cylinder, shift_iterate]
  rw [h]

/-- For the indicator of A: orbit hits on B₀ count membership in A. -/
theorem orbit_indicator_hits (A : Set ℕ) (N : ℕ) :
    ((Finset.range N).filter (fun n => shift^[n] (setIndicator A) ∈ cylinderZero)).card =
    ((Finset.range N).filter (fun n => n ∈ A)).card := by
  have h : (Finset.range N).filter (fun n => shift^[n] (setIndicator A) ∈ cylinderZero) =
      (Finset.range N).filter (fun n => n ∈ A) :=
    Finset.filter_congr fun n _ => by
      simpa [cylinderZero, cylinder] using shift_indicator_zero A n
  rw [h]

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
instance : CompactSpace Bool := inferInstance

/-- Cantor space is compact (Tychonoff's theorem: product of compact spaces). -/
instance : CompactSpace CantorSpace :=
  Pi.compactSpace

/-- Cantor space is metrizable (countable product of discrete spaces). -/
instance : TopologicalSpace.MetrizableSpace CantorSpace :=
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

/-! ═══════════════════════════════════════════════════════════════════════════════
PART VIII: CESÀRO PROBABILITY MEASURES — THE FURSTENBERG CONSTRUCTION
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Cesàro Averages: The Bridge from Density to Dynamics

The Furstenberg correspondence constructs a T-invariant probability measure
from a set A with positive upper Banach density. The construction:

**Step 1 (this section)**: For any window [a, a+N) with |A ∩ [a,a+N)| ≥ δN,
form the Cesàro probability measure:
  μ_{a,N} = (1/N) Σ_{n=0}^{N-1} δ_{shift^[n](shift^[a](1_A))}

This satisfies μ_{a,N}(B₀) = |A ∩ [a,a+N)| / N ≥ δ. **Proved below.**

**Step 2**: Extract a convergent subsequence from these measures
  (Prokhorov's theorem: compact space → tight → convergent subsequence).
  Proved (S14) via Mathlib v4.31's `Mathlib.MeasureTheory.Measure.Prokhorov`.

**Step 3**: Any limit point is T-invariant with μ(B₀) ≥ δ.
  T-invariance: |∫f d(T_*(μ_{a,N})) - ∫f dμ_{a,N}| ≤ 2‖f‖/N → 0.
-/

section CesaroMeasures

open MeasureTheory Classical

/-- Upper Banach density: A has density ≥ δ if arbitrarily long intervals
    contain ≥ δ-fraction of A. (Matches definition in FurstenbergCorrespondence.) -/
def HasUpperDensityGe (A : Set ℕ) (δ : ℝ) : Prop :=
  ∀ N₀ : ℕ, ∃ a N : ℕ, N ≥ N₀ ∧
    δ * ↑N ≤ ↑((Finset.Ico a (a + N)).filter (· ∈ A)).card

/-- **Key helper**: Evaluating a Finset sum of Dirac measures on a measurable set
    equals the cardinality of the fiber landing in that set.

    Proof: distribute evaluation over sum, apply Dirac formula, use Finset.sum_boole. -/
theorem finsetDirac_apply {ι : Type*} (s : Finset ι) (f : ι → CantorSpace)
    {t : Set CantorSpace} (ht : MeasurableSet t) :
    (∑ i ∈ s, Measure.dirac (f i)) t =
    ↑(s.filter (fun i => f i ∈ t)).card := by
  -- Distribute measure application over the Finset sum
  rw [Measure.finsetSum_apply]
  -- Each Dirac evaluates as an indicator: dirac a t = if a ∈ t then 1 else 0
  simp_rw [Measure.dirac_apply' _ ht, Set.indicator_apply, Pi.one_apply]
  -- Sum of characteristic function = cardinality of filter
  exact Finset.sum_boole _ _

/-- The N-step Cesàro probability measure at orbit point x:
    μ_N(x) = (1/N) Σ_{n=0}^{N-1} δ_{shift^[n](x)}.
    (Convention: μ_0(x) = δ_x.) -/
noncomputable def cesaroMeasure (x : CantorSpace) : ℕ → Measure CantorSpace
  | 0     => Measure.dirac x
  | N + 1 => (↑(N + 1 : ℕ) : ℝ≥0∞)⁻¹ •
              ∑ n ∈ Finset.range (N + 1), Measure.dirac (shift^[n] x)

/-- The Cesàro measure is a probability measure for N ≥ 1. -/
theorem cesaroMeasure_isProbability (x : CantorSpace) :
    ∀ N : ℕ, 0 < N → IsProbabilityMeasure (cesaroMeasure x N) := by
  intro N hN
  cases N with
  | zero => exact absurd hN (lt_irrefl _)
  | succ N =>
    refine ⟨?_⟩
    -- The sum of N+1 Dirac measures has total mass N+1
    have hsum : (∑ n ∈ Finset.range (N + 1), Measure.dirac (shift^[n] x)) Set.univ =
        ((N + 1 : ℕ) : ℝ≥0∞) := by
      rw [Measure.finsetSum_apply]
      simp
    simp only [cesaroMeasure, Measure.smul_apply, smul_eq_mul]
    rw [hsum]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast Nat.succ_ne_zero N)
      (ENNReal.natCast_ne_top _)

/-!
### The Orbit-Density Connection

The Cesàro measure of B₀ exactly counts what fraction of the orbit lies in B₀,
which equals the density of A in the corresponding window.
-/

/-- Membership criterion: the a-shifted orbit at time n lands in B₀ iff n+a ∈ A. -/
theorem mem_cylinderZero_shifted (A : Set ℕ) (a n : ℕ) :
    shift^[n] (shift^[a] (setIndicator A)) ∈ cylinderZero ↔ n + a ∈ A := by
  rw [← Function.iterate_add_apply]
  simp only [cylinderZero, cylinder, Set.mem_setOf_eq]
  exact shift_indicator_zero A (n + a)

/-- **Orbit-Density Formula**: The Cesàro measure of B₀ at shift^a(1_A) over N steps
    equals the density of A in the window [a, a+N). -/
theorem cesaroMeasure_cylinderZero (A : Set ℕ) (a : ℕ) {N : ℕ} (hN : 0 < N) :
    cesaroMeasure (shift^[a] (setIndicator A)) N cylinderZero =
    ↑((Finset.range N).filter (fun n => n + a ∈ A)).card / ↑N := by
  cases N with
  | zero => exact absurd hN (lt_irrefl _)
  | succ N =>
    simp only [cesaroMeasure, Measure.smul_apply, smul_eq_mul]
    rw [finsetDirac_apply _ _ cylinderZero_measurableSet]
    -- Connect filter to A-membership
    have hfilter : (Finset.range (N + 1)).filter
          (fun n => shift^[n] (shift^[a] (setIndicator A)) ∈ cylinderZero) =
        (Finset.range (N + 1)).filter (fun n => n + a ∈ A) :=
      Finset.filter_congr (fun n _ => mem_cylinderZero_shifted A a n)
    rw [hfilter]
    -- Goal: (↑(N+1))⁻¹ * ↑card = ↑card / ↑(N+1)
    -- i.e., a⁻¹ * b = b * a⁻¹ = b / a  (mul_comm + div_eq_mul_inv)
    rw [div_eq_mul_inv, mul_comm]

/-!
### Density Lower Bound — The Elementary Half of the Correspondence

Given A with upper Banach density ≥ δ, for any N₀ there exist a and N ≥ N₀
such that the Cesàro measure of B₀ is ≥ δ. No compactness needed here.
-/

/-- **Density Lower Bound** (proved, no sequential compactness needed):
    If A has upper Banach density ≥ δ > 0, then for any threshold N₀,
    there exist a and N ≥ N₀ such that the Cesàro probability measure
    at shift^a(1_A) has μ(B₀) ≥ δ.

    This is the fully proved half of the Furstenberg correspondence.
    The remaining step (extracting a T-invariant limit) requires Prokhorov. -/
theorem density_lower_bound (A : Set ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hd : HasUpperDensityGe A δ) (N₀ : ℕ) :
    ∃ a N : ℕ, N ≥ N₀ ∧
    ENNReal.ofReal δ ≤ cesaroMeasure (shift^[a] (setIndicator A)) N cylinderZero := by
  obtain ⟨a, N, hN_ge, hdensity⟩ := hd (max N₀ 1)
  have hN1 : 1 ≤ N := le_trans (Nat.le_max_right N₀ 1) hN_ge
  have hN_pos : 0 < N := Nat.lt_of_lt_of_le (by norm_num) hN1
  have hN₀_le : N₀ ≤ N := le_trans (Nat.le_max_left N₀ 1) hN_ge
  refine ⟨a, N, hN₀_le, ?_⟩
  rw [cesaroMeasure_cylinderZero A a hN_pos]
  -- Card equality: Ico-filter ↔ range-filter via bijection n ↦ n - a
  have hcard : ((Finset.Ico a (a + N)).filter (· ∈ A)).card =
      ((Finset.range N).filter (fun n => n + a ∈ A)).card := by
    apply Finset.card_bij (fun n _ => n - a)
    · -- n ∈ [a, a+N) ∩ A  →  n-a ∈ [0,N) with (n-a)+a ∈ A
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at *
      obtain ⟨⟨hna, hnaN⟩, hnA⟩ := hn
      exact ⟨by omega, by rwa [Nat.sub_add_cancel hna]⟩
    · -- n-a is injective on [a, a+N)
      intro n₁ hn₁ n₂ hn₂ h
      simp only [Finset.mem_filter, Finset.mem_Ico] at hn₁ hn₂
      omega
    · -- Surjectivity: for m ∈ range-filter, take n = m+a
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_range] at hm
      refine ⟨m + a, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨Nat.le_add_left a m, by omega⟩, hm.2⟩,
              by omega⟩
  rw [← hcard]
  -- ENNReal: δ ≤ |Ico-filter| / N  from  δ * N ≤ |Ico-filter|
  have hN_ne : (↑N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN_pos.ne'
  -- The inequality: ofReal δ ≤ card / N ↔ ofReal δ * N ≤ card
  rw [ENNReal.le_div_iff_mul_le (Or.inl hN_ne) (Or.inl (ENNReal.natCast_ne_top N))]
  -- ofReal δ * N ≤ card in ℝ≥0∞ follows from δ * N ≤ card in ℝ
  calc ENNReal.ofReal δ * ↑N
      = ENNReal.ofReal (δ * ↑N) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hδ.le]
    _ ≤ ENNReal.ofReal ↑((Finset.Ico a (a + N)).filter (· ∈ A)).card := by
          exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hdensity)
    _ = ↑((Finset.Ico a (a + N)).filter (· ∈ A)).card := ENNReal.ofReal_natCast _

end CesaroMeasures

/-! ═══════════════════════════════════════════════════════════════════════════════
PART VIII-b: APPROXIMATE T-INVARIANCE OF CESÀRO MEASURES
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### T-Invariance Telescoping Bound

The Cesàro measure μ_{N+1}(x) is approximately T-invariant: for any
measurable set S,
  μ_{N+1}(T⁻¹S) ≤ μ_{N+1}(S) + 1/(N+1)  and vice versa.

This follows from a telescoping argument: the orbit sums
Σ_{n<N+1} 1_S(T^{n+1}(x)) and Σ_{n<N+1} 1_S(T^n(x))
differ by at most 1 (gained the (N+1)-th term, lost the 0-th term).

Consequence: any weak-* limit of Cesàro measures (with N_k → ∞) is T-invariant.
-/

section TInvariance

open MeasureTheory Classical

/-- The shifted orbit filter {n < N+1 : T^{n+1}(x) ∈ S} has cardinality
    at most 1 more than the original {n < N+1 : T^n(x) ∈ S}.

    Proof: inject the shifted filter into range(N+2) via n ↦ n+1, then
    note range(N+2) = range(N+1) ∪ {N+1}, adding at most 1 to the count. -/
private theorem filter_shift_card_le (x : CantorSpace) (N : ℕ) (S : Set CantorSpace) :
    ((Finset.range (N + 1)).filter (fun n => shift^[n + 1] x ∈ S)).card ≤
    ((Finset.range (N + 1)).filter (fun n => shift^[n] x ∈ S)).card + 1 := by
  -- Step 1: inject shifted filter into range(N+2) filter via n ↦ n+1
  have h_inj :
      ((Finset.range (N + 1)).filter (fun n => shift^[n + 1] x ∈ S)).card ≤
      ((Finset.range (N + 2)).filter (fun m => shift^[m] x ∈ S)).card := by
    apply Finset.card_le_card_of_injOn (· + 1)
    · intro n hn
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn ⊢
      exact ⟨by omega, hn.2⟩
    · intro a _ b _ hab
      have hab' : a + 1 = b + 1 := hab
      omega
  -- Step 2: range(N+2) = insert (N+1) (range(N+1)), so filter grows by ≤ 1
  have h_split :
      ((Finset.range (N + 2)).filter (fun m => shift^[m] x ∈ S)).card ≤
      ((Finset.range (N + 1)).filter (fun m => shift^[m] x ∈ S)).card + 1 := by
    rw [Finset.range_add_one, Finset.filter_insert]
    split_ifs
    · exact le_of_le_of_eq (Finset.card_insert_le _ _) rfl
    · exact Nat.le_add_right _ _
  linarith

/-- Symmetric bound: the original filter has cardinality at most 1 more
    than the shifted filter. -/
private theorem filter_orig_card_le (x : CantorSpace) (N : ℕ) (S : Set CantorSpace) :
    ((Finset.range (N + 1)).filter (fun n => shift^[n] x ∈ S)).card ≤
    ((Finset.range (N + 1)).filter (fun n => shift^[n + 1] x ∈ S)).card + 1 := by
  -- Inject original filter into range(N+1) filter of shifted+1 via n ↦ n (when n ≥ 1)
  -- But element 0 may not be in shifted range. Split: {0} ∪ Ico 1 (N+1)
  have h_split : Finset.range (N + 1) = {0} ∪ Finset.Ico 1 (N + 1) := by
    ext m
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico, Finset.mem_singleton]
    omega
  have h0 : (({0} : Finset ℕ).filter (fun n => shift^[n] x ∈ S)).card ≤ 1 :=
    le_trans (Finset.card_filter_le _ _) (by simp)
  have hIco : ((Finset.Ico 1 (N + 1)).filter (fun n => shift^[n] x ∈ S)).card ≤
      ((Finset.range (N + 1)).filter (fun n => shift^[n + 1] x ∈ S)).card := by
    apply Finset.card_le_card_of_injOn (· - 1)
    · intro n hn
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico, Finset.mem_range] at hn ⊢
      refine ⟨by omega, ?_⟩
      have hn1 : n - 1 + 1 = n := by omega
      rw [hn1]
      exact hn.2
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ico] at ha hb
      have hab' : a - 1 = b - 1 := hab
      omega
  calc ((Finset.range (N + 1)).filter (fun n => shift^[n] x ∈ S)).card
      = ((({0} : Finset ℕ) ∪ Finset.Ico 1 (N + 1)).filter (fun n => shift^[n] x ∈ S)).card := by
        rw [← h_split]
    _ = ((({0} : Finset ℕ).filter (fun n => shift^[n] x ∈ S)) ∪
         ((Finset.Ico 1 (N + 1)).filter (fun n => shift^[n] x ∈ S))).card := by
        rw [Finset.filter_union]
    _ ≤ (({0} : Finset ℕ).filter (fun n => shift^[n] x ∈ S)).card +
        ((Finset.Ico 1 (N + 1)).filter (fun n => shift^[n] x ∈ S)).card :=
        Finset.card_union_le _ _
    _ ≤ 1 + ((Finset.range (N + 1)).filter (fun n => shift^[n + 1] x ∈ S)).card :=
        Nat.add_le_add h0 hIco
    _ = ((Finset.range (N + 1)).filter (fun n => shift^[n + 1] x ∈ S)).card + 1 :=
        Nat.add_comm _ _

/-- **Approximate T-invariance (upper bound)**: The Cesàro measure of T⁻¹(S) exceeds
    that of S by at most 1/(N+1). -/
theorem cesaroMeasure_preimage_le (x : CantorSpace) (N : ℕ)
    (S : Set CantorSpace) (hS : MeasurableSet S) :
    cesaroMeasure x (N + 1) (shift ⁻¹' S) ≤
    cesaroMeasure x (N + 1) S + (↑(N + 1) : ℝ≥0∞)⁻¹ := by
  simp only [cesaroMeasure, Measure.smul_apply, smul_eq_mul]
  rw [finsetDirac_apply _ _ (hS.preimage shift_measurable),
      finsetDirac_apply _ _ hS]
  -- Convert the preimage filter to match the shifted form
  have hfilt_eq : (Finset.range (N + 1)).filter (fun n => shift^[n] x ∈ shift ⁻¹' S) =
      (Finset.range (N + 1)).filter (fun n => shift^[n + 1] x ∈ S) :=
    Finset.filter_congr fun n _ => by
      simp only [Set.mem_preimage, Function.iterate_succ', Function.comp_def]
  rw [hfilt_eq]
  have hcast : (↑((Finset.range (N + 1)).filter (fun n => shift^[n + 1] x ∈ S)).card : ℝ≥0∞) ≤
      ↑((Finset.range (N + 1)).filter (fun n => shift^[n] x ∈ S)).card + 1 := by
    exact_mod_cast filter_shift_card_le x N S
  refine le_trans (mul_le_mul_left' hcast _) ?_
  rw [mul_add, mul_one]

/-- **Approximate T-invariance (lower bound)**: The Cesàro measure of S exceeds
    that of T⁻¹(S) by at most 1/(N+1). -/
theorem cesaroMeasure_preimage_ge (x : CantorSpace) (N : ℕ)
    (S : Set CantorSpace) (hS : MeasurableSet S) :
    cesaroMeasure x (N + 1) S ≤
    cesaroMeasure x (N + 1) (shift ⁻¹' S) + (↑(N + 1) : ℝ≥0∞)⁻¹ := by
  simp only [cesaroMeasure, Measure.smul_apply, smul_eq_mul]
  rw [finsetDirac_apply _ _ hS,
      finsetDirac_apply _ _ (hS.preimage shift_measurable)]
  have hfilt_eq : (Finset.range (N + 1)).filter (fun n => shift^[n] x ∈ shift ⁻¹' S) =
      (Finset.range (N + 1)).filter (fun n => shift^[n + 1] x ∈ S) :=
    Finset.filter_congr fun n _ => by
      simp only [Set.mem_preimage, Function.iterate_succ', Function.comp_def]
  rw [hfilt_eq]
  have hcast : (↑((Finset.range (N + 1)).filter (fun n => shift^[n] x ∈ S)).card : ℝ≥0∞) ≤
      ↑((Finset.range (N + 1)).filter (fun n => shift^[n + 1] x ∈ S)).card + 1 := by
    exact_mod_cast filter_orig_card_le x N S
  refine le_trans (mul_le_mul_left' hcast _) ?_
  rw [mul_add, mul_one]

end TInvariance

/-! ═══════════════════════════════════════════════════════════════════════════════
PART IX: PROKHOROV SEQUENTIAL COMPACTNESS (former axiom, proved in S14)
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### What the Correspondence Reduces To

Parts I–VIII prove everything except one classical analysis fact:
**sequential compactness of probability measures on Cantor space**.

The density lower bound (Part VIII, `density_lower_bound`) is fully proved:
for any A with upper Banach density ≥ δ, arbitrarily large Cesàro averages
have μ_{a,N}(B₀) ≥ δ.

What remains:
1. **Prokhorov step**: extract a weak-* convergent subsequence μ_{a_k, N_k} → μ.
2. **T-invariance**: for continuous f, |∫f d(T_*(μ_{a,N})) - ∫f dμ_{a,N}| ≤ 2‖f‖/N.
   So any limit μ is T-invariant.
3. **Density at limit**: μ(B₀) ≥ δ (by lower semi-continuity + density lower bound).

Mathlib v4.31 closed this gap upstream: `Mathlib.MeasureTheory.Measure.Prokhorov`
(Gouëzel, 2025) provides `CompactSpace (ProbabilityMeasure E)` for any compact
`E`, and `Mathlib.MeasureTheory.Measure.LevyProkhorovMetric` provides
`MetrizableSpace (ProbabilityMeasure X)` for separable pseudo-metrizable Borel
`X` — so sequential compactness follows from general topology
(`CompactSpace.tendsto_subseq`), with no hand-assembly needed.
-/

/-- **Prokhorov (S14: former local axiom, now a theorem)**: Sequential
    compactness of probability measures on Cantor space ℕ → Bool in the
    topology of weak convergence.

    Cantor space is compact, T2, second-countable and Borel, so Mathlib's
    Prokhorov instance (`Mathlib.MeasureTheory.Measure.Prokhorov`, 2025) makes
    `ProbabilityMeasure CantorSpace` a **compact** space; the Lévy–Prokhorov
    metrization makes it **metrizable**, hence first-countable. A sequence in
    a compact first-countable space has a convergent subsequence
    (`CompactSpace.tendsto_subseq`). The 2026-05 estimate of "~150–200 lines
    of assembly" is now three lines of instance plumbing. -/
theorem seqCompact_probabilityMeasure_cantor :
    ∀ (f : ℕ → ProbabilityMeasure CantorSpace),
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
    ∃ μ : ProbabilityMeasure CantorSpace,
    Filter.Tendsto (fun k => f (φ k)) Filter.atTop (nhds μ) := by
  intro f
  obtain ⟨μ, φ, hφ, hconv⟩ := CompactSpace.tendsto_subseq f
  exact ⟨φ, hφ, μ, hconv⟩

/-!
### Progress Summary

| Component | Status | Session |
|-----------|--------|---------|
| Shift map + cylinders | ✅ Proved | Prior |
| Set indicators + return property | ✅ Proved | Prior |
| Orbit-density connection | ✅ Proved | Prior |
| Compactness of Cantor space | ✅ Proved | Prior |
| `finsetDirac_apply` | ✅ Proved | This session |
| `cesaroMeasure` (definition) | ✅ Defined | This session |
| `cesaroMeasure_isProbability` | ✅ Proved | This session |
| `mem_cylinderZero_shifted` | ✅ Proved | This session |
| `cesaroMeasure_cylinderZero` (orbit-density formula) | ✅ Proved | This session |
| `density_lower_bound` (elementary half) | ✅ Proved | This session |
| Prokhorov sequential compactness | ✅ Proved (S14) | Session 2 → S14 |
| T-invariance telescoping bound | ✅ Proved | Session 3 |
| Density preservation at limit | ❌ Remaining | ~30 lines |

**Net result**: `furstenberg_correspondence` reduces to `seqCompact_probabilityMeasure_cantor`
plus ~30 lines of density preservation (clopen B₀ → μ(B₀) continuous under weak-* limits).

**Prokhorov gap analysis** (session 3): Mathlib v4.26 has `MetrizableSpace (ProbabilityMeasure X)`
for metrizable separable X (`instMetrizableSpaceProbabilityMeasure`) and
`UniformSpace.isCompact_iff_isSeqCompact` for first-countable spaces. The missing piece
is `CompactSpace (ProbabilityMeasure CantorSpace)`, which requires assembling Banach-Alaoglu
or Prokhorov from Mathlib ingredients (~150-200 lines).
-/

/-! ═══════════════════════════════════════════════════════════════════════════════
PART X: DENSITY PRESERVATION AT WEAK-* LIMITS
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Portmanteau for Clopen Sets on Cantor Space

Cylinder sets (and their finite intersections) are clopen in the product topology.
By the Portmanteau theorem, weak convergence of probability measures preserves
the measure of clopen sets. Since B₀ is clopen:

  μ_k → μ weakly  ⟹  μ_k(B₀) → μ(B₀)

Combined with the density lower bound `μ_k(B₀) ≥ δ`, this gives `μ(B₀) ≥ δ`
for any weak-* limit of Cesàro measures.
-/

section DensityPreservation

open MeasureTheory ProbabilityMeasure

/-- **Density preservation at limit**: If a sequence of probability measures on
    Cantor space converges weakly and each assigns at least `c` to B₀,
    then the limit also assigns at least `c` to B₀.

    Proof: B₀ = cylinder 0 true is clopen (Part II), so Portmanteau gives
    μ_k(B₀) → μ(B₀). The bound passes to the limit. -/
theorem density_preserved_at_limit
    (μs : ℕ → ProbabilityMeasure CantorSpace)
    (μ : ProbabilityMeasure CantorSpace)
    (hconv : Filter.Tendsto μs Filter.atTop (nhds μ))
    (c : ℝ≥0)
    (hbound : ∀ k, c ≤ μs k cylinderZero) :
    c ≤ μ cylinderZero := by
  have htends := ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hconv
    (cylinder_isClopen 0 true)
  exact ge_of_tendsto htends (Filter.Eventually.of_forall hbound)

/-- Cylinder measure convergence: for any cylinder set, weak convergence
    of probability measures gives pointwise convergence of measures. -/
theorem cylinder_measure_tendsto_of_tendsto
    (μs : ℕ → ProbabilityMeasure CantorSpace)
    (μ : ProbabilityMeasure CantorSpace)
    (hconv : Filter.Tendsto μs Filter.atTop (nhds μ))
    (i : ℕ) (b : Bool) :
    Filter.Tendsto (fun k => μs k (cylinder i b)) Filter.atTop (nhds (μ (cylinder i b))) :=
  ProbabilityMeasure.tendsto_measure_of_isClopen_of_tendsto hconv (cylinder_isClopen i b)

end DensityPreservation

/-! ═══════════════════════════════════════════════════════════════════════════════
PART XI: CESÀRO MEASURES AS PROBABILITY MEASURES
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Wrapping Cesàro Measures

To apply Prokhorov (sequential compactness) and Portmanteau (weak convergence),
we need the Cesàro measures as `ProbabilityMeasure CantorSpace`, not just
`Measure CantorSpace`.
-/

section CesaroProbability

open MeasureTheory Classical

/-- The Cesàro measure at x for N ≥ 1, packaged as a ProbabilityMeasure. -/
noncomputable def cesaroProbabilityMeasure (x : CantorSpace) (N : ℕ) (hN : 0 < N) :
    ProbabilityMeasure CantorSpace :=
  ⟨cesaroMeasure x N, cesaroMeasure_isProbability x N hN⟩

/-- Coercion: the underlying measure of cesaroProbabilityMeasure is cesaroMeasure. -/
theorem cesaroProbabilityMeasure_toMeasure (x : CantorSpace) (N : ℕ) (hN : 0 < N) :
    (cesaroProbabilityMeasure x N hN : Measure CantorSpace) = cesaroMeasure x N := rfl

end CesaroProbability

/-! ═══════════════════════════════════════════════════════════════════════════════
PART XII: SHIFT-INVARIANCE OF LIMIT MEASURES
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### From Approximate to Exact T-Invariance

The telescoping bounds (Part VIII-b) show that Cesàro measures are approximately
T-invariant: `|μ_N(T⁻¹S) - μ_N(S)| ≤ 1/N` for measurable S.

For clopen sets, Portmanteau gives `μ_k(S) → μ(S)` and `μ_k(T⁻¹S) → μ(T⁻¹S)`.
Since the difference goes to 0, we get `μ(T⁻¹S) = μ(S)` for all clopen sets.

Since clopen sets generate the Borel σ-algebra and form a π-system, the
two measures `μ` and `Measure.map shift μ` agree on all measurable sets.
This gives `MeasurePreserving shift μ μ`.
-/

section ShiftInvariance

open MeasureTheory Classical

/-- Preimage of a clopen set under a continuous map is clopen. -/
theorem isClopen_shift_preimage {S : Set CantorSpace} (hS : IsClopen S) :
    IsClopen (shift ⁻¹' S) :=
  ⟨hS.1.preimage shift_continuous, hS.2.preimage shift_continuous⟩

/-- The approximate T-invariance implies exact T-invariance on cylinder sets
    at the limit: if μ_k are Cesàro measures with N_k → ∞ and μ_k → μ,
    then μ(shift⁻¹(cylinder i b)) = μ(cylinder i b).

    Note: shift⁻¹(cylinder i b) = cylinder (i+1) b, so this is really
    relating measures of consecutive cylinders under the shift. -/
theorem limit_invariant_on_cylinder
    (μs : ℕ → ProbabilityMeasure CantorSpace)
    (μ : ProbabilityMeasure CantorSpace)
    (hconv : Filter.Tendsto μs Filter.atTop (nhds μ))
    (x : CantorSpace) (Ns : ℕ → ℕ)
    (hNs : Filter.Tendsto Ns Filter.atTop Filter.atTop)
    (hdef : ∀ k, (μs k : Measure CantorSpace) = cesaroMeasure x (Ns k + 1))
    (S : Set CantorSpace) (hS : MeasurableSet S) (hSclopen : IsClopen S) :
    (μ : Measure CantorSpace) (shift ⁻¹' S) = (μ : Measure CantorSpace) S := by
  -- Step 1 (ENNReal Portmanteau, both directions): clopen sets have empty
  -- frontier, hence null frontier, so weak convergence gives convergence of
  -- measures on S and on shift⁻¹' S.
  have hS_frontier : (μ : Measure CantorSpace) (frontier S) = 0 := by
    simp [hSclopen.frontier_eq]
  have hshiftS_clopen : IsClopen (shift ⁻¹' S) := isClopen_shift_preimage hSclopen
  have hshiftS_frontier : (μ : Measure CantorSpace) (frontier (shift ⁻¹' S)) = 0 := by
    simp [hshiftS_clopen.frontier_eq]
  have htend_S :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hconv hS_frontier
  have htend_shiftS :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hconv hshiftS_frontier
  -- Step 2 (error term → 0): (Ns k + 1 : ℝ≥0∞)⁻¹ → 0 since Ns k + 1 → ∞.
  have hinv_tend : Filter.Tendsto (fun k => (↑(Ns k + 1) : ℝ≥0∞)⁻¹)
      Filter.atTop (nhds 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp ((Filter.tendsto_add_atTop_nat 1).comp hNs)
  -- Step 3 (≤ direction): pass cesaroMeasure_preimage_le to the limit.
  have hle : (μ : Measure CantorSpace) (shift ⁻¹' S) ≤ (μ : Measure CantorSpace) S := by
    have hsum : Filter.Tendsto
        (fun k => (μs k : Measure CantorSpace) S + (↑(Ns k + 1) : ℝ≥0∞)⁻¹)
        Filter.atTop (nhds ((μ : Measure CantorSpace) S + 0)) := htend_S.add hinv_tend
    rw [add_zero] at hsum
    refine le_of_tendsto_of_tendsto' htend_shiftS hsum fun k => ?_
    rw [hdef k]
    exact cesaroMeasure_preimage_le x (Ns k) S hS
  -- Step 3' (≥ direction): symmetric, via cesaroMeasure_preimage_ge.
  have hge : (μ : Measure CantorSpace) S ≤ (μ : Measure CantorSpace) (shift ⁻¹' S) := by
    have hsum : Filter.Tendsto
        (fun k => (μs k : Measure CantorSpace) (shift ⁻¹' S) + (↑(Ns k + 1) : ℝ≥0∞)⁻¹)
        Filter.atTop (nhds ((μ : Measure CantorSpace) (shift ⁻¹' S) + 0)) :=
      htend_shiftS.add hinv_tend
    rw [add_zero] at hsum
    refine le_of_tendsto_of_tendsto' htend_S hsum fun k => ?_
    rw [hdef k]
    exact cesaroMeasure_preimage_ge x (Ns k) S hS
  -- Step 4: antisymmetry.
  exact le_antisymm hle hge

end ShiftInvariance

/-! ═══════════════════════════════════════════════════════════════════════════════
PART XIII: POSITIVE MEASURE IMPLIES ARITHMETIC PROGRESSIONS
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### The Return Property for Limit Measures

If the limit measure μ assigns positive measure to a finite intersection
of shifted cylinders ⋂_i T^{-i·d}(B₀), then for some large enough k,
the Cesàro measure μ_k also assigns positive measure. Since μ_k is an
average of Dirac measures on shifted indicators, at least one orbit point
lands in the intersection, giving an arithmetic progression in A.
-/

section ReturnProperty

open MeasureTheory Classical

/-- The k-fold intersection ⋂_i T^{-i·d}(B₀) is clopen (finite intersection of clopen sets). -/
theorem kfold_intersection_isClopen (k d : ℕ) :
    IsClopen (⋂ (i : Fin k), shift^[↑i * d] ⁻¹' cylinderZero) := by
  apply isClopen_iInter_of_finite
  intro i
  rw [iterate_preimage_cylinderZero]
  exact cylinder_isClopen _ true

/-- **Return property for Cesàro measures**: if a Cesàro measure assigns positive
    measure to a clopen set S, then some orbit point lies in S. -/
theorem cesaro_positive_implies_orbit_member (x : CantorSpace) (N : ℕ) (hN : 0 < N)
    (S : Set CantorSpace) (hS : MeasurableSet S)
    (hpos : cesaroMeasure x N S ≠ 0) :
    ∃ n, n < N ∧ shift^[n] x ∈ S := by
  cases N with
  | zero => exact absurd hN (lt_irrefl _)
  | succ N =>
    simp only [cesaroMeasure, Measure.smul_apply, smul_eq_mul] at hpos
    rw [finsetDirac_apply _ _ hS] at hpos
    -- If the scaled cardinality is nonzero, the cardinality is nonzero
    have hcard_pos : 0 < ((Finset.range (N + 1)).filter (fun n => shift^[n] x ∈ S)).card := by
      by_contra h
      push_neg at h
      have := Nat.eq_zero_of_le_zero h
      simp [this] at hpos
    -- Nonzero cardinality means the filter is nonempty
    obtain ⟨n, hn⟩ := Finset.card_pos.mp hcard_pos
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    exact ⟨n, hn.1, hn.2⟩

/-- **AP extraction from positive-measure k-fold intersection**:
    If some Cesàro measure at shift^a(1_A) assigns positive measure to the
    k-fold intersection, then A contains a k-term AP. -/
theorem positive_measure_gives_ap (A : Set ℕ) (a N : ℕ) (hN : 0 < N)
    (k d : ℕ) (hk : k ≥ 1)
    (hpos : cesaroMeasure (shift^[a] (setIndicator A)) N
      (⋂ (i : Fin k), shift^[↑i * d] ⁻¹' cylinderZero) ≠ 0) :
    ∃ b : ℕ, ∀ j < k, b + j * d ∈ A := by
  have hS_meas : MeasurableSet (⋂ (i : Fin k), shift^[↑i * d] ⁻¹' cylinderZero) :=
    MeasurableSet.iInter (fun i => (cylinder_measurableSet _ true).preimage
      (shift_measurable.iterate _))
  obtain ⟨n, _, hn_mem⟩ := cesaro_positive_implies_orbit_member _ N hN _ hS_meas hpos
  -- hn_mem : shift^[n] (shift^[a] (setIndicator A)) ∈ ⋂ i, shift^[i*d]⁻¹'(B₀)
  rw [Set.mem_iInter] at hn_mem
  refine ⟨n + a, fun j hj => ?_⟩
  -- Need: n + a + j * d ∈ A
  -- hn_mem gives: shift^[n](shift^[a](1_A)) ∈ shift^[j*d]⁻¹'(B₀)
  have hmem := hn_mem ⟨j, hj⟩
  -- Unpack: shift^[j*d](shift^[n](shift^[a](1_A))) ∈ cylinderZero
  rw [Set.mem_preimage] at hmem
  -- Use iterate_add to combine: shift^[j*d + n + a](1_A) ∈ cylinderZero
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply] at hmem
  -- cylinderZero membership for setIndicator: ↔ (j*d + (n + a)) ∈ A
  have key : ↑(⟨j, hj⟩ : Fin k) * d + (n + a) ∈ A := by
    refine (shift_indicator_zero A _).mp ?_
    simp only [cylinderZero, cylinder, Set.mem_setOf_eq, shift_iterate,
                zero_add] at hmem ⊢
    convert hmem using 2
    omega
  rwa [show n + a + j * d = ↑(⟨j, hj⟩ : Fin k) * d + (n + a) from by simp; ring]

end ReturnProperty

/-! ═══════════════════════════════════════════════════════════════════════════════
PART XIV: THE FULL FURSTENBERG CORRESPONDENCE (ASSEMBLY)
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### Assembling the Furstenberg Correspondence Principle

We now have all the components to prove the Furstenberg correspondence principle:

**Components (all proved except Prokhorov)**:
- `density_lower_bound`: Cesàro measures have μ(B₀) ≥ δ (Part VIII)
- `seqCompact_probabilityMeasure_cantor`: Prokhorov compactness (Part IX, proved S14)
- `density_preserved_at_limit`: μ(B₀) ≥ δ at limit (Part X, proved)
- `cesaroMeasure_preimage_le/ge`: approximate T-invariance (Part VIII-b, proved)
- `limit_invariant_on_cylinder`: exact T-invariance at the limit on clopen
  sets (Part XII, proved 2026-07-23 — Portmanteau null-frontier + vanishing
  1/(N+1) error + le_of_tendsto_of_tendsto')
- `positive_measure_gives_ap`: positive measure → AP (Part XIII, proved)

**Remaining sorries**: 0. **Remaining axioms**: 0 — the former Prokhorov
local axiom `seqCompact_probabilityMeasure_cantor` (Part IX) was proved in
S14 from Mathlib v4.31's Prokhorov + Lévy–Prokhorov metrization instances.

**Architecture**: We construct the `Furstenberg.System` directly on Cantor space:
- X = CantorSpace, T = shift, B = cylinderZero
- μ = weak-* limit of Cesàro measures (from Prokhorov)
- T-invariance from Part XII
- μ(B) ≥ δ from Part X
-/

-- The correspondence System is now assembled: Part XV below packages the
-- invariant limit measure as `exists_invariant_measure_correspondence`, and
-- `Proofs/FurstenbergCorrespondence.lean` (which imports this file) uses it
-- to prove the former `furstenberg_correspondence` axiom as a theorem.

/-! ═══════════════════════════════════════════════════════════════════════════════
PART XV: FULL SHIFT-INVARIANCE AND THE INVARIANT LIMIT MEASURE (S15)
═══════════════════════════════════════════════════════════════════════════════ -/

/-!
### From Clopen Invariance to `MeasurePreserving`

Part XII proved `μ(shift⁻¹ S) = μ(S)` for clopen `S` at any weak-* limit of
Cesàro measures. Three upgrades complete the correspondence:

1. **Moving base points**: the upper *Banach* density windows `[aₖ, aₖ+Nₖ)`
   move, so the Cesàro measures in the extraction are taken at *varying*
   orbit points `shift^[aₖ](1_A)`. The telescoping bounds (Part VIII-b) are
   uniform in the base point, so the Part XII argument goes through verbatim.
2. **π-system extension**: Mathlib's `measurableCylinders` form a π-system
   generating the product σ-algebra (`generateFrom_measurableCylinders`), and
   every measurable cylinder over `ℕ → Bool` is clopen (finite-coordinate
   condition into a finite discrete space). `ext_of_generate_finite` then
   upgrades clopen-set invariance to `Measure.map shift μ = μ`, i.e. full
   `MeasurePreserving shift μ μ`.
3. **Return property at the limit**: positive limit measure on the (clopen)
   k-fold intersection forces positive Cesàro measure along the subsequence
   (Portmanteau), which Part XIII converts into a k-AP in `A`.

The final package `exists_invariant_measure_correspondence` is exactly the
content of the Furstenberg correspondence principle on Cantor space.
-/

section FullInvariance

open MeasureTheory Classical

/-- **Moving-base-point T-invariance at the limit** (generalizes Part XII's
    `limit_invariant_on_cylinder` from a fixed base point to a sequence of
    base points, as required by the Banach-density extraction where the
    windows move): if `μₖ = cesaroMeasure (xs k) (Ns k + 1)` with `Ns → ∞`
    and `μₖ → μ` weakly, then `μ(shift⁻¹ S) = μ(S)` for every clopen `S`.

    The proof is verbatim Part XII — the approximate-invariance bounds
    `cesaroMeasure_preimage_le/ge` hold uniformly in the base point. -/
theorem limit_invariant_on_clopen_moving
    (μs : ℕ → ProbabilityMeasure CantorSpace)
    (μ : ProbabilityMeasure CantorSpace)
    (hconv : Filter.Tendsto μs Filter.atTop (nhds μ))
    (xs : ℕ → CantorSpace) (Ns : ℕ → ℕ)
    (hNs : Filter.Tendsto Ns Filter.atTop Filter.atTop)
    (hdef : ∀ k, (μs k : Measure CantorSpace) = cesaroMeasure (xs k) (Ns k + 1))
    (S : Set CantorSpace) (hS : MeasurableSet S) (hSclopen : IsClopen S) :
    (μ : Measure CantorSpace) (shift ⁻¹' S) = (μ : Measure CantorSpace) S := by
  have hS_frontier : (μ : Measure CantorSpace) (frontier S) = 0 := by
    simp [hSclopen.frontier_eq]
  have hshiftS_clopen : IsClopen (shift ⁻¹' S) := isClopen_shift_preimage hSclopen
  have hshiftS_frontier : (μ : Measure CantorSpace) (frontier (shift ⁻¹' S)) = 0 := by
    simp [hshiftS_clopen.frontier_eq]
  have htend_S :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hconv hS_frontier
  have htend_shiftS :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hconv hshiftS_frontier
  have hinv_tend : Filter.Tendsto (fun k => (↑(Ns k + 1) : ℝ≥0∞)⁻¹)
      Filter.atTop (nhds 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp ((Filter.tendsto_add_atTop_nat 1).comp hNs)
  have hle : (μ : Measure CantorSpace) (shift ⁻¹' S) ≤ (μ : Measure CantorSpace) S := by
    have hsum : Filter.Tendsto
        (fun k => (μs k : Measure CantorSpace) S + (↑(Ns k + 1) : ℝ≥0∞)⁻¹)
        Filter.atTop (nhds ((μ : Measure CantorSpace) S + 0)) := htend_S.add hinv_tend
    rw [add_zero] at hsum
    refine le_of_tendsto_of_tendsto' htend_shiftS hsum fun k => ?_
    rw [hdef k]
    exact cesaroMeasure_preimage_le (xs k) (Ns k) S hS
  have hge : (μ : Measure CantorSpace) S ≤ (μ : Measure CantorSpace) (shift ⁻¹' S) := by
    have hsum : Filter.Tendsto
        (fun k => (μs k : Measure CantorSpace) (shift ⁻¹' S) + (↑(Ns k + 1) : ℝ≥0∞)⁻¹)
        Filter.atTop (nhds ((μ : Measure CantorSpace) (shift ⁻¹' S) + 0)) :=
      htend_shiftS.add hinv_tend
    rw [add_zero] at hsum
    refine le_of_tendsto_of_tendsto' htend_S hsum fun k => ?_
    rw [hdef k]
    exact cesaroMeasure_preimage_ge (xs k) (Ns k) S hS
  exact le_antisymm hle hge

/-- Every measurable cylinder over `ℕ → Bool` is clopen: it is the preimage of
    a subset of the *finite discrete* space `(i : I) → Bool` (where every set
    is clopen) under the continuous restriction map. -/
theorem isClopen_of_mem_measurableCylinders {S : Set CantorSpace}
    (hS : S ∈ MeasureTheory.measurableCylinders (fun _ : ℕ => Bool)) :
    IsClopen S := by
  obtain ⟨I, B, _hB, rfl⟩ := (MeasureTheory.mem_measurableCylinders S).mp hS
  have hcont : Continuous (I.restrict : CantorSpace → ((i : I) → Bool)) :=
    continuous_pi fun i => continuous_apply (i : ℕ)
  exact (isClopen_discrete B).preimage hcont

/-- **Full shift-invariance of the limit measure**: any weak-* limit of Cesàro
    measures (with lengths `→ ∞`, arbitrary moving base points) is invariant
    under the shift, as a bona fide `MeasurePreserving`.

    Proof: clopen invariance (`limit_invariant_on_clopen_moving`) covers all
    measurable cylinders, which form a π-system generating the product
    σ-algebra; `ext_of_generate_finite` extends the equality
    `Measure.map shift μ = μ` to all Borel sets. -/
theorem limit_measurePreserving
    (μs : ℕ → ProbabilityMeasure CantorSpace)
    (μ : ProbabilityMeasure CantorSpace)
    (hconv : Filter.Tendsto μs Filter.atTop (nhds μ))
    (xs : ℕ → CantorSpace) (Ns : ℕ → ℕ)
    (hNs : Filter.Tendsto Ns Filter.atTop Filter.atTop)
    (hdef : ∀ k, (μs k : Measure CantorSpace) = cesaroMeasure (xs k) (Ns k + 1)) :
    MeasurePreserving shift (μ : Measure CantorSpace) (μ : Measure CantorSpace) := by
  refine ⟨shift_measurable, ?_⟩
  haveI : IsProbabilityMeasure ((μ : Measure CantorSpace).map shift) :=
    Measure.isProbabilityMeasure_map shift_measurable.aemeasurable
  refine ext_of_generate_finite (MeasureTheory.measurableCylinders (fun _ : ℕ => Bool))
    MeasureTheory.generateFrom_measurableCylinders.symm
    MeasureTheory.isPiSystem_measurableCylinders (fun S hSmem => ?_) ?_
  · have hSmeas : MeasurableSet S := MeasurableSet.of_mem_measurableCylinders hSmem
    rw [Measure.map_apply shift_measurable hSmeas]
    exact limit_invariant_on_clopen_moving μs μ hconv xs Ns hNs hdef S hSmeas
      (isClopen_of_mem_measurableCylinders hSmem)
  · rw [Measure.map_apply shift_measurable MeasurableSet.univ]
    simp

/-- **Return property at the limit**: if the limit measure charges the k-fold
    intersection `⋂ᵢ shift^[i·d]⁻¹(B₀)`, then — because that set is clopen and
    Portmanteau upgrades weak convergence to convergence of measures on it —
    some Cesàro measure along the sequence charges it too, and Part XIII
    extracts a k-term AP in `A`. -/
theorem limit_positive_implies_ap (A : Set ℕ)
    (μs : ℕ → ProbabilityMeasure CantorSpace)
    (μ : ProbabilityMeasure CantorSpace)
    (hconv : Filter.Tendsto μs Filter.atTop (nhds μ))
    (as : ℕ → ℕ) (Ns : ℕ → ℕ)
    (hdef : ∀ k, (μs k : Measure CantorSpace) =
      cesaroMeasure (shift^[as k] (setIndicator A)) (Ns k + 1))
    (k d : ℕ) (hk : 1 ≤ k)
    (hpos : (μ : Measure CantorSpace)
      (⋂ (i : Fin k), shift^[↑i * d] ⁻¹' cylinderZero) ≠ 0) :
    ∃ b : ℕ, ∀ j < k, b + j * d ∈ A := by
  set S := ⋂ (i : Fin k), shift^[↑i * d] ⁻¹' cylinderZero with hS_def
  have hSclopen : IsClopen S := kfold_intersection_isClopen k d
  have hS_frontier : (μ : Measure CantorSpace) (frontier S) = 0 := by
    simp [hSclopen.frontier_eq]
  have htend :=
    ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hconv hS_frontier
  have hev : ∀ᶠ j in Filter.atTop, (μs j : Measure CantorSpace) S ≠ 0 :=
    htend.eventually_ne hpos
  obtain ⟨j, hj⟩ := hev.exists
  rw [hdef j] at hj
  exact positive_measure_gives_ap A (as j) (Ns j + 1) (Nat.succ_pos _) k d hk hj

/-- The `Fin 2` k-fold intersection is the binary return set `B₀ ∩ shift^[n]⁻¹(B₀)`.
    Used to derive the pair-return clause of the correspondence from the k-fold one. -/
theorem kfold_two_eq_pair (n : ℕ) :
    (⋂ (i : Fin 2), shift^[↑i * n] ⁻¹' cylinderZero) =
      cylinderZero ∩ shift^[n] ⁻¹' cylinderZero := by
  ext x
  simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    simp only [Fin.val_zero, Nat.zero_mul, Function.iterate_zero_apply] at h0
    simp only [Fin.val_one, Nat.one_mul] at h1
    exact ⟨h0, h1⟩
  · rintro ⟨h0, h1⟩ i
    fin_cases i
    · simpa using h0
    · simpa using h1

/-- **The Furstenberg correspondence on Cantor space (full package)**:
    for any `A ⊆ ℕ` of upper Banach density `≥ δ > 0` there is a
    shift-invariant probability measure `μ` on `{0,1}^ℕ` with
    `μ(B₀) ≥ δ` such that positive `μ`-measure of any k-fold return set
    produces a k-term arithmetic progression in `A`.

    This is precisely the mathematical content of the
    `furstenberg_correspondence` axiom of `Proofs/FurstenbergCorrespondence.lean`
    (which now derives it from this theorem), assembled from:
    `density_lower_bound` (Part VIII) + `seqCompact_probabilityMeasure_cantor`
    (Part IX, Prokhorov) + Portmanteau density preservation (Part X) +
    `limit_measurePreserving` (Part XV) + `limit_positive_implies_ap`
    (Parts XIII+XV). -/
theorem exists_invariant_measure_correspondence (A : Set ℕ) {δ : ℝ} (hδ : 0 < δ)
    (hd : HasUpperDensityGe A δ) :
    ∃ μ : ProbabilityMeasure CantorSpace,
      MeasurePreserving shift (μ : Measure CantorSpace) (μ : Measure CantorSpace) ∧
      ENNReal.ofReal δ ≤ (μ : Measure CantorSpace) cylinderZero ∧
      ∀ k d : ℕ, 1 ≤ k →
        (μ : Measure CantorSpace)
          (⋂ (i : Fin k), shift^[↑i * d] ⁻¹' cylinderZero) ≠ 0 →
        ∃ b : ℕ, ∀ j < k, b + j * d ∈ A := by
  -- Step 1: density windows of every length, via the Banach density hypothesis.
  have hex : ∀ m : ℕ, ∃ a N : ℕ, N ≥ m + 1 ∧
      ENNReal.ofReal δ ≤ cesaroMeasure (shift^[a] (setIndicator A)) N cylinderZero :=
    fun m => density_lower_bound A hδ hd (m + 1)
  choose a N hN hbound using hex
  have hNpos : ∀ m, 0 < N m := fun m => lt_of_lt_of_le (Nat.succ_pos m) (hN m)
  -- Step 2: package the Cesàro measures (lengths in successor form).
  let xs : ℕ → CantorSpace := fun m => shift^[a m] (setIndicator A)
  let Ns : ℕ → ℕ := fun m => N m - 1
  have hNs_succ : ∀ m, Ns m + 1 = N m := fun m => Nat.succ_pred_eq_of_pos (hNpos m)
  have hNs_ge : ∀ m, m ≤ Ns m := fun m => by
    have h1 := hN m
    show m ≤ N m - 1
    omega
  have hNs_tend : Filter.Tendsto Ns Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono hNs_ge Filter.tendsto_id
  let μs : ℕ → ProbabilityMeasure CantorSpace :=
    fun m => cesaroProbabilityMeasure (xs m) (Ns m + 1) (Nat.succ_pos _)
  have hdef : ∀ m, (μs m : Measure CantorSpace) = cesaroMeasure (xs m) (Ns m + 1) :=
    fun m => rfl
  -- Step 3: Prokhorov extraction (Part IX).
  obtain ⟨φ, hφ, μ, hconv⟩ := seqCompact_probabilityMeasure_cantor μs
  have hNs_tend' : Filter.Tendsto (fun j => Ns (φ j)) Filter.atTop Filter.atTop :=
    hNs_tend.comp hφ.tendsto_atTop
  refine ⟨μ, ?_, ?_, ?_⟩
  -- Step 4: full shift-invariance (Part XV π-system upgrade).
  · exact limit_measurePreserving (fun j => μs (φ j)) μ hconv (fun j => xs (φ j))
      (fun j => Ns (φ j)) hNs_tend' (fun j => hdef (φ j))
  -- Step 5: density preservation at the limit (Portmanteau on the clopen B₀).
  · have hclopen : IsClopen cylinderZero := cylinder_isClopen 0 true
    have hfr : (μ : Measure CantorSpace) (frontier cylinderZero) = 0 := by
      simp [hclopen.frontier_eq]
    have htendB := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
      hconv hfr
    refine ge_of_tendsto htendB (Filter.Eventually.of_forall fun j => ?_)
    have h1 : ((μs (φ j) : ProbabilityMeasure CantorSpace) : Measure CantorSpace) =
        cesaroMeasure (xs (φ j)) (N (φ j)) := by
      rw [hdef (φ j), hNs_succ (φ j)]
    calc ENNReal.ofReal δ
        ≤ cesaroMeasure (xs (φ j)) (N (φ j)) cylinderZero := hbound (φ j)
      _ = (μs (φ j) : Measure CantorSpace) cylinderZero := by rw [h1]
  -- Step 6: k-fold return property at the limit.
  · intro k d hk hpos
    exact limit_positive_implies_ap A (fun j => μs (φ j)) μ hconv
      (fun j => a (φ j)) (fun j => Ns (φ j)) (fun j => hdef (φ j)) k d hk hpos

end FullInvariance

/-!
### Progress Summary (Session 4)

| Component | Status | Session |
|-----------|--------|---------|
| Shift map + cylinders | ✅ Proved | 1 |
| Set indicators + return property | ✅ Proved | 1 |
| Orbit-density connection | ✅ Proved | 1 |
| Compactness of Cantor space | ✅ Proved | 1 |
| `finsetDirac_apply` | ✅ Proved | 2 |
| `cesaroMeasure` + `cesaroMeasure_isProbability` | ✅ Proved | 2 |
| `cesaroMeasure_cylinderZero` (orbit-density formula) | ✅ Proved | 2 |
| `density_lower_bound` (elementary half) | ✅ Proved | 2 |
| Prokhorov sequential compactness | ✅ Proved (S14) | 2 → S14 |
| T-invariance telescoping bounds | ✅ Proved | 3 |
| `density_preserved_at_limit` (Portmanteau) | ✅ Proved | 4 |
| `cylinder_measure_tendsto_of_tendsto` | ✅ Proved | 4 |
| `cesaroProbabilityMeasure` (wrapping) | ✅ Defined | 4 |
| `kfold_intersection_isClopen` | ✅ Proved | 4 |
| `cesaro_positive_implies_orbit_member` | ✅ Proved | 4 |
| `positive_measure_gives_ap` | ✅ Proved | 4 |
| `correspondenceSystem` (System constructor) | ✅ Defined | 4 |
| `limit_invariant_on_cylinder` | ✅ Proved | S13 (2026-07-23) |

**Net result**: The `furstenberg_correspondence` axiom in FurstenbergCorrespondence.lean
reduces to:
  1. `seqCompact_probabilityMeasure_cantor` (Prokhorov axiom, standard analysis)

The T-invariance limit algebra (formerly a sorry) is now proved
(`limit_invariant_on_cylinder`, Part XII). The Prokhorov axiom is a
standard analysis fact, not deep mathematics.
The combinatorial-dynamical bridge (Parts III-V, XIII) is fully proved.
-/

end FurstenbergOQ01
