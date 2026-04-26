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
  Stated as a local axiom (Mathlib v4.26 has ingredients but not assembled).

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
  have eval_sum : (∑ i ∈ s, Measure.dirac (f i)) t = ∑ i ∈ s, Measure.dirac (f i) t := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert ha ih => rw [Finset.sum_insert ha, Measure.add_apply, ih]
  rw [eval_sum]
  -- Each Dirac evaluates as an indicator: dirac a t = if a ∈ t then 1 else 0
  simp_rw [Measure.dirac_apply' _ ht, Set.indicator_apply, Pi.one_apply]
  -- Sum of characteristic function = cardinality of filter
  exact_mod_cast Finset.sum_boole

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
    simp only [cesaroMeasure, Measure.smul_apply]
    rw [finsetDirac_apply _ _ MeasurableSet.univ]
    -- Filter trivializes: every orbit point is in Set.univ
    have : (Finset.range (N + 1)).filter (fun n => shift^[n] x ∈ Set.univ) =
        Finset.range (N + 1) :=
      Finset.filter_true_of_mem (fun _ _ => Set.mem_univ _)
    rw [this, Finset.card_range]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast Nat.succ_ne_zero N) ENNReal.natCast_ne_top

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
    simp only [cesaroMeasure, Measure.smul_apply]
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
              Nat.add_sub_cancel⟩
  rw [← hcard]
  -- ENNReal: δ ≤ |Ico-filter| / N  from  δ * N ≤ |Ico-filter|
  have hN_ne : (↑N : ℝ≥0∞) ≠ 0 := by exact_mod_cast hN_pos.ne'
  -- The inequality: ofReal δ ≤ card / N ↔ ofReal δ * N ≤ card
  rw [ENNReal.le_div_iff_mul_le hN_ne ENNReal.natCast_ne_top]
  -- ofReal δ * N ≤ card in ℝ≥0∞ follows from δ * N ≤ card in ℝ
  calc ENNReal.ofReal δ * ↑N
      = ENNReal.ofReal (δ * ↑N) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hδ.le]
    _ ≤ ENNReal.ofReal ↑((Finset.Ico a (a + N)).filter (· ∈ A)).card := by
          exact ENNReal.ofReal_le_ofReal (by exact_mod_cast hdensity)
    _ = ↑((Finset.Ico a (a + N)).filter (· ∈ A)).card := ENNReal.ofReal_natCast _

end CesaroMeasures

/-! ═══════════════════════════════════════════════════════════════════════════════
PART IX: THE MINIMAL REMAINING AXIOM (PROKHOROV)
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

Mathlib v4.26.0 has the ingredients:
- `IsTightMeasureSet.of_compactSpace` (all measures tight on compact spaces)
- `LevyProkhorov.eq_convergenceInDistribution` (metrizes weak convergence)
- `WeakDual.isSeqCompact_closedBall` (sequential Banach-Alaoglu)

The gap is ~150–200 lines assembling these into sequential compactness for
`ProbabilityMeasure CantorSpace`.
-/

/-- **Local Axiom (Prokhorov)**: Sequential compactness of probability measures
    on Cantor space ℕ → Bool in the weak-* topology.

    Mathematical status: This is a standard consequence of Prokhorov's theorem.
    Cantor space is compact metrizable separable. All sets of probability measures
    on a compact space are tight (Mathlib: `IsTightMeasureSet.of_compactSpace`).
    Prokhorov's theorem (tight + compact metrizable → sequentially compact)
    then applies. Estimated formalization: ~150–200 lines. -/
axiom seqCompact_probabilityMeasure_cantor :
    ∀ (f : ℕ → ProbabilityMeasure CantorSpace),
    ∃ (φ : ℕ → ℕ), StrictMono φ ∧
    ∃ μ : ProbabilityMeasure CantorSpace,
    Filter.Tendsto (fun k => f (φ k)) Filter.atTop (nhds μ)

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
| Prokhorov sequential compactness | ⚠ Local axiom | This session |
| T-invariance of limit measures | ❌ Remaining | ~50 lines |
| Density preservation at limit | ❌ Remaining | ~30 lines |

**Net result**: `furstenberg_correspondence` reduces to `seqCompact_probabilityMeasure_cantor`
plus ~80 lines of analysis (T-invariance estimate + density lower semi-continuity).
-/

/-! ═══════════════════════════════════════════════════════════════════════════════
PART X: T-INVARIANCE OF LIMIT MEASURES
═══════════════════════════════════════════════════════════════════════════════ -/

section TInvariance

/-- The pushforward of the N-step Cesàro measure at x under shift equals
    the N-step Cesàro measure at shift x.

    Proof: T_*(μ_{x,N}) = (1/N) Σ_{n<N} (Measure.dirac (T^{n+1} x))
                        = (1/N) Σ_{n<N} (Measure.dirac (T^n (Tx))) = μ_{Tx,N}. -/
theorem cesaroMeasure_map_shift (x : CantorSpace) (N : ℕ) (hN : 0 < N) :
    (cesaroMeasure x N).map shift = cesaroMeasure (shift x) N := by
  cases N with
  | zero => exact absurd hN (lt_irrefl _)
  | succ N =>
    -- Prove equality by evaluating both sides on arbitrary measurable sets
    apply Measure.ext
    intro s hs
    simp only [cesaroMeasure, Measure.map_apply shift_measurable hs, Measure.smul_apply]
    congr 1
    -- Both sums reduce to |{n < N+1 : shift^[n+1] x ∈ s}| via finsetDirac_apply
    rw [finsetDirac_apply _ (fun n => shift^[n] x) (shift_measurable hs)]
    rw [finsetDirac_apply _ (fun n => shift^[n] (shift x)) hs]
    -- Filter sets are equal: shift^[n] x ∈ shift⁻¹' s ↔ shift^[n] (shift x) ∈ s
    -- (both ↔ shift^[n+1] x ∈ s via iterate_succ_apply and iterate_succ_apply')
    norm_cast
    congr 1
    apply Finset.filter_congr
    intro n _
    -- Goal: shift^[n] x ∈ shift⁻¹' s ↔ shift^[n] (shift x) ∈ s
    -- LHS ↔ shift(shift^[n] x) ∈ s [by mem_preimage] ↔ shift^[n+1] x ∈ s [← iterate_succ_apply']
    -- RHS ↔ shift^[n+1] x ∈ s [← iterate_succ_apply]
    -- Both reduce to shift^[n+1] x ∈ s
    simp only [Set.mem_preimage, ← Function.iterate_succ_apply',
               ← Function.iterate_succ_apply]

/-- **Local Axiom (T-invariance)**: Any weak-* limit of Cesàro measures
    along a sequence N_k → ∞ is shift-invariant.

    Mathematical justification:
    - `cesaroMeasure_map_shift`: T_*(μ_{x_k, N_k}) = μ_{T x_k, N_k}.
    - For any bounded continuous f, the Cesàro telescoping identity gives:
        |∫f dT_*(μ_{x,N}) - ∫f dμ_{x,N}| = (1/N)|f(T^N x) - f(x)| ≤ 2‖f‖_∞/N → 0.
    - Since T is continuous, T_*(μ_k) → T_*(μ). Combined with the vanishing gap,
      T_*(μ) = μ.
    Formalization gap: ~60 lines using `Measure.integral_map`,
    `ContinuousLinearMap.tendsto_of_bounded` and `tendsto_nhds_unique`. -/
axiom shift_invariant_of_limit
    {x_seq : ℕ → CantorSpace} {N_seq : ℕ → ℕ}
    (hN : ∀ k, 0 < N_seq k)
    (hN_infty : Filter.Tendsto N_seq Filter.atTop Filter.atTop)
    {μ : ProbabilityMeasure CantorSpace}
    (htend : Filter.Tendsto
        (fun k => (⟨cesaroMeasure (x_seq k) (N_seq k),
            cesaroMeasure_isProbability (x_seq k) (N_seq k) (hN k)⟩ :
            ProbabilityMeasure CantorSpace))
        Filter.atTop (nhds μ)) :
    MeasurePreserving shift (μ : Measure CantorSpace) (μ : Measure CantorSpace)

end TInvariance

/-! ═══════════════════════════════════════════════════════════════════════════════
PART XI: DENSITY PRESERVATION AT THE LIMIT
═══════════════════════════════════════════════════════════════════════════════ -/

section DensityAtLimit

/-- If μ_k → μ weak-* and each μ_k(B₀) ≥ δ, then μ(B₀) ≥ δ.

    Proof: cylinderZero is closed (clopen in Cantor space).
    Portmanteau theorem for closed sets F: limsup_k μ_k(F) ≤ μ(F).
    Since all μ_k(cylinderZero) ≥ δ, we have limsup ≥ δ, so μ(cylinderZero) ≥ δ.

    Formalization: use `ProbabilityMeasure.limsup_measure_closed_le_of_tendsto` or
    `Filter.Tendsto.limsup_le_of_le` composed with Portmanteau. -/
theorem density_preserved_at_limit
    (μ_seq : ℕ → ProbabilityMeasure CantorSpace)
    {μ : ProbabilityMeasure CantorSpace}
    (htend : Filter.Tendsto μ_seq Filter.atTop (nhds μ))
    {δ : ℝ} (hδ : 0 < δ)
    (hbound : ∀ k, ENNReal.ofReal δ ≤ (μ_seq k : Measure CantorSpace) cylinderZero) :
    ENNReal.ofReal δ ≤ (μ : Measure CantorSpace) cylinderZero := by
  sorry
  -- Portmanteau for closed sets: limsup_k μ_k(cylinderZero) ≤ μ(cylinderZero).
  -- Since μ_k(cylinderZero) ≥ δ, limsup ≥ δ, hence μ(cylinderZero) ≥ δ.

end DensityAtLimit

/-! ═══════════════════════════════════════════════════════════════════════════════
PART XII: FURSTENBERG CORRESPONDENCE ASSEMBLY
═══════════════════════════════════════════════════════════════════════════════ -/

section FurstenbergAssembly

/-- **Furstenberg Correspondence Principle** (assembly).

    Given A ⊆ ℕ with upper Banach density ≥ δ > 0, there exists a
    T-invariant probability measure μ on CantorSpace with μ(B₀) ≥ δ.

    Assembly steps:
    1. For each k, `density_lower_bound A hδ hd (k+1)` gives (aₖ, Nₖ) with
       Nₖ ≥ k+1 and cesaroMeasure(shift^[aₖ] 1_A, Nₖ)(B₀) ≥ δ.
    2. `seqCompact_probabilityMeasure_cantor`: extract subsequence → μ.
    3. `shift_invariant_of_limit`: μ is T-invariant.
    4. `density_preserved_at_limit`: μ(B₀) ≥ δ. -/
theorem furstenberg_correspondence (A : Set ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hd : HasUpperDensityGe A δ) :
    ∃ μ : ProbabilityMeasure CantorSpace,
      ENNReal.ofReal δ ≤ (μ : Measure CantorSpace) cylinderZero ∧
      MeasurePreserving shift (μ : Measure CantorSpace) (μ : Measure CantorSpace) := by
  -- Step 1: Build a sequence of witnesses via density_lower_bound
  -- For each k, obtain (a_k, N_k) with N_k ≥ k+1 and measure bound ≥ δ
  have hwitness : ∀ k : ℕ, ∃ a N : ℕ, N ≥ k + 1 ∧
      ENNReal.ofReal δ ≤
        cesaroMeasure (shift^[a] (setIndicator A)) N cylinderZero :=
    fun k => density_lower_bound A hδ hd (k + 1)
  -- Extract canonical witnesses
  let a_seq : ℕ → ℕ := fun k => (hwitness k).choose
  let N_seq : ℕ → ℕ := fun k => (hwitness k).choose_spec.choose
  have hN_ge : ∀ k, k + 1 ≤ N_seq k :=
    fun k => (hwitness k).choose_spec.choose_spec.1
  have hN_pos : ∀ k, 0 < N_seq k :=
    fun k => Nat.lt_of_lt_of_le Nat.zero_lt_one (hN_ge k)
  have hN_infty : Filter.Tendsto N_seq Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_atTop.mpr fun b =>
      ⟨b, fun k hk => le_trans (by omega) (hN_ge k)⟩
  have hdensity : ∀ k,
      ENNReal.ofReal δ ≤ cesaroMeasure (shift^[a_seq k] (setIndicator A)) (N_seq k) cylinderZero :=
    fun k => (hwitness k).choose_spec.choose_spec.2
  -- Form the Cesàro probability measures
  let μ_seq : ℕ → ProbabilityMeasure CantorSpace := fun k =>
    ⟨cesaroMeasure (shift^[a_seq k] (setIndicator A)) (N_seq k),
     cesaroMeasure_isProbability _ _ (hN_pos k)⟩
  -- Step 2: Prokhorov compactness — extract convergent subsequence
  obtain ⟨φ, hφ_mono, μ, hμ_tend⟩ := seqCompact_probabilityMeasure_cantor μ_seq
  -- Step 3: The limit measure is T-invariant
  have hTinv : MeasurePreserving shift (μ : Measure CantorSpace) (μ : Measure CantorSpace) :=
    shift_invariant_of_limit
      (x_seq := fun k => shift^[a_seq (φ k)] (setIndicator A))
      (N_seq := fun k => N_seq (φ k))
      (fun k => hN_pos (φ k))
      (hN_infty.comp hφ_mono.tendsto_atTop)
      hμ_tend
  -- Step 4: Density preserved along subsequence → limit
  have hdensity_lim : ENNReal.ofReal δ ≤ (μ : Measure CantorSpace) cylinderZero :=
    density_preserved_at_limit
      (μ_seq := fun k => μ_seq (φ k))
      hμ_tend hδ
      (fun k => hdensity (φ k))
  exact ⟨μ, hdensity_lim, hTinv⟩

end FurstenbergAssembly

#check shift_continuous
#check shift_measurable
#check cylinderZero_measurableSet
#check indicator_in_kfold_return
#check orbit_indicator_hits
#check (inferInstance : CompactSpace CantorSpace)
-- Parts V-IX:
#check @finsetDirac_apply
#check @cesaroMeasure
#check @cesaroMeasure_isProbability
#check @mem_cylinderZero_shifted
#check @cesaroMeasure_cylinderZero
#check @density_lower_bound
#check @seqCompact_probabilityMeasure_cantor
-- Parts X-XII:
#check @cesaroMeasure_map_shift
#check @shift_invariant_of_limit
#check @density_preserved_at_limit
#check @furstenberg_correspondence

end FurstenbergOQ01
