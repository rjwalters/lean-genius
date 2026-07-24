/-
Furstenberg's Ergodic Approach to Szemerédi's Theorem

Investigates OQ-04: Can Furstenberg's ergodic proof (which gives no
quantitative bounds but proves more general results) be formalized in Lean 4?

**Answer**: Yes. Mathlib already provides the key infrastructure:
  - MeasurePreserving with iteration (Dynamics.Ergodic.MeasurePreserving)
  - Conservative systems (Dynamics.Ergodic.Conservative)
  - Poincaré recurrence: exists_gt_measure_inter_ne_zero
  - IsProbabilityMeasure → IsFiniteMeasure → MeasurePreserving.conservative

This file demonstrates the architecture of the proof:
  - Poincaré recurrence (k=2 multiple recurrence) from Mathlib (**proved**)
  - Furstenberg Correspondence Principle (**proved** 2026-07-24, former Axiom 1,
    via Proofs/FurstenbergCorrespondenceOQ01.lean: Cesàro averages of Dirac
    measures on Cantor-space shift orbits, Prokhorov extraction from Mathlib
    v4.31, π-system upgrade of clopen invariance to MeasurePreserving)
  - Szemerédi k=2 via the ergodic route (**proved**, now axiom-free)
  - Full Szemerédi for all k (**proved** from 1 axiom)

**Axioms** (1):
  1. Multiple Recurrence for k ≥ 3 — needs ergodic decomposition

**What Mathlib is missing** (gap analysis):
  - Ergodic decomposition theorem
  - Multiple recurrence theorem (Furstenberg 1977)

**Estimated effort** to eliminate the remaining axiom:
  - Multiple recurrence: ~2000+ lines (ergodic decomposition + structure theory)

References:
  - Furstenberg, "Ergodic behavior of diagonal measures" (1977)
  - Furstenberg, "Recurrence in ergodic theory and combinatorial NT" (1981)
  - Bergelson, "Ergodic Ramsey theory — an update" (1996)
-/
import Mathlib
import Proofs.FurstenbergCorrespondenceOQ01

open scoped Classical

namespace Furstenberg

open MeasureTheory Set

/-!
## Upper Banach Density

The upper Banach density of A ⊆ ℕ measures the maximum density of A
in the best-case window of any given length:
  d*(A) = lim sup_{N→∞} max_a |A ∩ [a, a+N)| / N
-/

/-- A set A ⊆ ℕ has upper Banach density at least δ: for any length
    threshold, there exists an interval of at least that length containing
    at least δ-fraction of A. -/
def HasUpperDensityGe (A : Set ℕ) (δ : ℝ) : Prop :=
  ∀ N₀ : ℕ, ∃ a N : ℕ, N ≥ N₀ ∧
    δ * ↑N ≤ ↑((Finset.Ico a (a + N)).filter (· ∈ A)).card

/-!
## Dynamical System Structure

A probability measure-preserving dynamical system with a distinguished
measurable set. This bundles all the data needed for Furstenberg's approach.
-/

/-- A probability measure-preserving system with a distinguished set -/
structure System where
  X : Type
  mX : MeasurableSpace X
  μ : @Measure X mX
  T : X → X
  B : Set X
  hProb : @IsProbabilityMeasure X mX μ
  hMP : @MeasurePreserving X X mX mX T μ μ
  hB : @MeasurableSet X mX B

/-!
## Poincaré Recurrence (from Mathlib)

Mathlib's key chain for the k=2 case:
  MeasurePreserving (on finite measure) → Conservative → Poincaré recurrence

The `Conservative` structure in Mathlib captures the essential property:
for any set of positive measure, some point returns. Combined with
`MeasurePreserving.conservative` (which shows every measure-preserving map
on a finite measure space is conservative), this gives Poincaré recurrence
via `Conservative.exists_gt_measure_inter_ne_zero`.
-/

/-- **Poincaré Recurrence** (from Mathlib): For a measure-preserving map T
    on a probability space, any measurable set B with μ(B) > 0 has a return
    time n > 0 with μ(B ∩ T^{-n}B) > 0.

    Proof: MeasurePreserving → Conservative (Mathlib) → recurrence (Mathlib). -/
theorem poincare_return (sys : System) (hpos : sys.μ sys.B ≠ 0) :
    ∃ n : ℕ, n > 0 ∧ sys.μ (sys.B ∩ sys.T^[n] ⁻¹' sys.B) ≠ 0 := by
  letI := sys.mX
  letI := sys.hProb
  obtain ⟨n, hn, hmeas⟩ := sys.hMP.conservative.exists_gt_measure_inter_ne_zero
    sys.hB.nullMeasurableSet hpos 0
  exact ⟨n, hn, hmeas⟩

/-- Infinitely many return times (from Mathlib) -/
theorem poincare_frequently (sys : System) (hpos : sys.μ sys.B ≠ 0) :
    ∃ᶠ n in Filter.atTop, sys.μ (sys.B ∩ sys.T^[n] ⁻¹' sys.B) ≠ 0 := by
  letI := sys.mX
  letI := sys.hProb
  exact sys.hMP.conservative.frequently_measure_inter_ne_zero
    sys.hB.nullMeasurableSet hpos

/-!
## Furstenberg Correspondence Principle (former Axiom 1 — PROVED 2026-07-24)

The correspondence translates combinatorial density into measure theory:

**Construction** (Furstenberg 1977), as formalized in
`Proofs/FurstenbergCorrespondenceOQ01.lean`:
1. Let X = {0,1}^ℕ with product topology and Borel σ-algebra
2. Define shift T : X → X by (Tx)(n) = x(n+1)
3. The indicator 1_A ∈ X represents the set A
4. Form Cesàro averages μ_N = (1/N) Σ_{n<N} δ_{T^n(shift^a(1_A))} over
   density windows [a, a+N)
5. A weak-* subsequential limit μ (Prokhorov, Mathlib v4.31) is T-invariant
   (telescoping bound + π-system extension over measurable cylinders)
6. For B = {x ∈ X : x(0) = 1}: μ(B) ≥ δ (Portmanteau on the clopen B)
7. Positive-measure k-fold intersections lift to k-APs in A (Portmanteau
   back to a Cesàro average + orbit counting)
-/

/-- **Furstenberg Correspondence Principle** (former Axiom 1, now a THEOREM).
    A set with positive upper Banach density corresponds to a measure-preserving
    system where positive-measure intersections give combinatorial patterns.

    Proved (2026-07-24) from the Cantor-space construction in
    `Proofs/FurstenbergCorrespondenceOQ01.lean`: the system is
    `(({0,1}^ℕ, Borel), μ, shift, B₀)` where `μ` is a weak-* subsequential
    limit (Prokhorov, Mathlib v4.31) of the Cesàro averages
    `(1/N) Σ_{n<N} δ_{shift^n(shift^a(1_A))}` along density windows, shift-
    invariance comes from the telescoping bound + a π-system extension over
    the measurable cylinders, and positive limit measure on (clopen) return
    sets passes back to some Cesàro average by Portmanteau, where it exhibits
    an AP in `A`. -/
theorem furstenberg_correspondence (A : Set ℕ) (δ : ℝ) (hδ : δ > 0)
    (hd : HasUpperDensityGe A δ) :
    ∃ (sys : System),
      sys.μ sys.B ≥ ENNReal.ofReal δ ∧
      -- Pair return: positive measure binary intersection gives 2-AP
      (∀ n : ℕ, n > 0 → sys.μ (sys.B ∩ sys.T^[n] ⁻¹' sys.B) ≠ 0 →
        ∃ a : ℕ, a ∈ A ∧ a + n ∈ A) ∧
      -- General return: positive measure k-fold intersection gives k-AP
      (∀ k n : ℕ, k ≥ 1 → n > 0 →
        sys.μ (⋂ (i : Fin k), sys.T^[↑i * n] ⁻¹' sys.B) ≠ 0 →
          ∃ a : ℕ, ∀ j < k, a + j * n ∈ A) := by
  obtain ⟨μ, hMP, hδμ, hret⟩ :=
    FurstenbergOQ01.exists_invariant_measure_correspondence A hδ hd
  refine ⟨⟨FurstenbergOQ01.CantorSpace, inferInstance,
    (μ : MeasureTheory.Measure FurstenbergOQ01.CantorSpace),
    FurstenbergOQ01.shift, FurstenbergOQ01.cylinderZero, μ.2, hMP,
    FurstenbergOQ01.cylinderZero_measurableSet⟩, hδμ, ?_, ?_⟩
  · -- Pair return: specialize the k-fold clause to k = 2.
    intro n hn hpos
    have hpos' : (μ : MeasureTheory.Measure FurstenbergOQ01.CantorSpace)
        (FurstenbergOQ01.cylinderZero ∩
          FurstenbergOQ01.shift^[n] ⁻¹' FurstenbergOQ01.cylinderZero) ≠ 0 := hpos
    rw [← FurstenbergOQ01.kfold_two_eq_pair n] at hpos'
    obtain ⟨b, hb⟩ := hret 2 n (by norm_num) hpos'
    refine ⟨b, ?_, ?_⟩
    · simpa using hb 0 (by norm_num)
    · simpa using hb 1 (by norm_num)
  · -- k-fold return, verbatim from the package.
    intro k n hk _hn hpos
    exact hret k n hk hpos

/-!
## Szemerédi k=2 via the Ergodic Route (PROVED)

The key result combining Mathlib's Poincaré recurrence with the
Furstenberg correspondence:

**Proof structure**:
1. Correspondence → system (X, μ, T, B) with μ(B) ≥ δ > 0
2. MeasurePreserving.conservative (Mathlib) → T is conservative
3. Conservative.exists_gt_measure_inter_ne_zero (Mathlib) → ∃ n > 0, μ(B ∩ T^{-n}B) ≠ 0
4. Correspondence return property → ∃ a, {a, a+n} ⊆ A
-/

/-- **Szemerédi k=2 via Furstenberg**: Sets with positive upper Banach density
    contain 2-term arithmetic progressions.
    Uses: Furstenberg correspondence (proved, Part above) + Poincaré recurrence
    (Mathlib). Fully verified: no custom axioms. -/
theorem szemeredi_k2_ergodic (A : Set ℕ) (δ : ℝ) (hδ : δ > 0)
    (hd : HasUpperDensityGe A δ) :
    ∃ a n : ℕ, n > 0 ∧ a ∈ A ∧ a + n ∈ A := by
  -- Step 1: Furstenberg correspondence gives us the system
  obtain ⟨sys, hμB, hreturn2, _⟩ := furstenberg_correspondence A δ hδ hd
  -- Step 2: B has positive measure (from μ(B) ≥ ofReal δ > 0)
  have hB_pos := (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hδ) hμB).ne'
  -- Step 3: Poincaré recurrence (from Mathlib!) gives a return time
  obtain ⟨n, hn_pos, hn_meas⟩ := poincare_return sys hB_pos
  -- Step 4: Correspondence return property gives the 2-AP
  obtain ⟨a, ha, han⟩ := hreturn2 n hn_pos hn_meas
  exact ⟨a, n, hn_pos, ha, han⟩

/-!
## Multiple Recurrence for k ≥ 3 (the sole remaining Axiom)

The Multiple Recurrence Theorem (Furstenberg 1977): For (X, μ, T)
measure-preserving on a probability space, and B with μ(B) > 0:

  ∀ k ≥ 1, ∃ n > 0, μ(B ∩ T^{-n}B ∩ T^{-2n}B ∩ ... ∩ T^{-(k-1)n}B) > 0

Case analysis:
- k=1: Trivial (B itself has positive measure)
- k=2: Poincaré recurrence (Section 2, **proved** from Mathlib)
- k≥3: Requires deep ergodic theory (**axiomatized**)

The proof for k ≥ 3 requires (none in Mathlib):
  1. Ergodic decomposition: reduce to ergodic measures
  2. Compact extension / weak mixing dichotomy
  3. Van der Waerden's theorem as base case
  4. Induction on k using characteristic factors
-/

/-- **Axiom (the only one left)**: Multiple Recurrence for k ≥ 3.
    The deep part of Furstenberg's proof: ergodic decomposition combined
    with structural analysis of measure-preserving systems. -/
axiom multiple_recurrence_ge3 (sys : System) (hpos : sys.μ sys.B ≠ 0)
    (k : ℕ) (hk : k ≥ 3) :
    ∃ n : ℕ, n > 0 ∧
      sys.μ (⋂ (i : Fin k), sys.T^[↑i * n] ⁻¹' sys.B) ≠ 0

/-!
## Full Szemerédi via the Ergodic Route

Assembling the infinite Szemerédi theorem for all k ≥ 1:
  d*(A) > 0 → A contains k-APs for all k

Uses: correspondence (proved) + Poincaré (Mathlib, k≤2) + the multiple-recurrence axiom (k≥3).
-/

/-- **Infinite Szemerédi via Furstenberg**: Sets with positive upper Banach
    density contain k-term APs for all k ≥ 1.
    Combines correspondence (proved), Poincaré (Mathlib), and
    multiple recurrence (the sole remaining axiom). -/
theorem szemeredi_ergodic (A : Set ℕ) (δ : ℝ) (hδ : δ > 0)
    (hd : HasUpperDensityGe A δ) (k : ℕ) (hk : k ≥ 1) :
    ∃ a n : ℕ, n > 0 ∧ ∀ j < k, a + j * n ∈ A := by
  -- Apply correspondence to get the system
  obtain ⟨sys, hμB, hreturn2, hreturnk⟩ := furstenberg_correspondence A δ hδ hd
  have hB_pos := (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hδ) hμB).ne'
  rcases Nat.lt_or_ge k 3 with hlt | hge
  · -- k ∈ {1, 2}: Poincaré recurrence suffices
    obtain ⟨a, n, hn, ha, han⟩ := szemeredi_k2_ergodic A δ hδ hd
    exact ⟨a, n, hn, fun j hj => by
      have : j ≤ 1 := by omega
      interval_cases j <;> simpa⟩
  · -- k ≥ 3: multiple recurrence axiom
    obtain ⟨n, hn_pos, hn_meas⟩ := multiple_recurrence_ge3 sys hB_pos k hge
    obtain ⟨a, ha⟩ := hreturnk k n hk hn_pos hn_meas
    exact ⟨a, n, hn_pos, ha⟩

/-!
## Summary: Feasibility of Formalizing Furstenberg's Proof

| Component | Status | Source |
|-----------|--------|--------|
| Measure-preserving maps | ✅ Available | Mathlib.Dynamics.Ergodic.MeasurePreserving |
| Iteration T^[n] | ✅ Available | MeasurePreserving.iterate |
| Conservative systems | ✅ Available | Mathlib.Dynamics.Ergodic.Conservative |
| Poincaré recurrence | ✅ Available | Conservative.exists_gt_measure_inter_ne_zero |
| Probability measures | ✅ Available | Mathlib.MeasureTheory.Measure |
| Correspondence principle | ✅ Proved (2026-07-24) | Proofs/FurstenbergCorrespondenceOQ01.lean |
| Multiple recurrence k≥3 | ❌ Axiomatized | Needs ergodic decomposition (~2000+ lines) |

**Conclusion**: Furstenberg's proof CAN be formalized in Lean 4.
The foundation (measure theory, dynamics, Poincaré) exists in Mathlib.
The remaining gaps (correspondence construction, multiple recurrence) are
well-defined mathematical constructions, not foundational limitations.
The k=2 case already works with only the correspondence axiom.
-/

end Furstenberg
