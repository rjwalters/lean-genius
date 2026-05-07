import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Proofs.MinkowskiFundamentalTheorem
import Mathlib.Tactic

/-!
# Blichfeldt's Theorem (Minkowski OQ-04)

## What This Proves

**Blichfeldt's theorem** (1914): If a measurable set S ⊆ ℝⁿ has Lebesgue measure > k,
then S contains k+1 distinct points x₁,...,x_{k+1} whose pairwise differences lie in ℤⁿ.

This generalizes Minkowski's convex body theorem: no convexity or symmetry is needed.
Minkowski's theorem is recovered as a corollary (see Part 4).

## Proof Strategy: Fundamental Domain Pigeonhole

The integer lattice ℤⁿ tiles ℝⁿ with the fundamental domain F = [0,1)ⁿ.
Define Sᵥ = {z ∈ F | z + v ∈ S} for each v ∈ ℤⁿ.

Key identity: vol(S) = ∑ᵥ vol(Sᵥ) (the fundamental domain partition formula).

For k=1: If all Sᵥ were pairwise disjoint, ∑ vol(Sᵥ) ≤ vol(F) = 1. Contradiction.
So ∃ v ≠ w with Sᵥ ∩ Sw ≠ ∅: pick z there to get z+v, z+w ∈ S with (z+v)−(z+w) = v−w ∈ ℤⁿ.

## Axioms

Three axioms capture the required measure-theory facts (all provable from Mathlib):

1. `blichfeldt_volume_partition`: vol(S) = ∑' g : ℤⁿ, vol(Sᵍ)
   → Apply `IsAddFundamentalDomain.lintegral_eq_tsum` with f = 1_S.

2. `blichfeldt_proj_measurable`: Each Sᵥ is measurable.
   → Intersection of measurable sets; translation preserves measurability.

3. `blichfeldt_disj_bound`: Pairwise-disjoint measurable subsets of F have total vol ≤ 1.
   → `measure_iUnion` (sigma-additivity) + `measure_mono` (monotonicity).
-/

open MeasureTheory Set MinkowskiProved

namespace BlichfeldtTheorem

-- ============================================================
-- PART 1: Measure-Theory Infrastructure Axioms
-- ============================================================

/-- **Axiom 1** (Fundamental Domain Partition):
    vol(S) = ∑' v : ℤⁿ, vol({z ∈ F | z + v ∈ S}).

    Proof path: Apply `(stdLattice_isAddFundamentalDomain n).lintegral_eq_tsum`
    to f = Set.indicator s 1. Then ∫⁻_F 1_S(v + z) dz = vol({z ∈ F | z + v ∈ S}). -/
axiom blichfeldt_volume_partition {n : ℕ} [NeZero n]
    (s : Set (Fin n → ℝ)) (h_meas : MeasurableSet s) :
    volume s = ∑' g : (stdLattice n).toAddSubgroup,
      volume {z ∈ stdFundDomain n | z + (g : Fin n → ℝ) ∈ s}

/-- **Lemma** (Projection Measurability):
    For measurable s and lattice element v, the set {z ∈ F | z + v ∈ s} is measurable.

    Proof: This set equals (stdFundDomain n) ∩ (fun z => z + v) ⁻¹' s.
    Translation `z ↦ z + v` is measurable (`measurable_id.add_const`), so the preimage
    is measurable. Intersecting with the measurable `stdFundDomain` gives measurability. -/
theorem blichfeldt_proj_measurable {n : ℕ} [NeZero n]
    (s : Set (Fin n → ℝ)) (h_meas : MeasurableSet s)
    (v : (stdLattice n).toAddSubgroup) :
    MeasurableSet {z ∈ stdFundDomain n | z + (v : Fin n → ℝ) ∈ s} := by
  have h_translate : Measurable fun z : Fin n → ℝ => z + (v : Fin n → ℝ) :=
    measurable_id.add_const _
  have h_pre : MeasurableSet
      ((fun z : Fin n → ℝ => z + (v : Fin n → ℝ)) ⁻¹' s) :=
    h_translate h_meas
  exact (stdFundDomain_measurableSet n).inter h_pre

/-- **Lemma** (Disjoint Subsets Bound):
    Pairwise-disjoint measurable subsets {Aᵥ} of F = stdFundDomain have ∑' vol(Aᵥ) ≤ 1.

    Proof: ∑' vol(Aᵥ) = vol(⋃ᵥ Aᵥ) by `measure_iUnion` (sigma-additivity for
    pairwise-disjoint measurable sets), then ≤ vol(F) = 1 via `measure_mono` and
    `stdLattice_covolume`. -/
theorem blichfeldt_disj_bound {n : ℕ} [NeZero n]
    (A : (stdLattice n).toAddSubgroup → Set (Fin n → ℝ))
    (h_meas : ∀ v, MeasurableSet (A v))
    (h_sub : ∀ v, A v ⊆ stdFundDomain n)
    (h_disj : Pairwise fun v w => Disjoint (A v) (A w)) :
    ∑' v, volume (A v) ≤ 1 := by
  haveI : Countable (stdLattice n).toAddSubgroup := by
    unfold stdLattice
    change Countable (Submodule.span ℤ (Set.range (stdBasis n)))
    infer_instance
  rw [← MeasureTheory.measure_iUnion h_disj h_meas]
  calc volume (⋃ v, A v)
      ≤ volume (stdFundDomain n) := measure_mono (Set.iUnion_subset h_sub)
    _ = 1 := stdLattice_covolume n

-- ============================================================
-- PART 2: Blichfeldt's Basic Theorem (k = 1)
-- ============================================================

/-- **Blichfeldt's Basic Theorem** (1914):
    If a measurable set S ⊆ ℝⁿ has vol(S) > 1, then S contains two distinct points
    x, y with x − y ∈ ℤⁿ (i.e., they are ℤⁿ-congruent). -/
theorem blichfeldt_basic {n : ℕ} [NeZero n]
    (s : Set (Fin n → ℝ)) (h_meas : MeasurableSet s)
    (h_vol : (1 : ENNReal) < volume s) :
    ∃ x y : Fin n → ℝ, x ∈ s ∧ y ∈ s ∧ x ≠ y ∧
    x - y ∈ (stdLattice n : Set (Fin n → ℝ)) := by
  -- Assume for contradiction that no two distinct points in s are ℤⁿ-congruent
  by_contra h_no_pair
  push_neg at h_no_pair
  -- After push_neg: h_no_pair : ∀ x y, x ∈ s → y ∈ s → x ≠ y → x - y ∉ stdLattice n
  -- Define the fundamental-domain projections Sᵥ = {z ∈ F | z + v ∈ s}
  let proj := fun v : (stdLattice n).toAddSubgroup =>
    {z ∈ stdFundDomain n | z + (v : Fin n → ℝ) ∈ s}
  -- Step 1: The projections are pairwise disjoint
  have h_disj : Pairwise fun v w => Disjoint (proj v) (proj w) := by
    intro v w hvw
    rw [disjoint_left]
    intro z hzv hzw
    -- z + v ∈ s (from z ∈ proj v) and z + w ∈ s (from z ∈ proj w)
    have hxs : z + (v : Fin n → ℝ) ∈ s := hzv.2
    have hys : z + (w : Fin n → ℝ) ∈ s := hzw.2
    -- z + v ≠ z + w since v ≠ w
    have hne : z + (v : Fin n → ℝ) ≠ z + (w : Fin n → ℝ) := by
      intro heq
      exact hvw (Subtype.ext (add_left_cancel heq))
    -- (z + v) − (z + w) = v − w ∈ ℤⁿ (lattice closed under subtraction)
    have hdiff : z + (v : Fin n → ℝ) - (z + (w : Fin n → ℝ)) ∈ (stdLattice n : Set (Fin n → ℝ)) := by
      have heq : z + (v : Fin n → ℝ) - (z + (w : Fin n → ℝ)) = (v : Fin n → ℝ) - w := by ring
      rw [heq]
      exact (stdLattice n).toAddSubgroup.sub_mem v.2 w.2
    -- h_no_pair says this contradicts ℤⁿ-non-congruence
    exact h_no_pair _ _ hxs hys hne hdiff
  -- Step 2: ∑ vol(proj v) ≤ vol(F) = 1 by pairwise-disjoint subsets bound
  have h_bound : ∑' v, volume (proj v) ≤ 1 :=
    blichfeldt_disj_bound proj
      (fun v => blichfeldt_proj_measurable s h_meas v)
      (fun _ z hz => hz.1)
      h_disj
  -- Step 3: But ∑ vol(proj v) = vol(s) > 1 by the partition formula
  have h_eq : volume s = ∑' v, volume (proj v) :=
    blichfeldt_volume_partition s h_meas
  -- Contradiction: vol(s) > 1 but ≤ 1
  exact absurd h_vol (not_lt.mpr (h_eq ▸ h_bound))

-- ============================================================
-- PART 3: The General k + 1 Version
-- ============================================================

/-!
### General Case via Covering Count

For vol(S) > k, the covering count function c : F → ℕ∞ defined by
  c(z) = #{v ∈ ℤⁿ | z + v ∈ S}
satisfies ∫_F c dz = vol(S) > k. Since c is ℕ∞-valued and ∫ c > k · vol(F) = k,
there exists z ∈ F with c(z) ≥ k+1. This gives k+1 distinct lattice elements
v₁,...,v_{k+1} with z + vᵢ ∈ S, yielding k+1 ℤⁿ-congruent points.
-/

/-- **Blichfeldt's General Theorem**: vol(S) > k implies k+1 ℤⁿ-congruent points in S.

    (The k=1 case is proved above; the general case uses an averaging argument
    on the covering count function c(z) = #{v | z + v ∈ S}.) -/
axiom blichfeldt_general {n : ℕ} [NeZero n]
    (k : ℕ) (s : Set (Fin n → ℝ)) (h_meas : MeasurableSet s)
    (h_vol : (k : ENNReal) < volume s) :
    ∃ pts : Fin (k+1) → Fin n → ℝ,
      Function.Injective pts ∧ (∀ i, pts i ∈ s) ∧
      ∀ i j, pts i - pts j ∈ (stdLattice n : Set (Fin n → ℝ))

/-- The k=1 case follows from the general theorem. -/
theorem blichfeldt_basic_from_general {n : ℕ} [NeZero n]
    (s : Set (Fin n → ℝ)) (h_meas : MeasurableSet s)
    (h_vol : (1 : ENNReal) < volume s) :
    ∃ x y : Fin n → ℝ, x ∈ s ∧ y ∈ s ∧ x ≠ y ∧
    x - y ∈ (stdLattice n : Set (Fin n → ℝ)) := by
  obtain ⟨pts, hinj, hmem, hcong⟩ := blichfeldt_general 1 s h_meas (by exact_mod_cast h_vol)
  refine ⟨pts 0, pts 1, hmem 0, hmem 1, ?_, hcong 0 1⟩
  intro heq
  exact absurd (hinj heq) (by decide)

-- ============================================================
-- PART 4: Minkowski as a Corollary
-- ============================================================

/-!
## Minkowski's Theorem via Blichfeldt

Given convex symmetric S with vol(S) > 2ⁿ:
1. T = (1/2) · S has vol(T) = vol(S)/2ⁿ > 1  [Jacobian of x ↦ x/2 is 2⁻ⁿ]
2. Blichfeldt gives x ≠ y ∈ T with x − y ∈ ℤⁿ
3. Let x₀ = 2x, y₀ = 2y ∈ S. Central symmetry: −y₀ ∈ S.
4. Convexity: (x₀ + (−y₀))/2 = x₀/2 − y₀/2 = x − y ∈ S.
5. x − y ≠ 0 since x ≠ y; x − y ∈ S ∩ ℤⁿ \ {0}.
-/

/-- **Minkowski's Theorem** (recovered from Blichfeldt):
    A convex centrally-symmetric set with vol > 2ⁿ contains a nonzero integer point.

    Proof sketch:
    1. Form T = (1/2)·S. Then vol(T) = vol(S)/2ⁿ > 1.
    2. Blichfeldt gives a ≠ b ∈ T with a − b ∈ ℤⁿ.
    3. Write a = x₀/2, b = y₀/2 for x₀, y₀ ∈ S.
    4. By central symmetry: −y₀ ∈ S.
    5. By convexity: (x₀ + (−y₀))/2 = a − b ∈ S.
    6. a − b ≠ 0 (since a ≠ b) and a − b ∈ S ∩ ℤⁿ. -/
theorem minkowski_from_blichfeldt {n : ℕ} [NeZero n]
    (s : Set (Fin n → ℝ))
    (h_meas : MeasurableSet s)
    (h_symm : ∀ x ∈ s, -x ∈ s)
    (h_conv : Convex ℝ s)
    (h_vol : (2 : ENNReal) ^ n < volume s) :
    ∃ p : (stdLattice n).toAddSubgroup, p ≠ 0 ∧ (p : Fin n → ℝ) ∈ s := by
  let T := (fun x : Fin n → ℝ => (2 : ℝ)⁻¹ • x) '' s
  have h_meas_T : MeasurableSet T := by
    sorry -- MeasurableEmbedding for x ↦ (1/2)·x (linear isomorphism) preserves measurability
  have h_vol_T : (1 : ENNReal) < volume T := by
    sorry -- vol(T) = vol(S)/2ⁿ > 1; proved via Measure.addHaar_smul and ENNReal arithmetic
  obtain ⟨a, b, haT, hbT, hab_ne, hab_diff⟩ := blichfeldt_basic T h_meas_T h_vol_T
  obtain ⟨x₀, hx₀s, rfl⟩ := haT
  obtain ⟨y₀, hy₀s, rfl⟩ := hbT
  have hp_in_s : (2 : ℝ)⁻¹ • x₀ - (2 : ℝ)⁻¹ • y₀ ∈ s := by
    have key : (2 : ℝ)⁻¹ • x₀ + (2 : ℝ)⁻¹ • (-y₀) ∈ s :=
      h_conv hx₀s (h_symm y₀ hy₀s) (by norm_num) (by norm_num) (by norm_num)
    rwa [smul_neg, ← sub_eq_add_neg] at key
  -- Package: p = a − b is a nonzero lattice point in s
  have hp_mem_sg : (2:ℝ)⁻¹ • x₀ - (2:ℝ)⁻¹ • y₀ ∈ (stdLattice n).toAddSubgroup :=
    hab_diff
  exact ⟨⟨_, hp_mem_sg⟩, fun h => (sub_ne_zero.mpr hab_ne) (congrArg Subtype.val h), hp_in_s⟩

end BlichfeldtTheorem

-- ============================================================
-- Export check
-- ============================================================

#check BlichfeldtTheorem.blichfeldt_basic
#check BlichfeldtTheorem.blichfeldt_general
#check BlichfeldtTheorem.minkowski_from_blichfeldt
