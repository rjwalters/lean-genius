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

One axiom remains (down from four in earlier sessions):

1. `blichfeldt_general`: the k≥1 covering-count averaging form.

The k=1 case (`blichfeldt_basic`) is now fully proved without any axiom by
applying Mathlib's `IsAddFundamentalDomain.exists_ne_zero_vadd_eq` directly:
the standard ℤⁿ-fundamental-domain has covolume 1, so a measurable set with
volume > 1 admits two points x, y with `g +ᵥ x = y` for some `g ≠ 0` in ℤⁿ.

Three former measure-theoretic axioms are now proved theorems / unused:
- `blichfeldt_proj_measurable` (translation continuity → preimage measurability)
- `blichfeldt_disj_bound` (sigma-additivity + monotonicity against vol(F)=1)
- `blichfeldt_volume_partition` is no longer needed (the basic theorem now
  uses Mathlib's pigeonhole directly).

`minkowski_from_blichfeldt` is now sorry-free: the half-scaling T = (1/2)·s is
shown measurable by rewriting as the preimage under doubling, and the volume
identity vol(T) = vol(s)/2ⁿ is closed via `Measure.addHaar_smul`.
-/

open MeasureTheory Set MinkowskiProved Pointwise

namespace BlichfeldtTheorem

-- ============================================================
-- PART 1: Measure-Theory Infrastructure (proved theorems)
-- ============================================================

/-!
The two helper theorems below were used by an earlier version of `blichfeldt_basic`
that built up the pigeonhole from the fundamental-domain partition formula. The
current proof of `blichfeldt_basic` uses Mathlib's
`IsAddFundamentalDomain.exists_ne_zero_vadd_eq` directly, so these theorems are
now self-contained pieces of infrastructure (kept as reusable building blocks
for the still-open `blichfeldt_general`).
-/

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
    x, y with x − y ∈ ℤⁿ (i.e., they are ℤⁿ-congruent).

    Proved directly from `MeasureTheory.IsAddFundamentalDomain.exists_ne_zero_vadd_eq`
    (the additive form of `exists_ne_one_smul_eq`): the standard ℤⁿ-fundamental-domain
    has covolume 1, so a measurable set of volume > 1 cannot avoid all lattice
    translates and we get two points x, y in s with `g +ᵥ x = y` for some `g ≠ 0`. -/
theorem blichfeldt_basic {n : ℕ} [NeZero n]
    (s : Set (Fin n → ℝ)) (h_meas : MeasurableSet s)
    (h_vol : (1 : ENNReal) < volume s) :
    ∃ x y : Fin n → ℝ, x ∈ s ∧ y ∈ s ∧ x ≠ y ∧
    x - y ∈ (stdLattice n : Set (Fin n → ℝ)) := by
  haveI : Countable (stdLattice n).toAddSubgroup := by
    unfold stdLattice
    change Countable (Submodule.span ℤ (Set.range (stdBasis n)))
    infer_instance
  -- F has volume 1 (`stdLattice_covolume`), so volume F < volume s
  have h_vol_lt : volume (stdFundDomain n) < volume s := by
    rw [stdLattice_covolume]; exact h_vol
  -- Mathlib's pigeonhole on a fundamental domain: ∃ x ∈ s, ∃ y ∈ s, ∃ g ≠ 0, g +ᵥ x = y
  obtain ⟨x, hx, y, hy, g, hg, hgxy⟩ :=
    (stdLattice_isAddFundamentalDomain n).exists_ne_zero_vadd_eq
      h_meas.nullMeasurableSet h_vol_lt
  -- Unfold the AddSubgroup action: g +ᵥ x = (g : ℝⁿ) + x
  have hg_eq : (g : Fin n → ℝ) + x = y := by
    have h := hgxy
    rw [AddSubgroup.vadd_def, vadd_eq_add] at h
    exact h
  refine ⟨y, x, hy, hx, ?_, ?_⟩
  · -- y ≠ x: from `(g : ℝⁿ) + x = y` and `g ≠ 0`, equality y = x would force g = 0
    intro hyx
    apply hg
    have hg_val : (g : Fin n → ℝ) = 0 := by
      have h1 : (g : Fin n → ℝ) + x = (0 : Fin n → ℝ) + x := by
        rw [zero_add, hg_eq]; exact hyx
      exact add_right_cancel h1
    exact Subtype.ext hg_val
  · -- y - x = (g : ℝⁿ) ∈ stdLattice
    show y - x ∈ (stdLattice n : Set (Fin n → ℝ))
    have h_diff : y - x = (g : Fin n → ℝ) := by rw [← hg_eq]; ring
    rw [h_diff]
    exact g.2

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
  -- Bridge: T = (2:ℝ)⁻¹ • s definitionally (Set.SMul via Pointwise)
  have h_T_eq : T = (2 : ℝ)⁻¹ • s := rfl
  have h2_ne : (2 : ℝ) ≠ 0 := by norm_num
  -- Measurability: rewrite T as preimage of s under doubling, then preimage of measurable
  have h_meas_T : MeasurableSet T := by
    have h_pre : (2 : ℝ)⁻¹ • s = ((2 : ℝ) • · : (Fin n → ℝ) → (Fin n → ℝ)) ⁻¹' s := by
      ext y
      simp only [Set.mem_smul_set, Set.mem_preimage]
      refine ⟨?_, ?_⟩
      · rintro ⟨a, has, rfl⟩
        rwa [smul_smul, mul_inv_cancel₀ h2_ne, one_smul]
      · intro h
        refine ⟨(2 : ℝ) • y, h, ?_⟩
        rw [smul_smul, inv_mul_cancel₀ h2_ne, one_smul]
    rw [h_T_eq, h_pre]
    exact h_meas.preimage (measurable_const_smul (2 : ℝ))
  -- Volume identity: vol(T) = (1/2)^n · vol(s) > 1 since vol(s) > 2^n
  have h_vol_T : (1 : ENNReal) < volume T := by
    rw [h_T_eq, MeasureTheory.Measure.addHaar_smul volume ((2 : ℝ)⁻¹) s]
    -- Goal: 1 < ENNReal.ofReal |(2:ℝ)⁻¹ ^ finrank ℝ (Fin n → ℝ)| * volume s
    rw [Module.finrank_fin_fun, abs_pow]
    -- Goal: 1 < ENNReal.ofReal (|(2:ℝ)⁻¹| ^ n) * volume s
    rw [ENNReal.ofReal_pow (abs_nonneg _)]
    -- Goal: 1 < (ENNReal.ofReal |(2:ℝ)⁻¹|) ^ n * volume s
    have h_abs : |((2 : ℝ)⁻¹)| = (2 : ℝ)⁻¹ := by norm_num
    rw [h_abs]
    -- Convert ENNReal.ofReal (2:ℝ)⁻¹ to (2 : ENNReal)⁻¹
    have h_ofReal : ENNReal.ofReal ((2 : ℝ)⁻¹) = (2 : ENNReal)⁻¹ := by
      rw [show ((2 : ℝ)⁻¹) = 1 / 2 by ring,
          ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ) < 2)]
      simp
    rw [h_ofReal]
    -- Goal: 1 < (2 : ENNReal)⁻¹ ^ n * volume s
    -- Use h_vol : (2 : ENNReal)^n < volume s; multiply both sides by (2⁻¹)^n
    have h2_inv_ne_zero_base : (2 : ENNReal)⁻¹ ≠ 0 :=
      ENNReal.inv_ne_zero.mpr (by norm_num)
    have h2_inv_ne_top_base : (2 : ENNReal)⁻¹ ≠ ⊤ :=
      ENNReal.inv_ne_top.mpr (by norm_num)
    have h2_inv_ne_zero : ((2 : ENNReal)⁻¹) ^ n ≠ 0 :=
      pow_ne_zero _ h2_inv_ne_zero_base
    have h2_inv_ne_top : ((2 : ENNReal)⁻¹) ^ n ≠ ⊤ := by
      intro hcontra
      rw [ENNReal.pow_eq_top_iff] at hcontra
      exact h2_inv_ne_top_base hcontra.1
    have h_step : ((2 : ENNReal)⁻¹) ^ n * (2 : ENNReal) ^ n
                  < ((2 : ENNReal)⁻¹) ^ n * volume s :=
      (ENNReal.mul_lt_mul_left h2_inv_ne_zero h2_inv_ne_top).mpr h_vol
    have h_eq_one : ((2 : ENNReal)⁻¹) ^ n * (2 : ENNReal) ^ n = 1 := by
      rw [← mul_pow,
          ENNReal.inv_mul_cancel (by norm_num : (2 : ENNReal) ≠ 0)
            (by norm_num : (2 : ENNReal) ≠ ⊤),
          one_pow]
    rw [h_eq_one] at h_step
    exact h_step
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
