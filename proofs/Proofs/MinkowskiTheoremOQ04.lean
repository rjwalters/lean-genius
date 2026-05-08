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

Zero axioms remain (down from four in earlier sessions). Build status of
the post-S14 axiom→theorem flip is gated on Docker CI; meta.json flags are
synced in a follow-up `verified` PR.

The k=1 case (`blichfeldt_basic`) is fully proved by applying Mathlib's
`IsAddFundamentalDomain.exists_ne_zero_vadd_eq` directly: the standard
ℤⁿ-fundamental-domain has covolume 1, so a measurable set with volume > 1
admits two points x, y with `g +ᵥ x = y` for some `g ≠ 0` in ℤⁿ.

The general k≥0 case (`blichfeldt_general`) is now a proved theorem (S13–S14,
PRs #17298/#17329). Strategy (Path A contrapose):
- **Move A**: ∫⁻ z in F, c(z) ∂volume = volume s, where
  c(z) = ∑' v∈ℤⁿ, 1_S((v:ℝⁿ)+z), via `volume_eq_setLIntegral_indicator_tsum`
  (S9, PR #16995) — itself proved from `IsAddFundamentalDomain.lintegral_eq_tsum''`
  + Tonelli.
- **Move B**: pointwise c(z) ≤ k contrapositively from the conclusion's
  negation, with the `tsum`-of-indicators rewritten as `T.encard` via
  `tsum_subtype + ENNReal.tsum_set_one`, then a finset is extracted from
  the encard bound and turned into `Fin (k+1) → L` via `Set.toFinset_card`
  + `Fintype.equivFinOfCardEq`.
- **Move C**: integrate the pointwise bound against the fundamental domain
  to get `volume s ≤ k`, contradicting the hypothesis `k < volume s`.

Three former measure-theoretic axioms are now proved theorems / unused:
- `blichfeldt_proj_measurable` (translation continuity → preimage measurability)
- `blichfeldt_disj_bound` (sigma-additivity + monotonicity against vol(F)=1)
- `blichfeldt_volume_partition` is no longer needed (the basic theorem now
  uses Mathlib's pigeonhole directly).

`minkowski_from_blichfeldt` is sorry-free: the half-scaling T = (1/2)·s is
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

`volume_eq_setLIntegral_indicator_tsum` below proves the integral identity
`∫_F (∑' g, 1_S(g + x)) dx = vol(S)` directly from `IsAddFundamentalDomain.lintegral_eq_tsum''`
combined with Tonelli (`lintegral_tsum`); this is the analytic core of the covering-count
argument and reduces the remaining work for `blichfeldt_general` to the combinatorial
extraction step (from a pointwise tsum > k, produce k+1 distinct lattice elements).
-/

/-- **Covering-count integral identity** (infrastructure for `blichfeldt_general`).

For any measurable `s ⊆ ℝⁿ`, the integral over the standard fundamental domain `F` of
the "covering count" — the sum over the integer lattice `ℤⁿ` of the indicator that
`(g : ℝⁿ) + x ∈ s` — equals `volume s`:
  ∫⁻ x in F, (∑' g : ℤⁿ, 1_s((g : ℝⁿ) + x)) ∂volume = volume s.

Proof: applying `IsAddFundamentalDomain.lintegral_eq_tsum''` to the indicator of `s`
gives `∫⁻ x, 1_s = ∑' g, ∫⁻ x in F, 1_s(g +ᵥ x)`; the LHS is `volume s` by
`lintegral_indicator_const` with constant 1. Tonelli (`lintegral_tsum`) swaps the
tsum and the integral, and `AddSubgroup.vadd_def + vadd_eq_add` unfold `g +ᵥ x` to
`(g : ℝⁿ) + x`. -/
theorem volume_eq_setLIntegral_indicator_tsum {n : ℕ} [NeZero n]
    {s : Set (Fin n → ℝ)} (h_meas : MeasurableSet s) :
    ∫⁻ x in stdFundDomain n,
        (∑' g : (stdLattice n).toAddSubgroup,
            s.indicator (fun _ => (1 : ENNReal))
              ((g : Fin n → ℝ) + x)) ∂volume
      = volume s := by
  haveI : Countable (stdLattice n).toAddSubgroup := by
    unfold stdLattice
    change Countable (Submodule.span ℤ (Set.range (stdBasis n)))
    infer_instance
  set ind : (Fin n → ℝ) → ENNReal := s.indicator (fun _ => (1 : ENNReal)) with h_ind_def
  have h_ind_meas : Measurable ind :=
    measurable_const.indicator h_meas
  have h_shift_meas_vadd : ∀ g : (stdLattice n).toAddSubgroup,
      Measurable (fun x : Fin n → ℝ => ind (g +ᵥ x)) := by
    intro g
    have h_add : Measurable (fun x : Fin n → ℝ => g +ᵥ x) := by
      have h_eq : (fun x : Fin n → ℝ => g +ᵥ x)
                = fun x => (g : Fin n → ℝ) + x := by
        funext x
        rw [AddSubgroup.vadd_def, vadd_eq_add]
      rw [h_eq]
      exact measurable_const.add measurable_id
    exact h_ind_meas.comp h_add
  have h_fund := stdLattice_isAddFundamentalDomain n
  calc ∫⁻ x in stdFundDomain n,
          (∑' g : (stdLattice n).toAddSubgroup, ind ((g : Fin n → ℝ) + x)) ∂volume
      = ∫⁻ x in stdFundDomain n,
          (∑' g : (stdLattice n).toAddSubgroup, ind (g +ᵥ x)) ∂volume := by
        apply lintegral_congr
        intro x
        apply tsum_congr
        intro g
        -- `g +ᵥ x = (g : Fin n → ℝ) + x` is definitionally equal via
        -- `AddSubgroup.vadd_def := rfl`, so `congr 1` closes the goal directly.
        congr 1
    _ = ∑' g : (stdLattice n).toAddSubgroup,
          ∫⁻ x in stdFundDomain n, ind (g +ᵥ x) ∂volume :=
        lintegral_tsum (fun g => (h_shift_meas_vadd g).aemeasurable)
    _ = ∫⁻ x, ind x ∂volume :=
        (h_fund.lintegral_eq_tsum'' ind).symm
    _ = volume s := by
        rw [h_ind_def, lintegral_indicator_const h_meas, one_mul]

/-- **Blichfeldt's General Theorem**: vol(S) > k implies k+1 ℤⁿ-congruent points in S.

Path A (contrapose route, S11 prototype + S12 v4.26.0 API fix). Mirrors Mathlib's
`k=1` `exists_pair_mem_lattice_not_disjoint_vadd` with Tonelli replacing
`measure_iUnion₀`.

* Move A: Reuse `volume_eq_setLIntegral_indicator_tsum` (proved S9).
* Move B: Pointwise `c z ≤ k` from contraposed hypothesis via `tsum_subtype` +
  `ENNReal.tsum_set_one`.
* Move C: Integrate via `setLIntegral_mono_ae` + `setLIntegral_const` +
  `stdLattice_covolume`.

The `Fin (k+1) → ↑F₀` injection (Move B inner) is constructed against the
v4.26.0 `Mathlib` pin (`mathlib 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`)
using only `Set.toFinset_card` + simp (S12 verification). -/
theorem blichfeldt_general {n : ℕ} [NeZero n]
    (k : ℕ) (s : Set (Fin n → ℝ)) (h_meas : MeasurableSet s)
    (h_vol : (k : ENNReal) < volume s) :
    ∃ pts : Fin (k+1) → Fin n → ℝ,
      Function.Injective pts ∧ (∀ i, pts i ∈ s) ∧
      ∀ i j, pts i - pts j ∈ (stdLattice n : Set (Fin n → ℝ)) := by
  haveI : Countable (stdLattice n).toAddSubgroup := by
    unfold stdLattice
    change Countable (Submodule.span ℤ (Set.range (stdBasis n)))
    infer_instance
  -- Container reformulation: factor out the lattice translation z.
  suffices h : ∃ z : Fin n → ℝ, ∃ vs : Fin (k+1) → (stdLattice n).toAddSubgroup,
      Function.Injective vs ∧ ∀ i, z + (vs i : Fin n → ℝ) ∈ s by
    obtain ⟨z, vs, hvs_inj, hvs_in⟩ := h
    refine ⟨fun i => z + (vs i : Fin n → ℝ), ?_, hvs_in, ?_⟩
    · intro i j hij
      have h_coe : (vs i : Fin n → ℝ) = (vs j : Fin n → ℝ) := add_left_cancel hij
      exact hvs_inj (Subtype.ext h_coe)
    · intro i j
      show (z + (vs i : Fin n → ℝ)) - (z + (vs j : Fin n → ℝ))
        ∈ (stdLattice n : Set (Fin n → ℝ))
      have h_sub : (z + (vs i : Fin n → ℝ)) - (z + (vs j : Fin n → ℝ))
                = (vs i : Fin n → ℝ) - (vs j : Fin n → ℝ) := by ring
      rw [h_sub, ← AddSubgroupClass.coe_sub]
      exact (vs i - vs j).2
  -- Contrapose to a volume bound.
  by_contra h_neg
  push_neg at h_neg
  -- h_neg : ∀ z, ∀ vs, Injective vs → ∃ i, z + (vs i : ℝⁿ) ∉ s
  apply absurd h_vol (not_lt.mpr ?_)
  -- Move A: ∫⁻ z in F, c z ∂volume = volume s
  rw [← volume_eq_setLIntegral_indicator_tsum h_meas]
  -- Move B: pointwise c z ≤ (k : ℝ≥0∞)
  have h_pointwise : ∀ z : Fin n → ℝ,
      (∑' v : (stdLattice n).toAddSubgroup,
          s.indicator (fun _ => (1 : ENNReal)) ((v : Fin n → ℝ) + z)) ≤ (k : ENNReal) := by
    intro z
    set T : Set (stdLattice n).toAddSubgroup :=
      {v | (v : Fin n → ℝ) + z ∈ s} with hT_def
    -- Bridge: tsum-of-indicators on L = T.encard.
    have h_summand_eq : ∀ v : (stdLattice n).toAddSubgroup,
        s.indicator (fun _ => (1 : ENNReal)) ((v : Fin n → ℝ) + z)
          = T.indicator (fun _ => (1 : ENNReal)) v := by
      intro v
      by_cases hv : (v : Fin n → ℝ) + z ∈ s
      · simp [Set.indicator, hv, hT_def, Set.mem_setOf_eq]
      · simp [Set.indicator, hv, hT_def, Set.mem_setOf_eq]
    have h_bridge :
        ∑' v : (stdLattice n).toAddSubgroup,
            s.indicator (fun _ => (1 : ENNReal)) ((v : Fin n → ℝ) + z)
          = (T.encard : ENNReal) := by
      rw [tsum_congr h_summand_eq, ← tsum_subtype, ENNReal.tsum_set_one]
    rw [h_bridge]
    -- Bound encard ≤ k via contrapositive of h_neg.
    by_contra h_too_many
    push_neg at h_too_many
    -- h_too_many : (k : ℝ≥0∞) < (T.encard : ℝ≥0∞)
    have h_le_encard : ((k + 1 : ℕ) : ℕ∞) ≤ T.encard := by
      have h_lt_enat : (k : ℕ∞) < T.encard := by
        have h_cast : ((k : ℕ∞) : ENNReal) < ((T.encard : ENNReal)) := by exact_mod_cast h_too_many
        exact_mod_cast h_cast
      have h_succ : (k : ℕ∞) + 1 ≤ T.encard :=
        (ENat.add_one_le_iff (ENat.coe_ne_top k)).mpr h_lt_enat
      exact_mod_cast h_succ
    obtain ⟨T₀, hT₀_sub, hT₀_card⟩ :=
      Set.exists_subset_encard_eq h_le_encard
    have hT₀_finite : T₀.Finite := by
      rw [← Set.encard_lt_top_iff, hT₀_card]
      exact ENat.coe_lt_top _
    set F₀ : Finset _ := hT₀_finite.toFinset with hF₀_def
    have hF₀_card : F₀.card = k + 1 := by
      have h_eq : T₀.encard = (F₀.card : ℕ∞) := by
        show T₀.encard = (hT₀_finite.toFinset.card : ℕ∞)
        exact hT₀_finite.encard_eq_coe_toFinset_card
      rw [hT₀_card] at h_eq
      exact_mod_cast h_eq.symm
    -- Build Fin (k+1) → L injection from F₀ (S12 v4.26.0 fix: Set.toFinset_card path).
    obtain ⟨vs, hvs_inj, hvs_range⟩ : ∃ vs : Fin (k+1) → (stdLattice n).toAddSubgroup,
        Function.Injective vs ∧ Set.range vs = ↑F₀ := by
      have h_card : Fintype.card (↑F₀ : Set ↥(stdLattice n).toAddSubgroup) = k + 1 := by
        rw [← Set.toFinset_card]
        simp [hF₀_card]
      let e : (↑F₀ : Set ↥(stdLattice n).toAddSubgroup) ≃ Fin (k+1) :=
        Fintype.equivFinOfCardEq h_card
      refine ⟨fun i => (e.symm i).1, ?_, ?_⟩
      · intro i j hij; exact e.symm.injective (Subtype.ext hij)
      · ext x
        simp only [Set.mem_range, Finset.mem_coe]
        constructor
        · rintro ⟨i, rfl⟩; exact (e.symm i).2
        · intro hx; exact ⟨e ⟨x, hx⟩, by simp⟩
    -- Each vs i ∈ T (via T₀ ⊆ T), i.e., (vs i : ℝⁿ) + z ∈ s.
    have h_all_in : ∀ i, z + (vs i : Fin n → ℝ) ∈ s := by
      intro i
      have h_in_F₀ : vs i ∈ F₀ := by
        have : vs i ∈ Set.range vs := ⟨i, rfl⟩
        rwa [hvs_range, Finset.mem_coe] at this
      have h_in_T₀ : vs i ∈ T₀ := by
        rw [hF₀_def, Set.Finite.mem_toFinset] at h_in_F₀
        exact h_in_F₀
      have h_in_T : vs i ∈ T := hT₀_sub h_in_T₀
      have h_swap : (vs i : Fin n → ℝ) + z = z + (vs i : Fin n → ℝ) := by ring
      rwa [Set.mem_setOf_eq, h_swap] at h_in_T
    obtain ⟨i, h_not_in⟩ := h_neg z vs hvs_inj
    exact h_not_in (h_all_in i)
  -- Move C: integrate the pointwise bound.
  calc ∫⁻ z in stdFundDomain n,
          (∑' v : (stdLattice n).toAddSubgroup,
              s.indicator (fun _ => (1 : ENNReal)) ((v : Fin n → ℝ) + z)) ∂volume
      ≤ ∫⁻ _ in stdFundDomain n, (k : ENNReal) ∂volume := by
        apply MeasureTheory.setLIntegral_mono_ae measurable_const.aemeasurable
        exact MeasureTheory.ae_of_all _ (fun z _ => h_pointwise z)
    _ = (k : ENNReal) * volume (stdFundDomain n) := by
        rw [MeasureTheory.setLIntegral_const]
    _ = (k : ENNReal) * 1 := by rw [stdLattice_covolume]
    _ = (k : ENNReal) := mul_one _

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

/-- **Blichfeldt at k = 2**: a measurable set in ℝⁿ with volume > 2 contains
three pairwise-distinct points whose pairwise differences all lie in ℤⁿ.

This is the smallest specialization of `blichfeldt_general` beyond the k=1
case (`blichfeldt_basic`); k=1 produces a single ℤⁿ-related pair, while k=2
forces a *triple* with all three pairwise differences in ℤⁿ — i.e. a single
lattice coset hits S in at least three points. Pedagogically this is the
canonical witness that the general Blichfeldt strengthens the basic form:
no naive iteration of the k=1 case yields three points in a common coset.

Specialization of `blichfeldt_general` at k = 2; introduced in S15
(researcher-12, 2026-05-08) as a downstream consumer of the post-S14
axiom→theorem flip. -/
theorem blichfeldt_three_points {n : ℕ} [NeZero n]
    (s : Set (Fin n → ℝ)) (h_meas : MeasurableSet s)
    (h_vol : (2 : ENNReal) < volume s) :
    ∃ x y z : Fin n → ℝ,
      x ∈ s ∧ y ∈ s ∧ z ∈ s ∧
      x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
      x - y ∈ (stdLattice n : Set (Fin n → ℝ)) ∧
      y - z ∈ (stdLattice n : Set (Fin n → ℝ)) ∧
      x - z ∈ (stdLattice n : Set (Fin n → ℝ)) := by
  obtain ⟨pts, hinj, hmem, hcong⟩ := blichfeldt_general 2 s h_meas (by exact_mod_cast h_vol)
  refine ⟨pts 0, pts 1, pts 2, hmem 0, hmem 1, hmem 2,
    ?_, ?_, ?_, hcong 0 1, hcong 1 2, hcong 0 2⟩
  · intro heq; exact absurd (hinj heq) (by decide)
  · intro heq; exact absurd (hinj heq) (by decide)
  · intro heq; exact absurd (hinj heq) (by decide)

/-- **Blichfeldt at k = 3**: a measurable set in ℝⁿ with volume > 3 contains
four pairwise-distinct points whose pairwise differences all lie in ℤⁿ.

The natural extension of `blichfeldt_three_points` (k = 2) one rung up the
corollary chain from `blichfeldt_general`. As at k = 2, no naive iteration
of the basic (k = 1) form would yield four points in a common ℤⁿ-coset —
the four-point case requires the full averaging (`volume_eq_setLIntegral_indicator_tsum`)
plus combinatorial extraction of `Fin (k+1) → L` developed in S13–S14.

Specialization of `blichfeldt_general` at k = 3; six pairwise-distinctness
goals (C(4,2) = 6) discharged uniformly by `Function.Injective` + `Fin.decide`. -/
theorem blichfeldt_four_points {n : ℕ} [NeZero n]
    (s : Set (Fin n → ℝ)) (h_meas : MeasurableSet s)
    (h_vol : (3 : ENNReal) < volume s) :
    ∃ w x y z : Fin n → ℝ,
      w ∈ s ∧ x ∈ s ∧ y ∈ s ∧ z ∈ s ∧
      w ≠ x ∧ w ≠ y ∧ w ≠ z ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      w - x ∈ (stdLattice n : Set (Fin n → ℝ)) ∧
      w - y ∈ (stdLattice n : Set (Fin n → ℝ)) ∧
      w - z ∈ (stdLattice n : Set (Fin n → ℝ)) ∧
      x - y ∈ (stdLattice n : Set (Fin n → ℝ)) ∧
      x - z ∈ (stdLattice n : Set (Fin n → ℝ)) ∧
      y - z ∈ (stdLattice n : Set (Fin n → ℝ)) := by
  obtain ⟨pts, hinj, hmem, hcong⟩ := blichfeldt_general 3 s h_meas (by exact_mod_cast h_vol)
  refine ⟨pts 0, pts 1, pts 2, pts 3,
    hmem 0, hmem 1, hmem 2, hmem 3,
    ?_, ?_, ?_, ?_, ?_, ?_,
    hcong 0 1, hcong 0 2, hcong 0 3, hcong 1 2, hcong 1 3, hcong 2 3⟩
  · intro heq; exact absurd (hinj heq) (by decide)
  · intro heq; exact absurd (hinj heq) (by decide)
  · intro heq; exact absurd (hinj heq) (by decide)
  · intro heq; exact absurd (hinj heq) (by decide)
  · intro heq; exact absurd (hinj heq) (by decide)
  · intro heq; exact absurd (hinj heq) (by decide)

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
    -- Mathlib 4.26: `ENNReal.mul_lt_mul_right` is a direct implication
    -- `(h0 : a ≠ 0) (hinf : a ≠ ⊤) (bc : b < c) : a * b < a * c` (not an Iff).
    have h_step : ((2 : ENNReal)⁻¹) ^ n * (2 : ENNReal) ^ n
                  < ((2 : ENNReal)⁻¹) ^ n * volume s :=
      ENNReal.mul_lt_mul_right h2_inv_ne_zero h2_inv_ne_top h_vol
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
#check BlichfeldtTheorem.blichfeldt_three_points
#check BlichfeldtTheorem.blichfeldt_four_points
#check BlichfeldtTheorem.minkowski_from_blichfeldt
