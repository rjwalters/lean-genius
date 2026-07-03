/-
# van der Corput's Convex-Body Counting Theorem
(minkowski-fundamental-theorem-oq-03-oq-01)

The general-`k` (van der Corput) refinement of Minkowski's fundamental theorem:
a convex, centrally symmetric body whose volume exceeds `k · 2ⁿ · covol(L)`
contains not just one nonzero lattice point (Minkowski, `k = 1`) but at least
`k` of them.

## Statement

Let `L ⊆ E` be a full-rank lattice with fundamental domain `F`, and let `s` be a
convex, centrally symmetric, null-measurable body.  If

  `k · (covol(L) · 2ⁿ) < vol(s)`

then `s` contains at least `k` nonzero lattice points: a finite set `D ⊆ L` with
`k ≤ #D`, `0 ∉ D`, and `(v : E) ∈ s` for every `v ∈ D`.  By central symmetry the
negatives `-v` also lie in `s`, so the points come in `± pairs` — this is the
"`k` pairs / `k+1` points counting the origin" normalization of van der Corput's
theorem.  Minkowski's fundamental theorem is `k = 1`.

## Proof

The measure-theoretic core — general-multiplicity Blichfeldt — is already
formalized in the parent entry `minkowski-fundamental-theorem-oq-03` as
`MeasureTheory.exists_finset_lattice_common_vadd`.  This file supplies the
*geometric* passage from that multiplicity input to lattice points of the convex
body, exactly as in Mathlib's own `k = 1` Minkowski proof but carrying the whole
over-covered family:

* Apply Blichfeldt to the shrunk body `½·s`, whose volume `2⁻ⁿ · vol(s)` still
  exceeds `k · covol(L)`.  It yields a finite `T ⊆ L` with `k < #T` and a common
  point `z` with `z ∈ l +ᵥ ½s` for all `l ∈ T`, i.e. `2·(z - l) ∈ s`.
* Fix `l₀ ∈ T`.  For each other `l ∈ T`, the difference of the two `½s`-points
  passes through convexity and central symmetry to a genuine lattice point:
  `(l - l₀ : E) = 2⁻¹ · (2·(z - l₀) - 2·(z - l)) ∈ s`
  (`half_diff_mem_of_symmetric_convex`).
* The map `l ↦ l - l₀` is injective and avoids `0` off `l₀`, so the `#T - 1 ≥ k`
  images form the required family of nonzero lattice points in `s`.

The reusable geometric lemma `half_diff_mem_of_symmetric_convex`
("for convex symmetric `s`, `a, b ∈ s ⟹ ½(a - b) ∈ s`") is the "congruent points
→ genuine lattice point" step the problem statement asks to be packaged.

All results are `0` axioms (`propext` / `Classical.choice` / `Quot.sound` only;
no `sorry`, no `decide`, no `native_decide`).
-/
import Mathlib
import Proofs.MinkowskiFundamentalTheoremOQ03

open MeasureTheory Module Set Filter
open scoped Pointwise ENNReal

namespace MinkowskiVanDerCorput

/-- **The central-symmetry / convexity passage lemma.**  For a convex, centrally
symmetric set `s`, the scaled difference of any two of its points stays in `s`:
`a, b ∈ s ⟹ 2⁻¹ • (a - b) ∈ s`.  This is the "two congruent points give a genuine
lattice point" step of the geometry of numbers, packaged abstractly. -/
theorem half_diff_mem_of_symmetric_convex {E : Type*} [AddCommGroup E] [Module ℝ E]
    {s : Set E} (hconv : Convex ℝ s) (hsymm : ∀ x ∈ s, -x ∈ s)
    {a b : E} (ha : a ∈ s) (hb : b ∈ s) :
    (2⁻¹ : ℝ) • (a - b) ∈ s := by
  have hnb : -b ∈ s := hsymm b hb
  have hmix := hconv ha hnb (by norm_num : (0:ℝ) ≤ 2⁻¹) (by norm_num : (0:ℝ) ≤ 2⁻¹)
    (by norm_num : (2⁻¹:ℝ) + 2⁻¹ = 1)
  simpa [smul_sub, smul_neg, sub_eq_add_neg] using hmix

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {F s : Set E} {L : AddSubgroup E} [Countable L]

/-- Volume of the half-scaled body: `vol(½s) = (2ⁿ)⁻¹ · vol(s)`. -/
theorem measure_half_smul :
    μ ((2⁻¹ : ℝ) • s) = (2 ^ finrank ℝ E)⁻¹ * μ s := by
  rw [Measure.addHaar_smul_of_nonneg μ (by norm_num : (0:ℝ) ≤ 2⁻¹) s,
      ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2⁻¹),
      ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ) < 2),
      ENNReal.ofReal_ofNat, ← ENNReal.inv_pow]

/-- **van der Corput's convex-body counting theorem.**  A convex, centrally
symmetric body `s` with `vol(s) > k · covol(L) · 2ⁿ` contains at least `k` nonzero
lattice points: a finite `D ⊆ L` with `k ≤ #D`, `0 ∉ D`, and `(v : E) ∈ s` for all
`v ∈ D`.  Minkowski's fundamental theorem is the case `k = 1`. -/
theorem vanDerCorput
    (fund : IsAddFundamentalDomain L F μ)
    (hs : NullMeasurableSet s μ)
    (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s)
    {k : ℕ} (h : k • (μ F * 2 ^ finrank ℝ E) < μ s) :
    ∃ D : Finset L, k ≤ D.card ∧ (0 : L) ∉ D ∧ ∀ v ∈ D, ((v : E) ∈ s) := by
  classical
  have hpow_ne : (2 : ℝ≥0∞) ^ finrank ℝ E ≠ 0 := by positivity
  have hpow_top : (2 : ℝ≥0∞) ^ finrank ℝ E ≠ ⊤ := by finiteness
  -- The half-body still has more than `k` copies of the covolume.
  have h_vol : (k : ℕ) • μ F < μ ((2⁻¹ : ℝ) • s) := by
    have hR : ((2 ^ finrank ℝ E)⁻¹ * μ s) * 2 ^ finrank ℝ E = μ s := by
      rw [mul_right_comm, ENNReal.inv_mul_cancel hpow_ne hpow_top, one_mul]
    have hL : ((k : ℕ) • μ F) * 2 ^ finrank ℝ E = k • (μ F * 2 ^ finrank ℝ E) := by
      rw [nsmul_eq_mul, nsmul_eq_mul]; ring
    have hmul : ((k : ℕ) • μ F) * 2 ^ finrank ℝ E
              < μ ((2⁻¹ : ℝ) • s) * 2 ^ finrank ℝ E := by
      rw [measure_half_smul, hR, hL]; exact h
    exact (ENNReal.mul_lt_mul_iff_left hpow_ne hpow_top).mp hmul
  -- Blichfeldt's general-multiplicity principle on `½s`.
  obtain ⟨T, hTcard, z, hz⟩ :=
    MeasureTheory.exists_finset_lattice_common_vadd fund
      ((h_conv.smul (2⁻¹ : ℝ)).nullMeasurableSet μ) h_vol
  -- `T` is nonempty; fix a base point `l₀`.
  obtain ⟨l₀, hl₀⟩ := Finset.card_pos.mp (by omega : 0 < T.card)
  -- From each `l ∈ T`: `2 • (z - l) ∈ s`.
  have extract : ∀ l ∈ T, (2 : ℝ) • (z - (l : E)) ∈ s := by
    intro l hlT
    have hmem := hz l hlT
    rw [Set.mem_vadd_set_iff_neg_vadd_mem,
        Set.mem_inv_smul_set_iff₀ (by norm_num : (2:ℝ) ≠ 0)] at hmem
    simpa [AddSubgroup.vadd_def, neg_add_eq_sub, sub_eq_add_neg, add_comm] using hmem
  -- The family of nonzero lattice differences.
  refine ⟨(T.erase l₀).image (fun l => l - l₀), ?_, ?_, ?_⟩
  · -- cardinality `≥ k`
    rw [Finset.card_image_of_injective _ (fun a b hab => by simpa using sub_left_injective hab),
        Finset.card_erase_of_mem hl₀]
    omega
  · -- `0` is not a difference (that would force `l = l₀`)
    intro h0
    rw [Finset.mem_image] at h0
    obtain ⟨l, hl, hleq⟩ := h0
    rw [Finset.mem_erase] at hl
    exact hl.1 (sub_eq_zero.mp hleq)
  · -- each difference is a lattice point of `s`
    intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨l, hl, rfl⟩ := hv
    rw [Finset.mem_erase] at hl
    have h1 := extract l₀ hl₀
    have h2 := extract l hl.2
    have hcoe : ((l - l₀ : L) : E)
        = (2⁻¹ : ℝ) • ((2 : ℝ) • (z - (l₀ : E)) - (2 : ℝ) • (z - (l : E))) := by
      rw [AddSubgroup.coe_sub]; module
    rw [hcoe]
    exact half_diff_mem_of_symmetric_convex h_conv h_symm h1 h2

/-- **Minkowski's fundamental theorem as `k = 1`.**  A convex symmetric body of
volume `> covol(L) · 2ⁿ` contains a nonzero lattice point (with its antipode). -/
theorem minkowski_of_vanDerCorput
    (fund : IsAddFundamentalDomain L F μ)
    (hs : NullMeasurableSet s μ)
    (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s)
    (h : μ F * 2 ^ finrank ℝ E < μ s) :
    ∃ v : L, v ≠ 0 ∧ ((v : E) ∈ s) ∧ ((-v : E) ∈ s) := by
  obtain ⟨D, hcard, hzero, hmem⟩ := vanDerCorput fund hs h_symm h_conv
    (k := 1) (by simpa using h)
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (by omega : 0 < D.card)
  refine ⟨v, ?_, hmem v hv, ?_⟩
  · rintro rfl; exact hzero hv
  · have := hmem v hv
    simpa using h_symm _ this

#check @half_diff_mem_of_symmetric_convex
#check @vanDerCorput
#check @minkowski_of_vanDerCorput

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`, no `decide`.
#print axioms vanDerCorput
#print axioms minkowski_of_vanDerCorput

end MinkowskiVanDerCorput
