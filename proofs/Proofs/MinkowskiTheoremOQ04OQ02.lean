import Mathlib.Algebra.Module.ZLattice.Covolume
import Proofs.MinkowskiTheoremOQ04
import Mathlib.Tactic

/-
# Blichfeldt & Minkowski for an arbitrary full-rank lattice — covolume threshold

Child of `minkowski-theorem-oq-04` (`Proofs/MinkowskiTheoremOQ04.lean`).

The parent already proves, verified and axiom-free, the lattice-parametric Blichfeldt
pigeonhole `BlichfeldtTheorem.blichfeldt_general_lattice`: for a basis
`b : Module.Basis (Fin n) ℝ (Fin n → ℝ)` and a measurable `s` with
`(k : ℝ≥0∞) * volume (ZSpan.fundamentalDomain b) < volume s`, there are `k + 1`
distinct points of `s` whose pairwise differences lie in `Submodule.span ℤ (Set.range b)`.

What the parent does *not* provide, and what this child adds, is the geometry-of-numbers
**covolume-threshold** form — the statement as it appears in Cassels / Siegel, phrased with
`ZLattice.covolume` (a real number, `= (volume of a fundamental domain).toReal`) rather than
the raw `ℝ≥0∞`-valued `volume (ZSpan.fundamentalDomain b)`. This is the shape used in
essentially every number-theoretic application (Diophantine approximation, ideal-lattice
bounds via the Minkowski embedding, whose covolume is `2^{-r₂}√|d_K|`).

## Main results

* `covolume_eq_toReal_volume_fundamentalDomain` — the bridge
  `ZLattice.covolume (span ℤ (range b)) volume = (volume (ZSpan.fundamentalDomain b)).toReal`.
* `blichfeldt_general_lattice_covolume` — Blichfeldt with threshold
  `ENNReal.ofReal (k · covol(Λ)) < volume s`.
* `blichfeldt_basic_lattice`, `blichfeldt_basic_lattice_covolume` — the `k = 1` corollaries.
* `minkowski_lattice` — Minkowski's convex-body theorem for an arbitrary full-rank lattice:
  a measurable, convex, centrally-symmetric `s` with
  `2ⁿ · volume (ZSpan.fundamentalDomain b) < volume s` contains a nonzero lattice point.
* `minkowski_lattice_covolume` — the same with the covolume threshold
  `ENNReal.ofReal (2ⁿ · covol(Λ)) < volume s`.

All results are reduced to the parent's verified engine plus the Mathlib `ZLattice.covolume`
API; no new axioms are introduced.

References: Blichfeldt (1914); Cassels, *Geometry of Numbers*, Ch. III;
Siegel, *Lectures on the Geometry of Numbers*.
-/

open MeasureTheory Set Pointwise

namespace BlichfeldtTheorem

variable {n : ℕ} [NeZero n]

omit [NeZero n] in
/-- The volume of a lattice fundamental domain is finite (it is a bounded set). -/
theorem volume_fundamentalDomain_ne_top (b : Module.Basis (Fin n) ℝ (Fin n → ℝ)) :
    volume (ZSpan.fundamentalDomain b) ≠ ⊤ :=
  (Bornology.IsBounded.measure_lt_top (ZSpan.fundamentalDomain_isBounded b)).ne

omit [NeZero n] in
/-- **Covolume bridge.** For the lattice `Λ = span ℤ (range b)`, the real-valued
`ZLattice.covolume` is exactly the `toReal` of the (`ℝ≥0∞`-valued) volume of the
half-open fundamental parallelepiped `ZSpan.fundamentalDomain b`. -/
theorem covolume_eq_toReal_volume_fundamentalDomain
    (b : Module.Basis (Fin n) ℝ (Fin n → ℝ)) :
    ZLattice.covolume (Submodule.span ℤ (Set.range b)) volume
      = (volume (ZSpan.fundamentalDomain b)).toReal := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume
        (ZSpan.isAddFundamentalDomain b volume), measureReal_def]

omit [NeZero n] in
/-- `(k : ℝ≥0∞) · volume F = ENNReal.ofReal (k · covol Λ)`, the arithmetic bridge that
turns the parent's `ℝ≥0∞`-threshold into the covolume threshold. -/
theorem natCast_mul_volume_fundamentalDomain
    (b : Module.Basis (Fin n) ℝ (Fin n → ℝ)) (k : ℕ) :
    (k : ENNReal) * volume (ZSpan.fundamentalDomain b)
      = ENNReal.ofReal ((k : ℝ) * ZLattice.covolume (Submodule.span ℤ (Set.range b)) volume) := by
  rw [covolume_eq_toReal_volume_fundamentalDomain, ENNReal.ofReal_mul (Nat.cast_nonneg k),
      ENNReal.ofReal_natCast, ENNReal.ofReal_toReal (volume_fundamentalDomain_ne_top b)]

/-- **Blichfeldt's theorem for an arbitrary full-rank lattice, covolume form.**

For a basis `b` (hence lattice `Λ = span ℤ (range b)`) and measurable `s` with
`vol(S) > k · covol(Λ)`, there exist `k + 1` distinct points of `S` whose pairwise
differences all lie in `Λ`. Covolume restatement of the parent's
`blichfeldt_general_lattice`. -/
theorem blichfeldt_general_lattice_covolume
    (b : Module.Basis (Fin n) ℝ (Fin n → ℝ)) (k : ℕ) (s : Set (Fin n → ℝ))
    (h_meas : MeasurableSet s)
    (h_vol : ENNReal.ofReal ((k : ℝ) * ZLattice.covolume (Submodule.span ℤ (Set.range b)) volume)
              < volume s) :
    ∃ pts : Fin (k + 1) → Fin n → ℝ,
      Function.Injective pts ∧ (∀ i, pts i ∈ s) ∧
      ∀ i j, pts i - pts j ∈
        (Submodule.span ℤ (Set.range b) : Set (Fin n → ℝ)) := by
  refine blichfeldt_general_lattice b k s h_meas ?_
  rw [natCast_mul_volume_fundamentalDomain]
  exact h_vol

/-- **Blichfeldt at `k = 1` for an arbitrary lattice** (fundamental-domain-volume form):
a measurable `s` with `volume s > volume (ZSpan.fundamentalDomain b)` contains two distinct
points differing by a lattice vector. -/
theorem blichfeldt_basic_lattice
    (b : Module.Basis (Fin n) ℝ (Fin n → ℝ)) (s : Set (Fin n → ℝ))
    (h_meas : MeasurableSet s)
    (h_vol : volume (ZSpan.fundamentalDomain b) < volume s) :
    ∃ x y : Fin n → ℝ, x ∈ s ∧ y ∈ s ∧ x ≠ y ∧
      x - y ∈ (Submodule.span ℤ (Set.range b) : Set (Fin n → ℝ)) := by
  obtain ⟨pts, hinj, hmem, hcong⟩ :=
    blichfeldt_general_lattice b 1 s h_meas (by rw [Nat.cast_one, one_mul]; exact h_vol)
  exact ⟨pts 0, pts 1, hmem 0, hmem 1, fun heq => absurd (hinj heq) (by decide), hcong 0 1⟩

/-- **Blichfeldt at `k = 1` for an arbitrary lattice**, covolume form:
`volume s > covol(Λ)` forces a lattice-related pair. -/
theorem blichfeldt_basic_lattice_covolume
    (b : Module.Basis (Fin n) ℝ (Fin n → ℝ)) (s : Set (Fin n → ℝ))
    (h_meas : MeasurableSet s)
    (h_vol : ENNReal.ofReal (ZLattice.covolume (Submodule.span ℤ (Set.range b)) volume)
              < volume s) :
    ∃ x y : Fin n → ℝ, x ∈ s ∧ y ∈ s ∧ x ≠ y ∧
      x - y ∈ (Submodule.span ℤ (Set.range b) : Set (Fin n → ℝ)) := by
  refine blichfeldt_basic_lattice b s h_meas ?_
  have h1 : ENNReal.ofReal (ZLattice.covolume (Submodule.span ℤ (Set.range b)) volume)
      = volume (ZSpan.fundamentalDomain b) := by
    rw [covolume_eq_toReal_volume_fundamentalDomain,
        ENNReal.ofReal_toReal (volume_fundamentalDomain_ne_top b)]
  rwa [h1] at h_vol

/-- **Minkowski's convex-body theorem for an arbitrary full-rank lattice.**

A measurable, convex, centrally-symmetric set `s ⊆ ℝⁿ` with
`volume s > 2ⁿ · volume (ZSpan.fundamentalDomain b)` contains a nonzero point of the
lattice `Λ = span ℤ (range b)`.

Half-scaling reduces it to `blichfeldt_basic_lattice` on `T = (1/2) • s`, exactly mirroring
the parent's `minkowski_from_blichfeldt` with the constant `1` (= covolume of `ℤⁿ`) replaced
by `volume (ZSpan.fundamentalDomain b)`. -/
theorem minkowski_lattice
    (b : Module.Basis (Fin n) ℝ (Fin n → ℝ)) (s : Set (Fin n → ℝ))
    (h_meas : MeasurableSet s) (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s)
    (h_vol : (2 : ENNReal) ^ n * volume (ZSpan.fundamentalDomain b) < volume s) :
    ∃ p : (Submodule.span ℤ (Set.range b)).toAddSubgroup, p ≠ 0 ∧ (p : Fin n → ℝ) ∈ s := by
  let T := (fun x : Fin n → ℝ => (2 : ℝ)⁻¹ • x) '' s
  have h_T_eq : T = (2 : ℝ)⁻¹ • s := rfl
  have h2_ne : (2 : ℝ) ≠ 0 := by norm_num
  -- Measurability of `T` (same argument as `minkowski_from_blichfeldt`).
  have h_meas_T : MeasurableSet T := by
    have h_pre : (2 : ℝ)⁻¹ • s = ((2 : ℝ) • · : (Fin n → ℝ) → (Fin n → ℝ)) ⁻¹' s := by
      ext y
      simp only [Set.mem_smul_set, Set.mem_preimage]
      refine ⟨?_, ?_⟩
      · rintro ⟨a, has, rfl⟩
        rwa [smul_smul, mul_inv_cancel₀ h2_ne, one_smul]
      · intro h
        exact ⟨(2 : ℝ) • y, h, by rw [smul_smul, inv_mul_cancel₀ h2_ne, one_smul]⟩
    rw [h_T_eq, h_pre]
    exact h_meas.preimage (measurable_const_smul (2 : ℝ))
  -- Volume identity: `vol T = (1/2)ⁿ · vol s > vol F` since `vol s > 2ⁿ · vol F`.
  have h_vol_T : volume (ZSpan.fundamentalDomain b) < volume T := by
    rw [h_T_eq, MeasureTheory.Measure.addHaar_smul volume ((2 : ℝ)⁻¹) s,
        Module.finrank_fin_fun, abs_pow, ENNReal.ofReal_pow (abs_nonneg _)]
    rw [show |((2 : ℝ)⁻¹)| = (2 : ℝ)⁻¹ by norm_num]
    have h_ofReal : ENNReal.ofReal ((2 : ℝ)⁻¹) = (2 : ENNReal)⁻¹ := by
      rw [show ((2 : ℝ)⁻¹) = 1 / 2 by ring,
          ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
      simp
    rw [h_ofReal]
    have h2iz : (2 : ENNReal)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (by norm_num)
    have h2it : (2 : ENNReal)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by norm_num)
    have hz : ((2 : ENNReal)⁻¹) ^ n ≠ 0 := pow_ne_zero _ h2iz
    have ht : ((2 : ENNReal)⁻¹) ^ n ≠ ⊤ := by
      intro hc; rw [ENNReal.pow_eq_top_iff] at hc; exact h2it hc.1
    have h_step := ENNReal.mul_lt_mul_right hz ht h_vol
    have h_eq_one : ((2 : ENNReal)⁻¹) ^ n * (2 : ENNReal) ^ n = 1 := by
      rw [← mul_pow,
          ENNReal.inv_mul_cancel (by norm_num : (2 : ENNReal) ≠ 0)
            (by norm_num : (2 : ENNReal) ≠ ⊤), one_pow]
    rw [← mul_assoc, h_eq_one, one_mul] at h_step
    exact h_step
  obtain ⟨a, c, haT, hcT, hac_ne, hac_diff⟩ := blichfeldt_basic_lattice b T h_meas_T h_vol_T
  obtain ⟨x₀, hx₀s, rfl⟩ := haT
  obtain ⟨y₀, hy₀s, rfl⟩ := hcT
  have hp_in_s : (2 : ℝ)⁻¹ • x₀ - (2 : ℝ)⁻¹ • y₀ ∈ s := by
    have key : (2 : ℝ)⁻¹ • x₀ + (2 : ℝ)⁻¹ • (-y₀) ∈ s :=
      h_conv hx₀s (h_symm y₀ hy₀s) (by norm_num) (by norm_num) (by norm_num)
    rwa [smul_neg, ← sub_eq_add_neg] at key
  -- `x ∈ (N : Set _)` and `x ∈ N.toAddSubgroup` are definitionally equal
  -- (`Submodule.mem_toAddSubgroup` is `Iff.rfl`), so `hac_diff` transfers directly.
  have hp_mem : (2 : ℝ)⁻¹ • x₀ - (2 : ℝ)⁻¹ • y₀
      ∈ (Submodule.span ℤ (Set.range b)).toAddSubgroup :=
    hac_diff
  exact ⟨⟨_, hp_mem⟩, fun h => (sub_ne_zero.mpr hac_ne) (congrArg Subtype.val h), hp_in_s⟩

/-- **Minkowski's convex-body theorem for an arbitrary lattice**, covolume form:
a measurable convex centrally-symmetric `s` with `volume s > 2ⁿ · covol(Λ)` contains a
nonzero lattice point. This is the classical geometry-of-numbers statement (Cassels III.2). -/
theorem minkowski_lattice_covolume
    (b : Module.Basis (Fin n) ℝ (Fin n → ℝ)) (s : Set (Fin n → ℝ))
    (h_meas : MeasurableSet s) (h_symm : ∀ x ∈ s, -x ∈ s) (h_conv : Convex ℝ s)
    (h_vol : ENNReal.ofReal
        ((2 : ℝ) ^ n * ZLattice.covolume (Submodule.span ℤ (Set.range b)) volume)
              < volume s) :
    ∃ p : (Submodule.span ℤ (Set.range b)).toAddSubgroup, p ≠ 0 ∧ (p : Fin n → ℝ) ∈ s := by
  refine minkowski_lattice b s h_meas h_symm h_conv ?_
  have hbridge : (2 : ENNReal) ^ n * volume (ZSpan.fundamentalDomain b)
      = ENNReal.ofReal
          ((2 : ℝ) ^ n * ZLattice.covolume (Submodule.span ℤ (Set.range b)) volume) := by
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ n),
        ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
        covolume_eq_toReal_volume_fundamentalDomain,
        ENNReal.ofReal_toReal (volume_fundamentalDomain_ne_top b)]
    norm_num
  rw [hbridge]
  exact h_vol

end BlichfeldtTheorem
