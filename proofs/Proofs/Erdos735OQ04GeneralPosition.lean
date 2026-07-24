/-
  Erdős Problem #735, Open Question #04 (oq-04) — S6e ACT:
  The general-position uniform-weight theorem for k-flat magic configurations.

  Parent: `Proofs.Erdos735OQ04` (k-flat magic configurations in ℝ^d).

  ## What this file proves

  The S6a tetrahedron witness (`Erdos735OQ04Tetrahedron.lean`) worked because a
  rank-2 flat cannot swallow four affinely independent points, so every 2-flat
  through ≥ 3 of them meets the configuration in *exactly* 3 points and the
  uniform weighting is magic with constant 3. This file abstracts that argument
  into the general theorem the S6 roadmap called the "general-position
  uniform-weight theorem", in three layers:

  * `IsKFlatGeneralPositionD k P` — no rank-`k` flat contains more than `k + 1`
    points of `P` (the `k`-flat analogue of the parent's `IsGeneralPositionD`,
    which is the case `k = 1` with bound `2`).
  * `isKFlatMagic_of_kFlatGeneralPosition` — **any** configuration in k-flat
    general position is k-flat magic, with uniform weight `1` and magic
    constant `k + 1`: each `ConfigKFlat` carries `≥ k+1` points by definition
    and `≤ k+1` by hypothesis, so every flat sum is exactly `k + 1`.
  * `kFlatGeneralPositionD_of_affineIndependent` — an affinely independent
    configuration is in k-flat general position for *every* `k`: any `k + 2`
    of its points span a flat of rank `≥ k + 1`, which cannot fit inside a
    rank-`k` flat (`AffineIndependent.finrank_vectorSpan` + rank monotonicity).

  Consequences:

  * `isKFlatMagic_of_affineIndependent` — every affinely independent
    configuration (simplex-type configuration) is k-flat magic for **every**
    `k` simultaneously. The S6a tetrahedron (`d = 3, k = 2`) becomes one
    instance of a uniform family: the higher-flat magic classes conjectured by
    this slug are *inhabited in every dimension and at every flat rank*.
  * `isKFlatMagic_one_of_generalPosition` — a configuration in the parent's
    1-flat general position (`IsGeneralPositionD`, class 2 of the conjectured
    four-class classification) is 1-flat magic — machine-checking the
    "general position ⟹ magic" implication of the S5 axiom
    `oneflat_classification_higher_dim` **unconditionally and in every
    dimension** (the axiom asserts the full four-class iff for `d ≥ 3`; this
    theorem proves one of its implications outright, shrinking the genuinely
    open content of the axiom).

  0 axioms, 0 sorries in this file (the slug's single S5 classification axiom
  lives in the parent and is untouched; nothing here depends on it).
-/

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Proofs.Erdos735OQ04

namespace Erdos735OQ04GenPos

open Erdos735OQ04
open scoped Classical

/-- **k-flat general position**: no rank-`k` affine subspace contains more than
`k + 1` points of `P`. For `k = 1` this is the bound form of the parent's
`IsGeneralPositionD` ("no three points on a common line"); for a `(d+1)`-point
affinely independent configuration it holds at every `k`
(`kFlatGeneralPositionD_of_affineIndependent`). -/
def IsKFlatGeneralPositionD {d : ℕ} (k : ℕ) (P : PointConfigD d) : Prop :=
  ∀ F : AffineSubspace ℝ (EuclideanSpace ℝ (Fin d)),
    Module.rank ℝ F.direction = (k : Cardinal) →
    (P.filter (· ∈ F)).card ≤ k + 1

/-- **The general-position uniform-weight theorem.** A configuration in k-flat
general position is k-flat magic: under the uniform weighting `w ≡ 1`, every
`k`-flat through `≥ k + 1` points contains *exactly* `k + 1` points (lower
bound from `ConfigKFlat`, upper bound from general position), so every flat sum
equals the magic constant `k + 1`. This abstracts the S6a tetrahedron argument
away from any concrete coordinates. -/
theorem isKFlatMagic_of_kFlatGeneralPosition {d k : ℕ} {P : PointConfigD d}
    (hgen : IsKFlatGeneralPositionD k P) : IsKFlatMagic k P := by
  refine ⟨⟨fun _ => (1 : ℝ), fun _ => zero_lt_one⟩, (k + 1 : ℕ), by positivity, ?_⟩
  intro Fcfg
  obtain ⟨F, hrk, hcard⟩ := Fcfg
  have hcardeq : (P.filter (· ∈ F)).card = k + 1 := le_antisymm (hgen F hrk) hcard
  show (P.filter (· ∈ F)).sum (fun p => if h : p ∈ P then (1 : ℝ) else 0) = _
  rw [Finset.sum_congr rfl fun p hp => dif_pos (Finset.mem_filter.mp hp).1,
    Finset.sum_const, Nat.smul_one_eq_cast, hcardeq]

/-- **Affinely independent configurations are in k-flat general position, for
every `k`.** If a rank-`k` flat contained `k + 2` points of `P`, those points —
being a subfamily of an affinely independent family — would span an affine
subspace whose direction has finrank `k + 1`, sitting inside a direction of
finrank `k`: contradiction. -/
theorem kFlatGeneralPositionD_of_affineIndependent {d k : ℕ} {P : PointConfigD d}
    (hP : AffineIndependent ℝ (fun p : ↥P => (p : EuclideanSpace ℝ (Fin d)))) :
    IsKFlatGeneralPositionD k P := by
  intro F hrk
  by_contra hgt
  have hge : k + 2 ≤ (P.filter (· ∈ F)).card := by omega
  obtain ⟨s, hs_sub, hs_card⟩ := Finset.exists_subset_card_eq hge
  have hsP : s ⊆ P := hs_sub.trans (Finset.filter_subset _ _)
  -- the points of `s`, as a subfamily of the affinely independent family on `P`
  have hs_ind : AffineIndependent ℝ (fun p : ↥s => (p : EuclideanSpace ℝ (Fin d))) := by
    have := hP.comp_embedding
      ⟨fun x : ↥s => (⟨x.1, hsP x.2⟩ : ↥P),
        fun x y hxy => Subtype.ext (Subtype.mk_eq_mk.mp hxy)⟩
    exact this
  -- their span has direction of finrank `k + 1` …
  have hfr : Module.finrank ℝ
      (vectorSpan ℝ (Set.range (fun p : ↥s => (p : EuclideanSpace ℝ (Fin d))))) = k + 1 :=
    hs_ind.finrank_vectorSpan (by simp [hs_card])
  -- … sitting inside `F.direction` …
  have hspan : affineSpan ℝ (Set.range (fun p : ↥s => (p : EuclideanSpace ℝ (Fin d)))) ≤ F := by
    rw [affineSpan_le]
    rintro x ⟨⟨p, hp⟩, rfl⟩
    exact (Finset.mem_filter.mp (hs_sub hp)).2
  have hdir : vectorSpan ℝ (Set.range (fun p : ↥s => (p : EuclideanSpace ℝ (Fin d)))) ≤
      F.direction := by
    rw [← direction_affineSpan]
    exact AffineSubspace.direction_le hspan
  -- … which has finrank `k`: contradiction.
  have hfrF : Module.finrank ℝ F.direction = k := by
    apply Module.finrank_eq_of_rank_eq (n := k)
    exact_mod_cast hrk
  have hmono := Submodule.finrank_mono hdir
  rw [hfr, hfrF] at hmono
  omega

/-- **Simplex-type configurations are universally flat-magic**: an affinely
independent configuration is k-flat magic for *every* `k`, with uniform weight
`1` and magic constant `k + 1`. The S6a tetrahedron (`d = 3, k = 2, c = 3`) is
the instance `P = tetraConfig`; this theorem shows the conjectured higher-flat
magic family is inhabited at every dimension and every flat rank. -/
theorem isKFlatMagic_of_affineIndependent {d k : ℕ} {P : PointConfigD d}
    (hP : AffineIndependent ℝ (fun p : ↥P => (p : EuclideanSpace ℝ (Fin d)))) :
    IsKFlatMagic k P :=
  isKFlatMagic_of_kFlatGeneralPosition (kFlatGeneralPositionD_of_affineIndependent hP)

/-- The parent's 1-flat general position (class 2 of the conjectured
classification, "no three points on a common line") implies 1-flat general
position in the bound form: any rank-1 flat with three points of `P` would
exhibit three distinct collinear points. -/
theorem kFlatGeneralPositionD_one_of_generalPosition {d : ℕ} {P : PointConfigD d}
    (h : IsGeneralPositionD P) : IsKFlatGeneralPositionD 1 P := by
  intro F hrk
  by_contra hgt
  have hge : 3 ≤ (P.filter (· ∈ F)).card := by omega
  obtain ⟨s, hs_sub, hs_card⟩ := Finset.exists_subset_card_eq hge
  obtain ⟨p, q, r, hpq, hpr, hqr, rfl⟩ := Finset.card_eq_three.mp hs_card
  have hp := hs_sub (by simp : p ∈ ({p, q, r} : Finset _))
  have hq := hs_sub (by simp : q ∈ ({p, q, r} : Finset _))
  have hr := hs_sub (by simp : r ∈ ({p, q, r} : Finset _))
  exact h p (Finset.mem_filter.mp hp).1 q (Finset.mem_filter.mp hq).1
    r (Finset.mem_filter.mp hr).1 hpq hqr hpr
    ⟨F, hrk, (Finset.mem_filter.mp hp).2, (Finset.mem_filter.mp hq).2,
      (Finset.mem_filter.mp hr).2⟩

/-- **The "general position ⟹ 1-flat magic" implication of the conjectured
higher-dimensional classification, machine-checked.** The S5 axiom
`oneflat_classification_higher_dim` asserts (for `d ≥ 3`) that 1-flat magic is
*equivalent* to membership in one of four classes; this theorem proves the
class-2 forward implication outright — in every dimension `d`, with no axiom —
shrinking the genuinely open content of the classification. -/
theorem isKFlatMagic_one_of_generalPosition {d : ℕ} {P : PointConfigD d}
    (h : IsGeneralPositionD P) : IsKFlatMagic 1 P :=
  isKFlatMagic_of_kFlatGeneralPosition (kFlatGeneralPositionD_one_of_generalPosition h)

end Erdos735OQ04GenPos
