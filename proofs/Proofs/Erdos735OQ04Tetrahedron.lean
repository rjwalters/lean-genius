/-
  Erdős Problem #735, Open Question #04 (oq-04) — S6a ACT:
  The regular tetrahedron is a 2-flat-magic configuration in ℝ³.

  Parent: `Proofs.Erdos735OQ04` (k-flat magic configurations in ℝ^d).

  This file ships a single concrete *existence* witness for the higher-flat
  (`k ≥ 2`) magic family conjectured in the parent slug: the regular
  tetrahedron at alternate cube vertices

      v₁ = ( 1,  1,  1),  v₂ = ( 1, -1, -1),
      v₃ = (-1,  1, -1),  v₄ = (-1, -1,  1)

  is `(k = 2)`-flat magic in `EuclideanSpace ℝ (Fin 3)` with magic constant 3
  under the uniform weighting `wᵢ = 1`.

  ## Proof architecture (affine-independence route)

  The S6a PREP (sessions/2026-05-13-s6a-prep-...) proposed enumerating the four
  triangular faces `F₁…F₄` and proving "no other minimal-spanning 2-flat". This
  file uses a cleaner route that avoids face enumeration entirely:

    * `tetra_affineIndependent` : the four vertices are affinely independent.
      Equivalently their `vectorSpan` is all of ℝ³ (`finrank = 3`).
    * For any `F : ConfigKFlat 2 tetraConfig`, the filtered point set has card
      `≥ 3` (config constraint) and `≤ 3` (a rank-2 flat cannot contain all four
      affinely independent vertices, else `finrank F.direction ≥ 3 > 2`). Hence
      card `= 3`, and the uniform-weight sum is `3 · 1 = 3`.

  The magic constant `c = 3` is exactly "k+1" — every minimal-spanning 2-flat in
  an affinely independent configuration meets it in exactly 3 points.

  ## Status (S6a COMPLETE — both proofs discharged, researcher-3, 2026-07-24)

  Both theorems are now fully proved (counts: 0 axioms, 0 sorries), completing
  the S6a milestone: the first machine-checked witness that the higher-flat
  (`k ≥ 2`) magic family is non-empty, confirming the class extends beyond the
  parent's four ABKPR plane classes.

    * `tetra_affineIndependent`: via `affineIndependent_iff_of_fintype` — a
      vanishing weighted combination gives, coordinate by coordinate, a linear
      system that together with `∑ wᵢ = 0` forces `w = 0` (`linarith`). This
      replaces the originally planned `affineIndependent_iff_linearIndependent_vsub`
      route (which needs an awkward subtype reindexing) with a direct
      weighted-sum argument.

    * `tetraConfig_isKFlatMagic`: witnesses `w ≡ 1`, `c = 3`. For
      `F : ConfigKFlat 2 tetraConfig` the filtered card is `≥ 3` (config
      constraint) and `≤ 3`: if all four vertices lay in `F` then
      `affineSpan ℝ (range tetraVertex) ≤ F`, so
      `vectorSpan ℝ (range tetraVertex) ≤ F.direction`; by
      `tetra_affineIndependent` + `AffineIndependent.finrank_vectorSpan`
      (`Fintype.card (Fin 4) = 3 + 1`) the left side has `finrank = 3`, forcing
      `finrank F.direction ≥ 3`, contradicting `Module.rank F.direction = 2`.
      Hence card `= 3` and the uniform-weight sum is `3`.
-/

import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Proofs.Erdos735OQ04

namespace Erdos735OQ04Tetra

open Erdos735OQ04
open scoped Classical

/-- The four vertices of a regular tetrahedron at alternate cube corners,
    as points of `EuclideanSpace ℝ (Fin 3)`. -/
noncomputable def tetraVertex : Fin 4 → EuclideanSpace ℝ (Fin 3)
  | 0 => !₂[ 1,  1,  1]
  | 1 => !₂[ 1, -1, -1]
  | 2 => !₂[-1,  1, -1]
  | 3 => !₂[-1, -1,  1]

/-- The tetrahedron as a `PointConfigD 3`. -/
noncomputable def tetraConfig : PointConfigD 3 :=
  Finset.image tetraVertex Finset.univ

/-- The four tetrahedron vertices are affinely independent (no plane contains
    all four). Proof: any vanishing affine combination `∑ wᵢ • vᵢ = 0` with
    `∑ wᵢ = 0` yields, coordinate by coordinate, the linear system

        w₀ + w₁ - w₂ - w₃ = 0,  w₀ - w₁ + w₂ - w₃ = 0,  w₀ - w₁ - w₂ + w₃ = 0

    which together with `w₀ + w₁ + w₂ + w₃ = 0` forces all `wᵢ = 0`. -/
theorem tetra_affineIndependent : AffineIndependent ℝ tetraVertex := by
  rw [affineIndependent_iff_of_fintype]
  intro w hw hvsub
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero (s := Finset.univ)
      w tetraVertex hw (0 : EuclideanSpace ℝ (Fin 3)),
    Finset.weightedVSubOfPoint_apply] at hvsub
  simp only [vsub_eq_sub, sub_zero, Fin.sum_univ_four] at hvsub
  rw [Fin.sum_univ_four] at hw
  have e0 : tetraVertex 0 = !₂[1, 1, 1] := rfl
  have e1 : tetraVertex 1 = !₂[1, -1, -1] := rfl
  have e2 : tetraVertex 2 = !₂[-1, 1, -1] := rfl
  have e3 : tetraVertex 3 = !₂[-1, -1, 1] := rfl
  rw [e0, e1, e2, e3] at hvsub
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => WithLp.ofLp v 0) hvsub
  have h1 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => WithLp.ofLp v 1) hvsub
  have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => WithLp.ofLp v 2) hvsub
  simp only [WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_zero,
    Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h0 h1 h2
  have hw0 : w 0 = 0 := by linarith
  have hw1 : w 1 = 0 := by linarith
  have hw2 : w 2 = 0 := by linarith
  have hw3 : w 3 = 0 := by linarith
  intro i
  fin_cases i
  · exact hw0
  · exact hw1
  · exact hw2
  · exact hw3

/-- The regular tetrahedron is `(k = 2)`-flat magic in ℝ³ with magic constant 3
    under the uniform weighting.

    Proof (affine-independence route, no face enumeration): for any
    `F : ConfigKFlat 2 tetraConfig` the filtered point set has card `≥ 3` (the
    config constraint) and `≤ 3` — if all four vertices lay in `F` then
    `vectorSpan ℝ (range tetraVertex) ≤ F.direction`, and by
    `tetra_affineIndependent` the left side has `finrank = 3`, contradicting
    `Module.rank ℝ F.direction = 2`.  Hence exactly 3 points, and the
    uniform-weight sum is `3`. -/
theorem tetraConfig_isKFlatMagic : IsKFlatMagic 2 tetraConfig := by
  refine ⟨⟨fun _ => (1 : ℝ), fun _ => zero_lt_one⟩, 3, by norm_num, ?_⟩
  intro Fcfg
  obtain ⟨F, hrk, hcard⟩ := Fcfg
  have hinj : Function.Injective tetraVertex := tetra_affineIndependent.injective
  have hcard4 : tetraConfig.card = 4 := by
    simp only [tetraConfig]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hle3 : (tetraConfig.filter (· ∈ F)).card ≤ 3 := by
    by_contra hgt
    have hfeq : tetraConfig.filter (· ∈ F) = tetraConfig :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
    have hallF : ∀ i, tetraVertex i ∈ F := by
      intro i
      have hmem : tetraVertex i ∈ tetraConfig.filter (· ∈ F) := by
        rw [hfeq]
        simp only [tetraConfig]
        exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
      exact (Finset.mem_filter.mp hmem).2
    have hspan : affineSpan ℝ (Set.range tetraVertex) ≤ F := by
      rw [affineSpan_le]
      rintro x ⟨i, rfl⟩
      exact hallF i
    have hdir : vectorSpan ℝ (Set.range tetraVertex) ≤ F.direction := by
      rw [← direction_affineSpan]
      exact AffineSubspace.direction_le hspan
    have hfr3 : Module.finrank ℝ (vectorSpan ℝ (Set.range tetraVertex)) = 3 :=
      tetra_affineIndependent.finrank_vectorSpan (by simp)
    have hfrF : Module.finrank ℝ F.direction = 2 := by
      apply Module.finrank_eq_of_rank_eq (n := 2)
      exact_mod_cast hrk
    have hmono := Submodule.finrank_mono hdir
    rw [hfr3, hfrF] at hmono
    omega
  have hcard3 : (tetraConfig.filter (· ∈ F)).card = 3 := le_antisymm hle3 hcard
  show (tetraConfig.filter (· ∈ F)).sum
      (fun p => if h : p ∈ tetraConfig then (1 : ℝ) else 0) = 3
  rw [Finset.sum_congr rfl fun p hp => dif_pos (Finset.mem_filter.mp hp).1,
    Finset.sum_const, Nat.smul_one_eq_cast, hcard3]
  norm_num

end Erdos735OQ04Tetra
