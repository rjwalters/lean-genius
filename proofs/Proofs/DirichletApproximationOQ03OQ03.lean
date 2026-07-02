/-
  Volume of a Parallelogram = |det| · (box volume)
  (research problem: dirichlet-approximation-theorem-oq-03-oq-03)

  The parent entry `dirichlet-approximation-theorem-oq-03` re-derives Dirichlet's
  approximation theorem from Minkowski's convex-body theorem, but leaves ONE step
  open: the volume computation `volume (body α N) = 4`.  Its docstring records the
  intended route — the body `K(α,N)` is the image of a box under a shear of
  determinant `-1`, so its area is `|det| · (box area) = 1 · 4 = 4` by
  `MeasureTheory.Measure.addHaar_image_linearMap`.

  This file packages that "determinant–shear volume" technique as the reusable lemma
  requested by the parent's third open question:

      volume of a parallelogram = |det| · (box volume),   in every dimension.

  Everything here is sorry-free and axiom-free (`import Mathlib` only).

  ## What is established

  * `volume_toLin'_image_Icc`
      — **the reusable core**: for a matrix `M : Matrix (Fin n) (Fin n) ℝ` and a box
        `[a, b] ⊆ ℝⁿ`, the image `M · [a,b]` has volume `|det M| · ∏ (bᵢ − aᵢ)`.
        This is the general-dimension "volume of a parallelepiped = |det| · box".
  * `volume_unitCube`
      — the unit cube `[0,1]ⁿ` has volume `1`.
  * `volume_parallelepiped`
      — Mathlib's fundamental parallelepiped `parallelepiped v` (spanned by the rows
        `v : Fin n → (Fin n → ℝ)`) has volume `|det|` of the matrix of coordinates.
        This gives the *concrete* `volume`/`Matrix.det` statement that Mathlib's
        abstract `addHaar_parallelepiped` (phrased with `Basis.addHaar`/`Basis.det`)
        does not directly provide.
  * `volume_parallelogram_2d`
      — the concrete 2-D specialisation: the parallelogram spanned by `(a,b)` and
        `(c,d)` has area `|a·d − b·c|`.
  * `volume_dirichlet_body`
      — **closes the parent's open volume step**: the shear image of the box
        `[−N,N] × [−1/N, 1/N]` under `(x,y) ↦ (x, α·x − y)` has volume exactly `4`,
        independent of `α` and of `N > 0`.  This is precisely the `2² · covolume(ℤ²)`
        area that Minkowski's theorem consumes in the parent derivation.

  ## Relation to Mathlib

  Mathlib provides `MeasureTheory.Measure.addHaar_image_linearMap`
  (`μ (f '' s) = ofReal |det f| · μ s`) and `addHaar_parallelepiped`
  (`b.addHaar (parallelepiped v) = ofReal |b.det v|`).  The contribution here is to
  specialise these to the Lebesgue `volume` on `Fin n → ℝ` with the *matrix*
  determinant `Matrix.det` and to concrete boxes, yielding lemmas directly usable in
  geometry-of-numbers arguments (Minkowski's linear-forms theorem) without unfolding
  the `Basis.addHaar`/`Basis.det` machinery each time.
-/
import Mathlib

namespace ParallelepipedVolume

open MeasureTheory Matrix Set

variable {n : ℕ}

/-- **Reusable core lemma** ("volume of a parallelogram = |det| · box volume").
    The image of a box `[a, b] ⊆ ℝⁿ` under the linear map of a matrix `M` has volume
    `|det M|` times the volume of the box. -/
theorem volume_toLin'_image_Icc (M : Matrix (Fin n) (Fin n) ℝ) (a b : Fin n → ℝ) :
    volume (Matrix.toLin' M '' Set.Icc a b)
      = ENNReal.ofReal |M.det| * ∏ i, ENNReal.ofReal (b i - a i) := by
  rw [volume.addHaar_image_linearMap (Matrix.toLin' M) (Set.Icc a b),
      LinearMap.det_toLin', Real.volume_Icc_pi]

/-- The unit cube `[0,1]ⁿ` has Lebesgue volume `1`. -/
theorem volume_unitCube : volume (Set.Icc (0 : Fin n → ℝ) 1) = 1 := by
  rw [Real.volume_Icc_pi]
  simp

/-- The linear map `t ↦ ∑ i, tᵢ • vᵢ` defining `parallelepiped v` is `Matrix.toLin'`
    of the matrix whose columns are the vectors `vᵢ`. -/
theorem parallelepiped_eq_toLin'_image (v : Fin n → (Fin n → ℝ)) :
    parallelepiped v = Matrix.toLin' (Matrix.of fun i j => v j i) '' Set.Icc 0 1 := by
  have hfun :
      (fun t : Fin n → ℝ => ∑ i, t i • v i)
        = Matrix.toLin' (Matrix.of fun i j => v j i) := by
    ext t k
    simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.of_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  show (fun t : Fin n → ℝ => ∑ i, t i • v i) '' Set.Icc 0 1
      = Matrix.toLin' (Matrix.of fun i j => v j i) '' Set.Icc 0 1
  rw [hfun]

/-- **Concrete parallelepiped volume.** The fundamental parallelepiped spanned by the
    vectors `v : Fin n → (Fin n → ℝ)` has volume `|det|` of the coordinate matrix. -/
theorem volume_parallelepiped (v : Fin n → (Fin n → ℝ)) :
    volume (parallelepiped v) = ENNReal.ofReal |(Matrix.of fun i j => v j i).det| := by
  rw [parallelepiped_eq_toLin'_image,
      volume.addHaar_image_linearMap (Matrix.toLin' (Matrix.of fun i j => v j i)) (Set.Icc 0 1),
      LinearMap.det_toLin', volume_unitCube, mul_one]

/-- **2-D specialisation.** The parallelogram spanned by `(a,b)` and `(c,d)` has area
    `|a·d − b·c|`. -/
theorem volume_parallelogram_2d (a b c d : ℝ) :
    volume (parallelepiped ![![a, b], ![c, d]]) = ENNReal.ofReal |a * d - b * c| := by
  have hdet :
      (Matrix.of fun i j => (![![a, b], ![c, d]] : Fin 2 → Fin 2 → ℝ) j i).det
        = a * d - b * c := by
    rw [Matrix.det_fin_two]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  rw [volume_parallelepiped, hdet]

/-- **Closes the parent's open volume step.** The shear image of the box
    `[−N, N] × [−1/N, 1/N]` under `(x, y) ↦ (x, α·x − y)` has volume exactly `4`,
    for every `α` and every `N > 0` — the `2² · covolume(ℤ²)` input that Minkowski's
    convex-body theorem consumes in the Dirichlet re-derivation. -/
theorem volume_dirichlet_body (α : ℝ) (N : ℝ) (hN : 0 < N) :
    volume (Matrix.toLin' !![1, 0; α, -1] '' Set.Icc ![-N, -(1 / N)] ![N, 1 / N]) = 4 := by
  have hNe : N ≠ 0 := hN.ne'
  rw [volume_toLin'_image_Icc, Fin.prod_univ_two]
  have hdet : |(!![1, 0; α, -1] : Matrix (Fin 2) (Fin 2) ℝ).det| = 1 := by
    rw [Matrix.det_fin_two_of]; norm_num
  have h0 :
      (![N, 1 / N] : Fin 2 → ℝ) 0 - (![-N, -(1 / N)] : Fin 2 → ℝ) 0 = 2 * N := by
    simp only [Matrix.cons_val_zero]; ring
  have h1 :
      (![N, 1 / N] : Fin 2 → ℝ) 1 - (![-N, -(1 / N)] : Fin 2 → ℝ) 1 = 2 * (1 / N) := by
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero]; ring
  have hprod : (2 * N) * (2 * (1 / N)) = 4 := by
    rw [one_div, mul_mul_mul_comm, mul_inv_cancel₀ hNe, mul_one]; norm_num
  rw [hdet, h0, h1, ENNReal.ofReal_one, one_mul, ← ENNReal.ofReal_mul (by positivity), hprod]
  norm_num

end ParallelepipedVolume
