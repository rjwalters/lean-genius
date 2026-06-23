import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Tactic

set_option maxHeartbeats 800000

noncomputable section

open Set Metric Topology TopologicalSpace

-- The orthogonal complement homeomorphism to EuclideanSpace ℝ (Fin 3)
def orthCompHomeomorph (v : EuclideanSpace ℝ (Fin 4)) (hv : ‖v‖ = 1) :
    ↥(Submodule.span ℝ {v})ᗮ ≃ₜ EuclideanSpace ℝ (Fin 3) := by
  have hdim : Module.finrank ℝ ↥(Submodule.span ℝ {v})ᗮ = 3 := by
    have h1 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 4 := by
      rw [finrank_euclideanSpace_fin]
    have h2 : Module.finrank ℝ (Submodule.span ℝ {v}) = 1 := by
      rw [finrank_span_singleton]
      simp [hv, norm_ne_zero_iff.mpr (by intro h; simp [h] at hv)]
    have h3 := Submodule.finrank_add_finrank_orthogonal
      (Submodule.span ℝ ({v} : Set (EuclideanSpace ℝ (Fin 4))))
    omega
  let b := stdOrthonormalBasis ℝ ↥(Submodule.span ℝ {v})ᗮ
  let b3 := b.reindex (Fintype.equivFinOfCardEq (by simp [hdim]))
  exact b3.repr.toHomeomorph

-- Compose stereographic with orthCompHomeomorph to get chart to R^3
def sphereChartToR3 (v : EuclideanSpace ℝ (Fin 4)) (hv : ‖v‖ = 1) :
    OpenPartialHomeomorph ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
      (EuclideanSpace ℝ (Fin 3)) :=
  (stereographic hv).transHomeomorph (orthCompHomeomorph v hv)

-- Helper: on the unit sphere in R^n (n ≥ 1), x ≠ -x
lemma sphere_ne_neg (x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)) :
    x ≠ ⟨-(x : EuclideanSpace ℝ (Fin 4)),
      mem_sphere_zero_iff_norm.mpr (by rw [norm_neg]; exact mem_sphere_zero_iff_norm.mp x.2)⟩ := by
  intro h
  have heq : (x : EuclideanSpace ℝ (Fin 4)) = -(x : EuclideanSpace ℝ (Fin 4)) :=
    congr_arg Subtype.val h
  have hx_norm : ‖(x : EuclideanSpace ℝ (Fin 4))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp x.2
  -- From x = -x we get x + x = 0
  have h2 : (x : EuclideanSpace ℝ (Fin 4)) + (x : EuclideanSpace ℝ (Fin 4)) = 0 := by
    rw [heq]; simp [add_neg_cancel]
  -- So 2 • x = 0
  have h3 : (2 : ℝ) • (x : EuclideanSpace ℝ (Fin 4)) = 0 := by
    rw [two_smul]; exact h2
  -- So x = 0
  have h4 : (x : EuclideanSpace ℝ (Fin 4)) = 0 := by
    have : (2 : ℝ) ≠ 0 := by norm_num
    exact (smul_eq_zero.mp h3).resolve_left this
  -- But ‖x‖ = 1 ≠ 0
  rw [h4] at hx_norm
  simp at hx_norm

-- Check stereographic target
#check @stereographic_target

-- Prove S³ is locally Euclidean
-- Strategy: use stereographic from -x, which has source = S³ \ {-x} and target = univ
theorem sphere3_locally_euclidean' :
    ∀ x : ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1),
    ∃ U : Set ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1), IsOpen U ∧ x ∈ U ∧
    ∃ (_e : U ≃ₜ EuclideanSpace ℝ (Fin 3)), True := by
  intro x
  have hneg : ‖-(x : EuclideanSpace ℝ (Fin 4))‖ = 1 := by
    rw [norm_neg]; exact mem_sphere_zero_iff_norm.mp x.2
  let chart := sphereChartToR3 (-(x : EuclideanSpace ℝ (Fin 4))) hneg
  use chart.source, chart.open_source
  constructor
  · -- x ∈ chart.source
    simp only [chart, sphereChartToR3, OpenPartialHomeomorph.transHomeomorph_source]
    rw [stereographic_source]
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact sphere_ne_neg x
  · -- chart has target = Set.univ (stereographic is surjective onto the model space)
    -- So chart.toHomeomorphSourceTarget : chart.source ≃ₜ chart.target
    -- and chart.target = univ means chart.target ≃ₜ EuclideanSpace ℝ (Fin 3)
    -- Actually, we need to verify the target is univ first
    -- stereographic_target says (stereographic hv).target = Set.univ
    have htarget : chart.target = Set.univ := by
      simp only [chart, sphereChartToR3, OpenPartialHomeomorph.transHomeomorph_target]
      rw [stereographic_target]
      simp [Homeomorph.range_coe]
    -- Now: chart gives homeomorphism from source to target = univ
    -- chart.toHomeomorphSourceTarget : source ≃ₜ target
    -- We want: source ≃ₜ EuclideanSpace ℝ (Fin 3)
    -- Use: target = univ, so target ≃ₜ EuclideanSpace ℝ (Fin 3)
    have heq : ↥chart.target = EuclideanSpace ℝ (Fin 3) := by
      rw [htarget]; simp
    refine ⟨chart.toHomeomorphSourceTarget.trans ?_, trivial⟩
    exact Homeomorph.setCongr htarget |>.trans (Homeomorph.Set.univ _)

end
