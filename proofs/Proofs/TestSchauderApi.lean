import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Contracting

open Set Metric

noncomputable section

-- Test: Check if LipschitzWith.of_dist_le_mul exists
#check @LipschitzWith.of_dist_le_mul

-- Test: Build LipschitzWith from dist hypothesis using of_dist_le_mul
example {X : Type*} [PseudoMetricSpace X]
    {f : X → X} {k : NNReal}
    (hlip : ∀ x y, dist (f x) (f y) ≤ k * dist x y) :
    LipschitzWith k f :=
  LipschitzWith.of_dist_le_mul hlip

-- Test: Full Banach contraction
theorem banach_test
    {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    {f : X → X} {k : ℝ} (hk : k < 1) (hk0 : 0 ≤ k)
    (hlip : ∀ x y, dist (f x) (f y) ≤ k * dist x y) :
    ∃! x, f x = x := by
  let K : NNReal := ⟨k, hk0⟩
  have hK_nnreal : K < 1 := by exact_mod_cast hk
  have hlip' : LipschitzWith K f := LipschitzWith.of_dist_le_mul hlip
  have hcontr : ContractingWith K f := ⟨hK_nnreal, hlip'⟩
  exact ⟨hcontr.fixedPoint f,
    hcontr.fixedPoint_isFixedPt,
    fun y hy => (hcontr.fixedPoint_unique hy)⟩
