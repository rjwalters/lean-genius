import Mathlib.Topology.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Basic

-- Check for proper space compactness
#check @ProperSpace.isCompact_closedBall
#check @isCompact_isClosed_isBounded
-- #check @Metric.isCompact_of_isClosed_isBounded
-- #check @isCompact_iff_isClosed_isBounded

-- Try IsClosed intersection with compact
#check IsCompact.inter_left
#check IsCompact.inter_right

-- Check convexHull ⊆ span
#check convexHull_subset_affineSpan
-- #check Submodule.convexHull_subset_span

-- Check if there's IsCompact.convexHull in Combination
-- #check Finset.isCompact_convexHull

-- The approach: closure(hull) ⊆ K (closed), so it suffices to show hull is closed.
-- hull ⊆ V (closed subspace), so closure(hull) ⊆ V.
-- Actually can I just do: hull ⊆ V ∩ K, V ∩ K is compact (closed ∩ compact),
-- so hull is precompact. But need it closed for compactness.

-- Alternative: IsClosed.inter gives V ∩ K is closed.
-- But hull ⊆ V ∩ K doesn't make hull closed.

-- Best approach: Use the simplex characterization.
-- convexHull(range pts) = image of stdSimplex under continuous map centerMass
-- stdSimplex is compact, centerMass is continuous, so image is compact
-- Compact implies closed in Hausdorff space.

-- Let me test this approach directly
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (pts : Fin m → E) :
    IsClosed (convexHull ℝ (Set.range pts)) := by
  exact (Set.finite_range pts).isCompact_convexHull.isClosed
