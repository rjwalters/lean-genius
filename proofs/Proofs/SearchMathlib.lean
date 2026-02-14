-- Test file to understand Mathlib API for compact convex hulls in finite dimensions
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Convex.Combination
import Mathlib.Analysis.Convex.Hull

open Set Submodule Filter

-- Lemmas we're looking for:
-- 1. isCompact of finite set
#check Set.finite_range
#check Set.Finite.isCompact

-- 2. Finite dimensional space has compact closed convex hull
#check Module.Finite.span_of_finite

-- 3. Compactness in finite-dimensional subspace
#check IsCompact.of_isClosed_isBounded
#check isCompact_of_isClosed_of_isBounded

-- 4. Subspace closure properties
#check Submodule.isClosed
#check IsClosed.closure_eq

-- 5. Convex hull properties
#check convex_convexHull
#check convexHull_mono
