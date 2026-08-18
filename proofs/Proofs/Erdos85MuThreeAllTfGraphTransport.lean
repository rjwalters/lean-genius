import Proofs.Erdos85MuThreeAllTfNormalizedAdapter
import Mathlib.Combinatorics.SimpleGraph.Basic

/-! # Relabeling a 48-vertex graph for the all-TF certificate

This is the type-level boundary between an exterior graph and the normalized
`Fin 48` relation consumed by the checked certificate.  The structural work
upstream only has to supply an equivalence with `Fin 48` and establish the
hit-count and common-neighbor laws after this relabeling.
-/

open SimpleGraph

namespace Erdos85

/-- The unordered-pair Boolean relation obtained by transporting a graph
along an enumeration of its 48 vertices.  Values outside the normalized
range are deliberately false; native edge IDs never query them. -/
def mu3NormalizedGraphAdj {W : Type*} [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (e : Fin 48 ≃ W) :
    (Nat × Nat) → Bool := fun uv =>
  if hu : uv.1 < 48 then
    if hv : uv.2 < 48 then
      decide (G.Adj (e ⟨uv.1, hu⟩) (e ⟨uv.2, hv⟩))
    else false
  else false

theorem mu3NormalizedGraphAdj_pair {W : Type*} [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (e : Fin 48 ≃ W)
    (u v : Fin 48) :
    mu3NormalizedGraphAdj G e (min u.val v.val, max u.val v.val) =
      decide (G.Adj (e (min u v)) (e (max u v))) := by
  have hmin : min u.val v.val < 48 :=
    lt_of_le_of_lt (min_le_left _ _) u.isLt
  have hmax : max u.val v.val < 48 := (max_lt_iff.mpr ⟨u.isLt, v.isLt⟩)
  simp only [mu3NormalizedGraphAdj]
  rw [dif_pos hmin, dif_pos hmax]
  congr 3

theorem mu3NativeEdgeVal_normalizedGraphAdj {W : Type*} [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (e : Fin 48 ≃ W)
    (u v : Fin 48) (huv : u ≠ v) :
    mu3NativeEdgeValOfPairRelation (mu3NormalizedGraphAdj G e)
        (mu3NativeEdgeId u v) =
      decide (G.Adj (e (min u v)) (e (max u v))) := by
  rw [mu3NativeEdgeValOfPairRelation_edge _ u v huv]
  exact mu3NormalizedGraphAdj_pair G e u v

/-- Certificate endpoint stated directly for an arbitrary graph with exactly
48 enumerated vertices.  The two hypotheses are intentionally mathematical
graph laws, transported through `mu3NormalizedGraphAdj`; no DIMACS valuation
is exposed. -/
theorem false_of_mu3AllTfGraphConstraints
    {W : Type*} [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (e : Fin 48 ≃ W)
    (shape : Mu3AllTfShape)
    (hhit : Mu3NormalizedHitCounts shape (mu3NormalizedGraphAdj G e))
    (hc4 : Mu3NormalizedBaseC4 (mu3NormalizedGraphAdj G e)) : False :=
  false_of_mu3AllTfNormalizedConstraints shape (mu3NormalizedGraphAdj G e)
    ⟨hhit, hc4⟩

end Erdos85
