import Proofs.Erdos85MuThreeAllTfNormalizedAdapter
import Proofs.Erdos85BinarySquareMuThreeExteriorGrid

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

theorem mu3NativeEdgeVal_normalizedGraphAdj_eq_true_iff
    {W : Type*} [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (e : Fin 48 ≃ W)
    (u v : Fin 48) (huv : u ≠ v) :
    mu3NativeEdgeValOfPairRelation (mu3NormalizedGraphAdj G e)
        (mu3NativeEdgeId u v) = true ↔ G.Adj (e u) (e v) := by
  rw [mu3NativeEdgeVal_normalizedGraphAdj G e u v huv]
  by_cases h : u ≤ v
  · simp [min_eq_left h, max_eq_right h]
  · have h' : v ≤ u := le_of_not_ge h
    simp [min_eq_right h', max_eq_left h', G.adj_comm]

theorem mu3NativeCommonTruthValues_count_eq_filter_length
    (val : DimacsValuation) (u v : Nat) :
    (mu3NativeCommonTruthValues val (mu3NativeCommonSpecs u v)).count true =
      ((List.range 48).filter fun m =>
        m ≠ u ∧ m ≠ v ∧
          (val (mu3NativeEdgeId u m) &&
            val (mu3NativeEdgeId v m))).length := by
  simp [mu3NativeCommonTruthValues, mu3NativeCommonSpecs,
    List.count_eq_length_filter]
  generalize List.range 48 = xs
  induction xs with
  | nil => simp
  | cons m rest ih =>
      simp only [List.filterMap_cons, List.filter_cons]
      split_ifs <;> simp_all

set_option maxRecDepth 100000 in
theorem mu3NativePairs_bounds : ∀ pair ∈ mu3NativePairs,
    pair.1 < 48 ∧ pair.2 < 48 ∧ pair.1 ≠ pair.2 := by
  native_decide

/-- C4-freeness supplies the normalized static common-neighbor bound; this
discharges the entire certificate's C4 side without a separate encoding
hypothesis. -/
theorem mu3NormalizedBaseC4_of_c4Free
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 W G) (e : Fin 48 ≃ W) :
    Mu3NormalizedBaseC4 (mu3NormalizedGraphAdj G e) := by
  intro pair hpair
  rw [mu3NativeCommonTruthValues_count_eq_filter_length]
  let candidates := (List.range 48).filter fun m =>
    m ≠ pair.1 ∧ m ≠ pair.2 ∧
      (mu3NativeEdgeValOfPairRelation (mu3NormalizedGraphAdj G e)
          (mu3NativeEdgeId pair.1 m) &&
        mu3NativeEdgeValOfPairRelation (mu3NormalizedGraphAdj G e)
          (mu3NativeEdgeId pair.2 m))
  have hnodup : candidates.Nodup := by
    exact List.nodup_range.filter _
  rw [← List.toFinset_card_of_nodup hnodup]
  apply Finset.card_le_one.mpr
  intro m hm n hn
  have hm' := List.mem_filter.mp (List.mem_toFinset.mp hm)
  have hn' := List.mem_filter.mp (List.mem_toFinset.mp hn)
  have hmP := of_decide_eq_true hm'.2
  have hnP := of_decide_eq_true hn'.2
  have hp := mu3NativePairs_bounds pair hpair
  let u : Fin 48 := ⟨pair.1, hp.1⟩
  let v : Fin 48 := ⟨pair.2, hp.2.1⟩
  let fm : Fin 48 := ⟨m, List.mem_range.mp hm'.1⟩
  let fn : Fin 48 := ⟨n, List.mem_range.mp hn'.1⟩
  have huv : u ≠ v := by
    intro h
    exact hp.2.2 (Fin.ext_iff.mp h)
  have hum : u ≠ fm := by
    intro h
    exact hmP.1 (Fin.ext_iff.mp h).symm
  have hvm : v ≠ fm := by
    intro h
    exact hmP.2.1 (Fin.ext_iff.mp h).symm
  have hun : u ≠ fn := by
    intro h
    exact hnP.1 (Fin.ext_iff.mp h).symm
  have hvn : v ≠ fn := by
    intro h
    exact hnP.2.1 (Fin.ext_iff.mp h).symm
  have hmvals :
      mu3NativeEdgeValOfPairRelation (mu3NormalizedGraphAdj G e)
          (mu3NativeEdgeId pair.1 m) = true ∧
        mu3NativeEdgeValOfPairRelation (mu3NormalizedGraphAdj G e)
          (mu3NativeEdgeId pair.2 m) = true := by
    simpa only [Bool.and_eq_true] using hmP.2.2
  have hnvals :
      mu3NativeEdgeValOfPairRelation (mu3NormalizedGraphAdj G e)
          (mu3NativeEdgeId pair.1 n) = true ∧
        mu3NativeEdgeValOfPairRelation (mu3NormalizedGraphAdj G e)
          (mu3NativeEdgeId pair.2 n) = true := by
    simpa only [Bool.and_eq_true] using hnP.2.2
  have humAdj : G.Adj (e u) (e fm) :=
    (mu3NativeEdgeVal_normalizedGraphAdj_eq_true_iff G e u fm hum).mp hmvals.1
  have hvmAdj : G.Adj (e v) (e fm) :=
    (mu3NativeEdgeVal_normalizedGraphAdj_eq_true_iff G e v fm hvm).mp hmvals.2
  have hunAdj : G.Adj (e u) (e fn) :=
    (mu3NativeEdgeVal_normalizedGraphAdj_eq_true_iff G e u fn hun).mp hnvals.1
  have hvnAdj : G.Adj (e v) (e fn) :=
    (mu3NativeEdgeVal_normalizedGraphAdj_eq_true_iff G e v fn hvn).mp hnvals.2
  have hmn : e fm = e fn :=
    c4Free_commonNeighborPair_injective G hfree (e.injective.ne huv)
      humAdj hunAdj hvmAdj hvnAdj
  exact congrArg Fin.val (e.injective hmn)

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

/-- Sharpened graph endpoint: for a C4-free graph, transported exact row and
column hit counts are the only remaining certificate premise. -/
theorem false_of_c4Free_mu3AllTfGraphHitCounts
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 W G) (e : Fin 48 ≃ W)
    (shape : Mu3AllTfShape)
    (hhit : Mu3NormalizedHitCounts shape (mu3NormalizedGraphAdj G e)) : False :=
  false_of_mu3AllTfGraphConstraints G e shape hhit
    (mu3NormalizedBaseC4_of_c4Free G hfree e)

end Erdos85
