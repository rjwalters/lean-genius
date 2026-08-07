import Proofs.Erdos85DoubleCoverProjectionFiber
import Proofs.Erdos85ForwardSupportClassification

/-!
# Graph-facing projected anchor on a cyclic double cover

The abstract deck-fiber quantization is transported to the exact form used
by `orientedProjectedAnchor`.  A forward-oriented doubled component joined
to its base cycle by a quotient-one cyclic cover contributes, at every
nonzero residue, precisely the indicator of one ordered difference.
-/

namespace Erdos85

noncomputable section

open SimpleGraph

/-- A forward cyclic diagonal support is inverse closed. -/
theorem negFinset_graphCycleBlockZeroSupport_of_forward
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {r : ℕ} [NeZero r] (v : ZMod r → V)
    (hfwd : ∀ x y : ZMod r,
      G.Adj (v (x + 1)) (v (y + 1)) ↔ G.Adj (v x) (v y)) :
    negFinset (graphCycleBlockZeroSupport G v v) =
      graphCycleBlockZeroSupport G v v := by
  ext z
  rw [mem_negFinset_iff]
  constructor
  · intro hz
    have := neg_mem_graphCycleBlockZeroSupport_of_forward G v hfwd hz
    simpa using this
  · exact neg_mem_graphCycleBlockZeroSupport_of_forward G v hfwd

/-- **Double-cover projected-anchor formula.**  Suppose a labeled
`2p`-cycle is joined to a disjoint labeled `p`-cycle by an oriented cyclic
double cover, and its diagonal adjacency block is forward-oriented.  Then
for every nonzero residue `t`, the diagonal support in the reduction fiber
over `t` has cardinality zero or one, and is present exactly when the
doubled canonical lift is an ordered difference of the diagonal support. -/
theorem graph_doubleCover_projectedAnchor_eq_indicator_ods
    {V : Type*} [Fintype V] [DecidableEq V]
    {p : ℕ} [NeZero p]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    (u : ZMod p → V) (v : ZMod (2 * p) → V)
    (hsep : ∀ x y, u x ≠ v y)
    (hvinj : Function.Injective v)
    (f : ZMod (2 * p) → ZMod p)
    (hadj : ∀ x y, G.Adj (u x) (v y) ↔ x = f y)
    (horient : (∀ y, f (y + 1) = f y + 1) ∨
      (∀ y, f (y + 1) = f y - 1))
    (hfwd : ∀ x y : ZMod (2 * p),
      G.Adj (v (x + 1)) (v (y + 1)) ↔ G.Adj (v x) (v y))
    (t : ZMod p) (ht : t ≠ 0) :
    let A := graphCycleBlockZeroSupport G v v
    let x : ZMod (2 * p) := (t.val : ℕ)
    (A.filter (fun z : ZMod (2 * p) ↦
      ((z.val : ℕ) : ZMod p) = t)).card =
        if 2 * x ∈ orderedDifferenceSet A then 1 else 0 := by
  classical
  dsimp only
  let A := graphCycleBlockZeroSupport G v v
  let hpdiv : p ∣ (2 : ℕ) * p := dvd_mul_left p 2
  have hneg : negFinset A = A := by
    exact negFinset_graphCycleBlockZeroSupport_of_forward G v hfwd
  have htrans : ∀ x y : ZMod (2 * p),
      G.adjMatrix ℤ (v (x + 1)) (v (y + 1)) =
        G.adjMatrix ℤ (v x) (v y) := by
    intro x y
    simp only [SimpleGraph.adjMatrix_apply, hfwd x y]
  have hsidon : IsOrderedSidon A := by
    change IsOrderedSidon (zeroRowSupport
      (fun x y : ZMod (2 * p) ↦ G.adjMatrix ℤ (v x) (v y)))
    exact isOrderedSidon_zeroRowSupport_of_c4Free_orientation
      G hfree v v hvinj hvinj (Or.inl htrans)
  have hdeck : ∀ y ∈ A,
      y + (p : ZMod (2 * p)) ∉ A := by
    intro y hy hyp
    have hmixed : mixedAnchorSupport G (v 0) v = A := by
      exact mixedAnchorSupport_eq_graphCycleBlockZeroSupport G v v
    apply cycleCover_diagAnchor_not_both_halfTurns G hfree u v hsep hvinj
      f hadj horient y
    rw [hmixed]
    exact ⟨hy, hyp⟩
  have hquant := card_doubleCover_projectedSupport_eq_indicator_ods
    A hneg hsidon hdeck t ht
  dsimp only at hquant
  rw [← hquant]
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_inter, projectionFiber,
    Finset.mem_univ, true_and]
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

end

end Erdos85
