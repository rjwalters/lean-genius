import Proofs.Erdos85CollisionRainbowOwnerPattern

/-! # Private defect pairs are outside propagated owner blocks -/

open SimpleGraph

namespace Erdos85

/-- If `p,q` are the directed private defect neighbors of an equal-row pair
`a,b`, then none of the four cross pairs between `{a,b}` and `{p,q}` belongs
to that owner graph.  In particular, propagation to `p,q` does not identify
the two owner `K₂,₂` blocks. -/
theorem equalRows_privateDefectPair_ownerCross_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (D H : SimpleGraph V) [DecidableRel D.Adj] [DecidableRel H.Adj]
    (hdis : ∀ {x y}, D.Adj x y → ¬ H.Adj x y)
    {a b p q : V}
    (hDp : D.Adj a p) (hDq : D.Adj b q)
    (hrows : ∀ z, H.adjMatrix ℤ a z = H.adjMatrix ℤ b z) :
    ¬H.Adj a p ∧ ¬H.Adj b p ∧ ¬H.Adj a q ∧ ¬H.Adj b q := by
  have rowAdj (z : V) : H.Adj a z ↔ H.Adj b z := by
    have h := hrows z
    simp only [SimpleGraph.adjMatrix_apply] at h
    by_cases haz : H.Adj a z <;> by_cases hbz : H.Adj b z <;>
      simp_all
  have hap : ¬H.Adj a p := hdis hDp
  have hbq : ¬H.Adj b q := hdis hDq
  have hbp : ¬H.Adj b p := by
    intro h
    exact hap ((rowAdj p).mpr h)
  have haq : ¬H.Adj a q := by
    intro h
    exact hbq ((rowAdj q).mp h)
  exact ⟨hap, hbp, haq, hbq⟩

end Erdos85
