import Proofs.Erdos85BinarySquareRegularParity
import Proofs.Erdos85ExceptionalCoreCliqueSaturation

/-!
# No order-q defect clique at even degree

The binary-square defect graph is `(q-1)`-regular.  A `q`-vertex defect
clique therefore exhausts every one of its vertices' defect neighborhoods,
so it is a whole connected component.  The existing parity theorem excludes
components of order `q` when `q` is even.
-/

open SimpleGraph

namespace Erdos85

/-- At even regular degree, a binary-square second-order defect graph has no
clique of cardinality `q`. -/
theorem binarySquare_regular_no_sizeQ_secondOrderDefect_clique_of_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q) (hqEven : Even q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (C : Finset V) (hCcard : C.card = q)
    (hclique : ∀ ⦃u v⦄, u ∈ C → v ∈ C → u ≠ v →
      (secondOrderDefectGraph G).Adj u v) : False := by
  let D := secondOrderDefectGraph G
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDdegree : ∀ z : V, D.degree z = q - 1 := by
    intro z
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus z
    change D.degree z = (q - 3) + 2 at h
    omega
  have hclosed : ∀ ⦃u v : V⦄, u ∈ C → D.Adj u v → v ∈ C := by
    intro u v hu huv
    have hvN : v ∈ D.neighborFinset u := (D.mem_neighborFinset u v).mpr huv
    rw [neighborFinset_eq_clique_erase_of_degree_saturated
      D C hCcard hclique u hu (hDdegree u)] at hvN
    exact (Finset.mem_erase.mp hvN).2
  have hCnonempty : C.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hxC⟩ := hCnonempty
  let c : D.ConnectedComponent := D.connectedComponentMk x
  have hreach_mem : ∀ ⦃y : V⦄, D.Reachable x y → y ∈ C := by
    intro y hreach
    rw [D.reachable_iff_reflTransGen] at hreach
    induction hreach with
    | refl => exact hxC
    | tail hreach hadj ih => exact hclosed ih hadj
  have hsupport : c.supp = (C : Set V) := by
    ext y
    constructor
    · intro hy
      have hreach : D.Reachable x y := by
        exact (SimpleGraph.ConnectedComponent.exact hy).symm
      exact hreach_mem hreach
    · intro hy
      rw [SimpleGraph.ConnectedComponent.mem_supp_iff]
      change D.connectedComponentMk y = D.connectedComponentMk x
      by_cases hyx : y = x
      · exact congrArg D.connectedComponentMk hyx
      · exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj
          (hclique hy hxC hyx)
  have hc : c.supp.ncard = q := by
    rw [hsupport, Set.ncard_coe_finset, hCcard]
  exact binarySquare_regular_no_sizeQ_defectComponent_of_even
    G hfree hq hqEven hreg hcard c hc

end Erdos85

#print axioms Erdos85.binarySquare_regular_no_sizeQ_secondOrderDefect_clique_of_even
