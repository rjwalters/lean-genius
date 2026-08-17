import Proofs.Erdos85BinarySquareOwnerCross

/-!
# Unique mixed routes for unit owner colors

The rank-one cross-product identity for shifted owner matrices has a sharp
combinatorial meaning when both normalized component sizes are one: the
reflexive closures of two distinct owner colors compose to the complete
relation with multiplicity exactly one.
-/

open SimpleGraph

namespace Erdos85

/-- Distinct normalized-size-one owner colors give a unique mixed two-step
route between every ordered pair of ambient vertices. -/
theorem binarySquare_regular_unitOwnerColors_existsUnique_mixedRoute
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c d : (secondOrderDefectGraph G).ConnectedComponent) (hcd : c ≠ d)
    (hc : c.supp.ncard = q) (hd : d.supp.ncard = q)
    (x z : V) :
    ∃! y : V,
      (x = y ∨ (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj x y) ∧
      (y = z ∨ (componentOwnerGraph G (secondOrderDefectGraph G) d).Adj y z) := by
  let Oc := componentOwnerGraph G (secondOrderDefectGraph G) c
  let Od := componentOwnerGraph G (secondOrderDefectGraph G) d
  let P : V → Prop := fun y =>
    (x = y ∨ Oc.Adj x y) ∧ (y = z ∨ Od.Adj y z)
  have hprod := binarySquare_regular_shiftedOwnerMatrices_cross_product
    G hfree hq hreg hcard c d hcd (m_c := 1) (m_d := 1)
      (by simpa using hc) (by simpa using hd)
  have hentry := congrArg (fun M : Matrix V V ℤ => M x z) hprod
  have hsum : (∑ y : V, if P y then (1 : ℤ) else 0) = 1 := by
    calc
      (∑ y : V, if P y then (1 : ℤ) else 0) =
          ∑ y : V,
            (Oc.adjMatrix ℤ x y + (1 : Matrix V V ℤ) x y) *
            (Od.adjMatrix ℤ y z + (1 : Matrix V V ℤ) y z) := by
        apply Finset.sum_congr rfl
        intro y _hy
        by_cases hxy : x = y
        · subst y
          have hloopc : ¬ Oc.Adj x x := Oc.loopless.irrefl x
          by_cases hxz : x = z
          · subst z
            have hloopd : ¬ Od.Adj x x := Od.loopless.irrefl x
            simp [P, hloopc, hloopd, SimpleGraph.adjMatrix_apply]
          · by_cases hdxz : Od.Adj x z <;>
              simp [P, hloopc, hxz, hdxz, SimpleGraph.adjMatrix_apply]
        · by_cases hcxy : Oc.Adj x y
          · by_cases hyz : y = z
            · subst z
              have hloopd : ¬ Od.Adj y y := Od.loopless.irrefl y
              simp [P, hxy, hcxy, hloopd, SimpleGraph.adjMatrix_apply]
            · by_cases hdyz : Od.Adj y z <;>
                simp [P, hxy, hcxy, hyz, hdyz, SimpleGraph.adjMatrix_apply]
          · simp [P, hxy, hcxy, SimpleGraph.adjMatrix_apply]
      _ = 1 := by
        simpa [Oc, Od, Matrix.mul_apply, Matrix.add_apply, Matrix.one_apply,
          FriendshipTheoremOQ01.onesMatrix, Matrix.smul_apply] using hentry
  rw [Finset.sum_boole] at hsum
  have hcardP : ((Finset.univ : Finset V).filter P).card = 1 := by
    exact_mod_cast hsum
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hcardP
  have hyP : P y := by
    have : y ∈ (Finset.univ : Finset V).filter P := by rw [hy]; simp
    exact (Finset.mem_filter.mp this).2
  refine ⟨y, hyP, ?_⟩
  intro w hw
  have hwmem : w ∈ (Finset.univ : Finset V).filter P :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ w, hw⟩
  rw [hy] at hwmem
  simpa using hwmem

/-- **Distinct-intermediate composition law.**  Fix two distinct unit owner
colors.  Matching equivalences composed through two different intermediate
defect components disagree at every source point.  Otherwise the two
intermediate images would be two mixed-color routes with the same endpoints,
contradicting uniqueness. -/
theorem unitOwnerColors_matchingCompositions_pointwise_ne_of_intermediate_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (e f f' g c d : (secondOrderDefectGraph G).ConnectedComponent)
    (hff' : f ≠ f') (hcd : c ≠ d)
    (hc : c.supp.ncard = q) (hd : d.supp.ncard = q)
    (σ : g.supp ≃ f.supp) (τ : f.supp ≃ e.supp)
    (σ' : g.supp ≃ f'.supp) (τ' : f'.supp ≃ e.supp)
    (hσ : ∀ x : g.supp,
      (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj x.1 (σ x).1)
    (hτ : ∀ y : f.supp,
      (componentOwnerGraph G (secondOrderDefectGraph G) d).Adj y.1 (τ y).1)
    (hσ' : ∀ x : g.supp,
      (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj x.1 (σ' x).1)
    (hτ' : ∀ y : f'.supp,
      (componentOwnerGraph G (secondOrderDefectGraph G) d).Adj y.1 (τ' y).1)
    (x : g.supp) : τ (σ x) ≠ τ' (σ' x) := by
  intro hout
  let Oc := componentOwnerGraph G (secondOrderDefectGraph G) c
  let Od := componentOwnerGraph G (secondOrderDefectGraph G) d
  have hroute := binarySquare_regular_unitOwnerColors_existsUnique_mixedRoute
    G hfree hq hreg hcard c d hcd hc hd x.1 (τ (σ x)).1
  have hy :
      (x.1 = (σ x).1 ∨ Oc.Adj x.1 (σ x).1) ∧
      ((σ x).1 = (τ (σ x)).1 ∨ Od.Adj (σ x).1 (τ (σ x)).1) :=
    ⟨Or.inr (hσ x), Or.inr (hτ (σ x))⟩
  have hy' :
      (x.1 = (σ' x).1 ∨ Oc.Adj x.1 (σ' x).1) ∧
      ((σ' x).1 = (τ (σ x)).1 ∨ Od.Adj (σ' x).1 (τ (σ x)).1) := by
    refine ⟨Or.inr (hσ' x), Or.inr ?_⟩
    have houtVal : (τ' (σ' x)).1 = (τ (σ x)).1 :=
      congrArg Subtype.val hout.symm
    rw [← houtVal]
    exact hτ' (σ' x)
  have hinter : (σ x).1 = (σ' x).1 := hroute.unique hy hy'
  have hfComp : (secondOrderDefectGraph G).connectedComponentMk (σ x).1 = f :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff f (σ x).1).mp (σ x).2
  have hf'Comp : (secondOrderDefectGraph G).connectedComponentMk (σ' x).1 = f' :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff f' (σ' x).1).mp (σ' x).2
  have hfeq : f = f' := by
    calc
      f = (secondOrderDefectGraph G).connectedComponentMk (σ x).1 := hfComp.symm
      _ = (secondOrderDefectGraph G).connectedComponentMk (σ' x).1 := by rw [hinter]
      _ = f' := hf'Comp
  exact hff' hfeq

end Erdos85
