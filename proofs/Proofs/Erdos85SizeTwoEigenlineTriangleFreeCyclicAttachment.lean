import Proofs.Erdos85SizeTwoEigenlineTriangleFreeSector
import Proofs.Erdos85SizeTwoEigenlineCyclicPermutationExactCode

/-!
# Attaching the all-triangle-free sector to the cyclic code

Node: `SIZE-TWO-EIGENLINE(q)` (outline F.3).

Once the missing cells are exactly the internal shifts, the occupied witness
grid is the cyclic exterior grid with reflection parameter `a = 0`.  This
file transports the ambient exterior graph to that grid and constructs the
exact reciprocal permutation code consumed by the packing layer.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

theorem sizeTwoReflectionRel_zero_iff
    (q : ℕ) (x y : ZMod q) :
    sizeTwoReflectionRel q 0 x y ↔ y = x ∨ y = x - 1 := by
  constructor
  · rintro (h | h)
    · left
      have hz := congrArg (fun z : ZMod q => z + x) h
      simpa [sizeTwoReflectionRel] using hz
    · right
      simp only [sub_zero] at h
      have hz := congrArg (fun z : ZMod q => z + x) h
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hz
  · rintro (rfl | rfl)
    · left; simp
    · right; ring

/-- Choose the unique ambient witness of an occupied cyclic cell. -/
def sizeTwoTriangleFreeCellWitness
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (pval nval : ZMod q → V)
    (hocc : ∀ u : sizeTwoCyclicExteriorCell q 0,
      ∃ w, IsGridWitness G c pval nval w u.1.1 u.1.2)
    (u : sizeTwoCyclicExteriorCell q 0) : V :=
  Classical.choose (hocc u)

theorem sizeTwoTriangleFreeCellWitness_spec
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (pval nval : ZMod q → V)
    (hocc : ∀ u : sizeTwoCyclicExteriorCell q 0,
      ∃ w, IsGridWitness G c pval nval w u.1.1 u.1.2)
    (u : sizeTwoCyclicExteriorCell q 0) :
    IsGridWitness G c pval nval
      (sizeTwoTriangleFreeCellWitness G c pval nval hocc u) u.1.1 u.1.2 :=
  Classical.choose_spec (hocc u)

/-- Ambient adjacency pulled back along the occupied-cell witness map. -/
def sizeTwoTriangleFreeCyclicGraph
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (pval nval : ZMod q → V)
    (hocc : ∀ u : sizeTwoCyclicExteriorCell q 0,
      ∃ w, IsGridWitness G c pval nval w u.1.1 u.1.2) :
    SimpleGraph (sizeTwoCyclicExteriorCell q 0) :=
  G.comap (sizeTwoTriangleFreeCellWitness G c pval nval hocc)

noncomputable instance sizeTwoTriangleFreeCyclicGraph_decidable
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} [NeZero q]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (pval nval : ZMod q → V)
    (hocc : ∀ u : sizeTwoCyclicExteriorCell q 0,
      ∃ w, IsGridWitness G c pval nval w u.1.1 u.1.2) :
    DecidableRel (sizeTwoTriangleFreeCyclicGraph G c pval nval hocc).Adj := by
  intro u v
  unfold sizeTwoTriangleFreeCyclicGraph
  infer_instance

/-- The occupied-cell witness map is injective. -/
theorem sizeTwoTriangleFreeCellWitness_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {q : ℕ} [NeZero q] (hq : 5 ≤ q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hsum : ∑ x, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      ((q : ℤ) - 5) * s x)
    (coord : SizeTwoCycleGridCoordinates G c.supp s q)
    (hocc : ∀ u : sizeTwoCyclicExteriorCell q 0,
      ∃ w, IsGridWitness G c coord.pval coord.nval w u.1.1 u.1.2) :
    Function.Injective
      (sizeTwoTriangleFreeCellWitness G c coord.pval coord.nval hocc) := by
  intro u v huv
  have hu := sizeTwoTriangleFreeCellWitness_spec
    G c coord.pval coord.nval hocc u
  have hv0 := sizeTwoTriangleFreeCellWitness_spec
    G c coord.pval coord.nval hocc v
  have hv : IsGridWitness G c coord.pval coord.nval
      (sizeTwoTriangleFreeCellWitness G c coord.pval coord.nval hocc u)
      v.1.1 v.1.2 := by
    rw [huv]
    exact hv0
  obtain ⟨p, n, hpS, hnS, hps, hns, heq⟩ := exterior_labels G hfree hq
    hreg hcard c hc s hs_in hs_out hsum hA_in hDs hu.1
  have positive_unique : ∀ z y : ZMod q,
      IsGridWitness G c coord.pval coord.nval
        (sizeTwoTriangleFreeCellWitness G c coord.pval coord.nval hocc u)
        z y → coord.pval z = p := by
    intro z y hz
    have hm : coord.pval z ∈ componentNeighborFinset G
        (secondOrderDefectGraph G) c
        (sizeTwoTriangleFreeCellWitness G c coord.pval coord.nval hocc u) := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hz.2.1,
        (ConnectedComponent.mem_supp_iff c _).mp (coord.p_mem_sign z).1⟩
    rw [heq, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · exact hm
    · exfalso
      have hs := (coord.p_mem_sign z).2
      rw [hm, hns] at hs
      norm_num at hs
  have negative_unique : ∀ x z : ZMod q,
      IsGridWitness G c coord.pval coord.nval
        (sizeTwoTriangleFreeCellWitness G c coord.pval coord.nval hocc u)
        x z → coord.nval z = n := by
    intro x z hz
    have hm : coord.nval z ∈ componentNeighborFinset G
        (secondOrderDefectGraph G) c
        (sizeTwoTriangleFreeCellWitness G c coord.pval coord.nval hocc u) := by
      rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset _ _).mpr hz.2.2,
        (ConnectedComponent.mem_supp_iff c _).mp (coord.n_mem_sign z).1⟩
    rw [heq, Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with hm | hm
    · exfalso
      have hs := (coord.n_mem_sign z).2
      rw [hm, hps] at hs
      norm_num at hs
    · exact hm
  apply Subtype.ext
  apply Prod.ext
  · apply coord.p_injective
    exact (positive_unique u.1.1 u.1.2 hu).trans
      (positive_unique v.1.1 v.1.2 hv).symm
  · apply coord.n_injective
    exact (negative_unique u.1.1 u.1.2 hu).trans
      (negative_unique v.1.1 v.1.2 hv).symm

/-- Pullback along the injective witness map preserves C4-freeness. -/
theorem sizeTwoTriangleFreeCyclicGraph_c4Free
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    {q : ℕ} [NeZero q]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (pval nval : ZMod q → V)
    (hocc : ∀ u : sizeTwoCyclicExteriorCell q 0,
      ∃ w, IsGridWitness G c pval nval w u.1.1 u.1.2)
    (hinj : Function.Injective
      (sizeTwoTriangleFreeCellWitness G c pval nval hocc))
    (hfree : ¬ containsC4 V G) :
    ¬ containsC4 _ (sizeTwoTriangleFreeCyclicGraph G c pval nval hocc) := by
  rintro ⟨f, hf, hadj⟩
  apply hfree
  refine ⟨fun i => sizeTwoTriangleFreeCellWitness G c pval nval hocc (f i),
    hinj.comp hf, ?_⟩
  intro i j hij
  exact hadj i j hij

/-- **All-triangle-free cyclic attachment.**  If the graph-derived missing
cells are exactly the internal shifts, the exterior witness graph supplies
an exact cyclic permutation code with reflection parameter `a = 0`. -/
theorem nonempty_sizeTwoCyclicExactPermutationCode_zero_of_hole_eq_internal
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {q : ℕ} [NeZero q] (hq : 5 ≤ q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2) (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hsum : ∑ x, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      ((q : ℤ) - 5) * s x)
    (coord : SizeTwoCycleGridCoordinates G c.supp s q)
    (hhole : ∀ x y : ZMod q,
      (¬ ∃ u, IsGridWitness G c coord.pval coord.nval u x y) ↔
        y = x ∨ y = x - 1) :
    Nonempty (SizeTwoCyclicExactPermutationCode q 0) := by
  classical
  have hocc : ∀ u : sizeTwoCyclicExteriorCell q 0,
      ∃ w, IsGridWitness G c coord.pval coord.nval w u.1.1 u.1.2 := by
    intro u
    by_contra hno
    have hp := (hhole u.1.1 u.1.2).mp hno
    exact u.2 ((sizeTwoReflectionRel_zero_iff q u.1.1 u.1.2).mpr hp)
  let C := sizeTwoTriangleFreeCyclicGraph G c coord.pval coord.nval hocc
  have hinj := sizeTwoTriangleFreeCellWitness_injective G hfree hq hreg hcard
    c hc s hs_in hs_out hsum hA_in hDs coord hocc
  have hCfree : ¬ containsC4 (sizeTwoCyclicExteriorCell q 0) C :=
    sizeTwoTriangleFreeCyclicGraph_c4Free G c coord.pval coord.nval
      hocc hinj hfree
  have hrow : ∀ (u : sizeTwoCyclicExteriorCell q 0) (x' : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = x').card =
        if u.1.2 = x' ∨ u.1.2 = x' - 1 then 0 else 1 := by
    intro u x'
    let w := sizeTwoTriangleFreeCellWitness G c coord.pval coord.nval hocc u
    have hw := sizeTwoTriangleFreeCellWitness_spec
      G c coord.pval coord.nval hocc u
    have hraw := cell_row_neighbors_card G c s coord.pval coord.nval hfree hq
      hreg hcard hc hs_in hs_out hsum hA_in hDs coord.p_mem_sign
      coord.n_mem_sign coord.n_injective coord.n_surjective coord.adj_iff hw x'
    rw [← hraw]
    apply Finset.card_bij (fun v _ => v.1.2)
    · intro v hv
      rw [Finset.mem_filter] at hv ⊢
      have hadj : G.Adj w
          (sizeTwoTriangleFreeCellWitness G c coord.pval coord.nval hocc v) :=
        (C.mem_neighborFinset u v).mp hv.1
      exact ⟨Finset.mem_univ _,
        sizeTwoTriangleFreeCellWitness G c coord.pval coord.nval hocc v,
        by simpa [hv.2] using
          (sizeTwoTriangleFreeCellWitness_spec
            G c coord.pval coord.nval hocc v), hadj⟩
    · intro v₁ hv₁ v₂ hv₂ heq
      apply Subtype.ext
      apply Prod.ext
      · exact (Finset.mem_filter.mp hv₁).2.trans
          (Finset.mem_filter.mp hv₂).2.symm
      · exact heq
    · intro y' hy'
      rw [Finset.mem_filter] at hy'
      obtain ⟨-, w', hw', hadj⟩ := hy'
      have hnot : ¬ sizeTwoReflectionRel q 0 x' y' := by
        intro href
        have hp := (sizeTwoReflectionRel_zero_iff q x' y').mp href
        exact (hhole x' y').mpr hp ⟨w', hw'⟩
      let v : sizeTwoCyclicExteriorCell q 0 := ⟨(x', y'), hnot⟩
      have hvw : sizeTwoTriangleFreeCellWitness G c coord.pval coord.nval hocc v =
          w' := gridWitness_unique G c s coord.pval coord.nval hfree
            (fun x => (coord.p_mem_sign x).2)
            (fun y => (coord.n_mem_sign y).2)
            (sizeTwoTriangleFreeCellWitness_spec
              G c coord.pval coord.nval hocc v) hw'
      refine ⟨v, Finset.mem_filter.mpr ⟨?_, rfl⟩, rfl⟩
      apply (C.mem_neighborFinset u v).mpr
      simpa [w, C, sizeTwoTriangleFreeCyclicGraph, hvw] using hadj
  have hcol : ∀ (u : sizeTwoCyclicExteriorCell q 0) (y' : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = y').card =
        if u.1.1 = y' ∨ u.1.1 = y' + 1 then 0 else 1 := by
    intro u y'
    let w := sizeTwoTriangleFreeCellWitness G c coord.pval coord.nval hocc u
    have hw := sizeTwoTriangleFreeCellWitness_spec
      G c coord.pval coord.nval hocc u
    have hraw := cell_col_neighbors_card G c s coord.pval coord.nval hfree hq
      hreg hcard hc hs_in hs_out hsum hA_in hDs coord.p_mem_sign
      coord.n_mem_sign coord.p_injective coord.p_surjective coord.adj_iff hw y'
    have hcond : (u.1.1 = y' ∨ u.1.1 = y' + 1) ↔
        (y' = u.1.1 ∨ y' = u.1.1 - 1) := by
      constructor
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr (by rw [h]; ring)
      · rintro (h | h)
        · exact Or.inl h.symm
        · exact Or.inr (by rw [h]; ring)
    rw [if_congr hcond rfl rfl, ← hraw]
    apply Finset.card_bij (fun v _ => v.1.1)
    · intro v hv
      rw [Finset.mem_filter] at hv ⊢
      have hadj : G.Adj w
          (sizeTwoTriangleFreeCellWitness G c coord.pval coord.nval hocc v) :=
        (C.mem_neighborFinset u v).mp hv.1
      exact ⟨Finset.mem_univ _,
        sizeTwoTriangleFreeCellWitness G c coord.pval coord.nval hocc v,
        by simpa [hv.2] using
          (sizeTwoTriangleFreeCellWitness_spec
            G c coord.pval coord.nval hocc v), hadj⟩
    · intro v₁ hv₁ v₂ hv₂ heq
      apply Subtype.ext
      apply Prod.ext
      · exact heq
      · exact (Finset.mem_filter.mp hv₁).2.trans
          (Finset.mem_filter.mp hv₂).2.symm
    · intro x' hx'
      rw [Finset.mem_filter] at hx'
      obtain ⟨-, w', hw', hadj⟩ := hx'
      have hnot : ¬ sizeTwoReflectionRel q 0 x' y' := by
        intro href
        have hp := (sizeTwoReflectionRel_zero_iff q x' y').mp href
        exact (hhole x' y').mpr hp ⟨w', hw'⟩
      let v : sizeTwoCyclicExteriorCell q 0 := ⟨(x', y'), hnot⟩
      have hvw : sizeTwoTriangleFreeCellWitness G c coord.pval coord.nval hocc v =
          w' := gridWitness_unique G c s coord.pval coord.nval hfree
            (fun x => (coord.p_mem_sign x).2)
            (fun y => (coord.n_mem_sign y).2)
            (sizeTwoTriangleFreeCellWitness_spec
              G c coord.pval coord.nval hocc v) hw'
      refine ⟨v, Finset.mem_filter.mpr ⟨?_, rfl⟩, rfl⟩
      apply (C.mem_neighborFinset u v).mpr
      simpa [w, C, sizeTwoTriangleFreeCyclicGraph, hvw] using hadj
  exact ⟨sizeTwoCyclicExactPermutationCode_of_grid
    q 0 C hCfree hrow hcol⟩

/-- Graph-facing capstone for the connected all-triangle-free sector: one
triangle-free internal edge produces the exact `a = 0` reciprocal cyclic
code, including looplessness and the full cross-agreement law. -/
theorem nonempty_sizeTwoCyclicExactPermutationCode_zero_of_connected_triangleFree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {q : ℕ} [NeZero q] (hq : 5 ≤ q) (hqEven : Even q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = q * 2)
    (hconn : (G.induce c.supp).Connected)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hs_out : ∀ x ∉ c.supp, s x = 0)
    (hsum : ∑ x, s x = 0)
    (hA_in : ∀ x ∈ c.supp,
      ∑ y ∈ G.neighborFinset x, s y = -2 * s x)
    (hDs : ∀ x, ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y =
      ((q : ℤ) - 5) * s x)
    (coord : SizeTwoCycleGridCoordinates G c.supp s q)
    (hseed : ∃ x y : ZMod q,
      (triangleFreeEdgeGraph G).Adj (coord.pval x) (coord.nval y)) :
    Nonempty (SizeTwoCyclicExactPermutationCode q 0) := by
  have hhole :=
    eigenline_hole_eq_internal_of_connected_exists_triangleFreeEdge
      G hfree hq hqEven hreg hcard c hc hconn s hs_in hs_out hsum hA_in hDs
        coord hseed
  exact nonempty_sizeTwoCyclicExactPermutationCode_zero_of_hole_eq_internal
    G hfree hq hreg hcard c hc s hs_in hs_out hsum hA_in hDs coord hhole

end

end Erdos85

#print axioms Erdos85.sizeTwoReflectionRel_zero_iff
#print axioms Erdos85.sizeTwoTriangleFreeCellWitness_injective
#print axioms Erdos85.sizeTwoTriangleFreeCyclicGraph_c4Free
#print axioms Erdos85.nonempty_sizeTwoCyclicExactPermutationCode_zero_of_hole_eq_internal
#print axioms Erdos85.nonempty_sizeTwoCyclicExactPermutationCode_zero_of_connected_triangleFree
