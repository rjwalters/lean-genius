import Proofs.Erdos85SizeTwoEigenlineSectorDichotomy
import Proofs.Erdos85SizeTwoEigenlineCyclicPermutationExactCode

/-!
# Attaching a reflection-circulant sector to the cyclic code

Node: `SIZE-TWO-EIGENLINE(q)` (outline F.3).

This is the parameter-generic graph-to-code bridge: whenever the two missing
cells in every row form the reflection pair `{a, -1-a}`, the occupied ambient
witness graph yields the exact cyclic permutation code with parameter `a`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Choose the unique ambient witness of an occupied cyclic cell. -/
def sizeTwoReflectionCellWitness
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} {a : ZMod q}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (pval nval : ZMod q → V)
    (hocc : ∀ u : sizeTwoCyclicExteriorCell q a,
      ∃ w, IsGridWitness G c pval nval w u.1.1 u.1.2)
    (u : sizeTwoCyclicExteriorCell q a) : V :=
  Classical.choose (hocc u)

theorem sizeTwoReflectionCellWitness_spec
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} {a : ZMod q}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (pval nval : ZMod q → V)
    (hocc : ∀ u : sizeTwoCyclicExteriorCell q a,
      ∃ w, IsGridWitness G c pval nval w u.1.1 u.1.2)
    (u : sizeTwoCyclicExteriorCell q a) :
    IsGridWitness G c pval nval
      (sizeTwoReflectionCellWitness G c pval nval hocc u) u.1.1 u.1.2 :=
  Classical.choose_spec (hocc u)

/-- Ambient adjacency pulled back along the occupied-cell witness map. -/
def sizeTwoReflectionCyclicGraph
    {V : Type*} [Fintype V] [DecidableEq V] {q : ℕ} {a : ZMod q}
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (pval nval : ZMod q → V)
    (hocc : ∀ u : sizeTwoCyclicExteriorCell q a,
      ∃ w, IsGridWitness G c pval nval w u.1.1 u.1.2) :
    SimpleGraph (sizeTwoCyclicExteriorCell q a) :=
  G.comap (sizeTwoReflectionCellWitness G c pval nval hocc)

noncomputable instance sizeTwoReflectionCyclicGraph_decidable
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {a : ZMod q} [NeZero q]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (pval nval : ZMod q → V)
    (hocc : ∀ u : sizeTwoCyclicExteriorCell q a,
      ∃ w, IsGridWitness G c pval nval w u.1.1 u.1.2) :
    DecidableRel (sizeTwoReflectionCyclicGraph G c pval nval hocc).Adj := by
  intro u v
  unfold sizeTwoReflectionCyclicGraph
  infer_instance

/-- The occupied-cell witness map is injective. -/
theorem sizeTwoReflectionCellWitness_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {q : ℕ} {a : ZMod q} [NeZero q] (hq : 5 ≤ q)
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
    (hocc : ∀ u : sizeTwoCyclicExteriorCell q a,
      ∃ w, IsGridWitness G c coord.pval coord.nval w u.1.1 u.1.2) :
    Function.Injective
      (sizeTwoReflectionCellWitness G c coord.pval coord.nval hocc) := by
  intro u v huv
  have hu := sizeTwoReflectionCellWitness_spec
    G c coord.pval coord.nval hocc u
  have hv0 := sizeTwoReflectionCellWitness_spec
    G c coord.pval coord.nval hocc v
  have hv : IsGridWitness G c coord.pval coord.nval
      (sizeTwoReflectionCellWitness G c coord.pval coord.nval hocc u)
      v.1.1 v.1.2 := by
    rw [huv]
    exact hv0
  obtain ⟨p, n, hpS, hnS, hps, hns, heq⟩ := exterior_labels G hfree hq
    hreg hcard c hc s hs_in hs_out hsum hA_in hDs hu.1
  have positive_unique : ∀ z y : ZMod q,
      IsGridWitness G c coord.pval coord.nval
        (sizeTwoReflectionCellWitness G c coord.pval coord.nval hocc u)
        z y → coord.pval z = p := by
    intro z y hz
    have hm : coord.pval z ∈ componentNeighborFinset G
        (secondOrderDefectGraph G) c
        (sizeTwoReflectionCellWitness G c coord.pval coord.nval hocc u) := by
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
        (sizeTwoReflectionCellWitness G c coord.pval coord.nval hocc u)
        x z → coord.nval z = n := by
    intro x z hz
    have hm : coord.nval z ∈ componentNeighborFinset G
        (secondOrderDefectGraph G) c
        (sizeTwoReflectionCellWitness G c coord.pval coord.nval hocc u) := by
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
theorem sizeTwoReflectionCyclicGraph_c4Free
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    {q : ℕ} {a : ZMod q} [NeZero q]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (pval nval : ZMod q → V)
    (hocc : ∀ u : sizeTwoCyclicExteriorCell q a,
      ∃ w, IsGridWitness G c pval nval w u.1.1 u.1.2)
    (hinj : Function.Injective
      (sizeTwoReflectionCellWitness G c pval nval hocc))
    (hfree : ¬ containsC4 V G) :
    ¬ containsC4 _ (sizeTwoReflectionCyclicGraph G c pval nval hocc) := by
  rintro ⟨f, hf, hadj⟩
  apply hfree
  refine ⟨fun i => sizeTwoReflectionCellWitness G c pval nval hocc (f i),
    hinj.comp hf, ?_⟩
  intro i j hij
  exact hadj i j hij

/-- **Reflection-circulant cyclic attachment.**  If the graph-derived missing
cells are exactly a reflection pair, the exterior witness graph supplies
an exact cyclic permutation code with that reflection parameter. -/
theorem nonempty_sizeTwoCyclicExactPermutationCode_of_hole_eq_reflection
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {q : ℕ} {a : ZMod q} [NeZero q] (hq : 5 ≤ q)
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
        sizeTwoReflectionRel q a x y) :
    Nonempty (SizeTwoCyclicExactPermutationCode q a) := by
  classical
  have hocc : ∀ u : sizeTwoCyclicExteriorCell q a,
      ∃ w, IsGridWitness G c coord.pval coord.nval w u.1.1 u.1.2 := by
    intro u
    by_contra hno
    have hp := (hhole u.1.1 u.1.2).mp hno
    exact u.2 hp
  let C := sizeTwoReflectionCyclicGraph G c coord.pval coord.nval hocc
  have hinj := sizeTwoReflectionCellWitness_injective G hfree hq hreg hcard
    c hc s hs_in hs_out hsum hA_in hDs coord hocc
  have hCfree : ¬ containsC4 (sizeTwoCyclicExteriorCell q a) C :=
    sizeTwoReflectionCyclicGraph_c4Free G c coord.pval coord.nval
      hocc hinj hfree
  have hrow : ∀ (u : sizeTwoCyclicExteriorCell q a) (x' : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = x').card =
        if u.1.2 = x' ∨ u.1.2 = x' - 1 then 0 else 1 := by
    intro u x'
    let w := sizeTwoReflectionCellWitness G c coord.pval coord.nval hocc u
    have hw := sizeTwoReflectionCellWitness_spec
      G c coord.pval coord.nval hocc u
    have hraw := cell_row_neighbors_card G c s coord.pval coord.nval hfree hq
      hreg hcard hc hs_in hs_out hsum hA_in hDs coord.p_mem_sign
      coord.n_mem_sign coord.n_injective coord.n_surjective coord.adj_iff hw x'
    rw [← hraw]
    apply Finset.card_bij (fun v _ => v.1.2)
    · intro v hv
      rw [Finset.mem_filter] at hv ⊢
      have hadj : G.Adj w
          (sizeTwoReflectionCellWitness G c coord.pval coord.nval hocc v) :=
        (C.mem_neighborFinset u v).mp hv.1
      exact ⟨Finset.mem_univ _,
        sizeTwoReflectionCellWitness G c coord.pval coord.nval hocc v,
        by simpa [hv.2] using
          (sizeTwoReflectionCellWitness_spec
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
      have hnot : ¬ sizeTwoReflectionRel q a x' y' := by
        intro href
        exact (hhole x' y').mpr href ⟨w', hw'⟩
      let v : sizeTwoCyclicExteriorCell q a := ⟨(x', y'), hnot⟩
      have hvw : sizeTwoReflectionCellWitness G c coord.pval coord.nval hocc v =
          w' := gridWitness_unique G c s coord.pval coord.nval hfree
            (fun x => (coord.p_mem_sign x).2)
            (fun y => (coord.n_mem_sign y).2)
            (sizeTwoReflectionCellWitness_spec
              G c coord.pval coord.nval hocc v) hw'
      refine ⟨v, Finset.mem_filter.mpr ⟨?_, rfl⟩, rfl⟩
      apply (C.mem_neighborFinset u v).mpr
      simpa [w, C, sizeTwoReflectionCyclicGraph, hvw] using hadj
  have hcol : ∀ (u : sizeTwoCyclicExteriorCell q a) (y' : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = y').card =
        if u.1.1 = y' ∨ u.1.1 = y' + 1 then 0 else 1 := by
    intro u y'
    let w := sizeTwoReflectionCellWitness G c coord.pval coord.nval hocc u
    have hw := sizeTwoReflectionCellWitness_spec
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
          (sizeTwoReflectionCellWitness G c coord.pval coord.nval hocc v) :=
        (C.mem_neighborFinset u v).mp hv.1
      exact ⟨Finset.mem_univ _,
        sizeTwoReflectionCellWitness G c coord.pval coord.nval hocc v,
        by simpa [hv.2] using
          (sizeTwoReflectionCellWitness_spec
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
      have hnot : ¬ sizeTwoReflectionRel q a x' y' := by
        intro href
        exact (hhole x' y').mpr href ⟨w', hw'⟩
      let v : sizeTwoCyclicExteriorCell q a := ⟨(x', y'), hnot⟩
      have hvw : sizeTwoReflectionCellWitness G c coord.pval coord.nval hocc v =
          w' := gridWitness_unique G c s coord.pval coord.nval hfree
            (fun x => (coord.p_mem_sign x).2)
            (fun y => (coord.n_mem_sign y).2)
            (sizeTwoReflectionCellWitness_spec
              G c coord.pval coord.nval hocc v) hw'
      refine ⟨v, Finset.mem_filter.mpr ⟨?_, rfl⟩, rfl⟩
      apply (C.mem_neighborFinset u v).mpr
      simpa [w, C, sizeTwoReflectionCyclicGraph, hvw] using hadj
  exact ⟨sizeTwoCyclicExactPermutationCode_of_grid
    q a C hCfree hrow hcol⟩

/-- **Connected-sector graph-to-code capstone.** Every connected normalized
size-two eigenline sector produces an exact cyclic code, for the reflection
parameter supplied by the sector dichotomy. -/
theorem exists_nonempty_sizeTwoCyclicExactPermutationCode_of_connected
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
    (coord : SizeTwoCycleGridCoordinates G c.supp s q) :
    ∃ a : ZMod q, a ≠ -1 ∧
      Nonempty (SizeTwoCyclicExactPermutationCode q a) := by
  obtain ⟨a, ha, hhole⟩ := eigenline_hole_reflectionCirculant_of_connected
    G hfree hq hqEven hreg hcard c hc hconn s hs_in hs_out hsum hA_in hDs
      coord
  refine ⟨a, ha, ?_⟩
  apply nonempty_sizeTwoCyclicExactPermutationCode_of_hole_eq_reflection
    G hfree hq hreg hcard c hc s hs_in hs_out hsum hA_in hDs coord
  intro x y
  simpa [sizeTwoReflectionRel] using hhole x y


end

end Erdos85

#print axioms Erdos85.sizeTwoReflectionCellWitness_injective
#print axioms Erdos85.sizeTwoReflectionCyclicGraph_c4Free
#print axioms Erdos85.nonempty_sizeTwoCyclicExactPermutationCode_of_hole_eq_reflection
#print axioms Erdos85.exists_nonempty_sizeTwoCyclicExactPermutationCode_of_connected
