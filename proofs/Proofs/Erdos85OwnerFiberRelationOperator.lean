import Proofs.Erdos85OwnerFiberOperator

/-!
# Owner-fiber operators over a relation with loops

The exterior adjacency in the saturated minimum-layer branch is not a cover
of a simple graph: above a child vertex there is a matching inside the same
owner fiber.  It is instead a locally bijective lift of the *reflexive*
complement of the child adjacency relation.  This file supplies the matrix
interface for such covers.
-/

namespace Erdos85

noncomputable section

open Matrix
open scoped Matrix

def relationMatrix
    {Y K : Type*} [Zero K] [One K] (R : Y → Y → Prop)
    [DecidableRel R] : Matrix Y Y K :=
  fun a b => if R a b then 1 else 0

/-- The reflexive nonadjacency relation of a simple graph is represented by
the all-ones matrix minus adjacency. -/
theorem relationMatrix_not_adj_eq_ones_sub_adjMatrix
    {Y K : Type*} [Fintype Y] [DecidableEq Y] [Ring K]
    (H : SimpleGraph Y) [DecidableRel H.Adj] :
    relationMatrix (K := K) (fun a b => ¬H.Adj a b) =
      (fun _ _ => (1 : K)) - H.adjMatrix K := by
  ext a b
  simp only [relationMatrix, Matrix.sub_apply, SimpleGraph.adjMatrix_apply]
  by_cases h : H.Adj a b <;> simp [h]

theorem transpose_relationMatrix
    {Y K : Type*} [Zero K] [One K] (R : Y → Y → Prop)
    [DecidableRel R] (hsymm : Symmetric R) :
    Matrix.transpose (relationMatrix (K := K) R) = relationMatrix R := by
  ext a b
  simp only [Matrix.transpose_apply, relationMatrix]
  by_cases hab : R a b
  · rw [if_pos hab, if_pos (hsymm hab)]
  · have hba : ¬R b a := fun h => hab (hsymm h)
    rw [if_neg hab, if_neg hba]

/-- A locally bijective lift of a possibly reflexive relation intertwines
adjacency with the transpose of the owner-incidence matrix. -/
theorem adjMatrix_mul_ownerIncidence_transpose_relation
    {X Y K : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] [Semiring K]
    (P : SimpleGraph X) [DecidableRel P.Adj]
    (R : Y → Y → Prop) [DecidableRel R]
    (owner : X → Y)
    (hmap : ∀ {x z}, P.Adj x z → R (owner x) (owner z))
    (hlift : ∀ (x : X) (b : Y), R (owner x) b →
      ∃! z : X, P.Adj x z ∧ owner z = b) :
    P.adjMatrix K * Matrix.transpose (ownerIncidenceMatrix (K := K) owner) =
      Matrix.transpose (ownerIncidenceMatrix (K := K) owner) *
        relationMatrix (K := K) R := by
  ext x b
  have hleft :
      (P.adjMatrix K *
        Matrix.transpose (ownerIncidenceMatrix (K := K) owner)) x b =
      ((Finset.univ.filter fun z => P.Adj x z ∧ owner z = b).card : K) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply,
      ownerIncidenceMatrix, SimpleGraph.adjMatrix_apply]
    calc
      (∑ z, (if P.Adj x z then 1 else 0) *
          if owner z = b then 1 else 0) =
          ∑ z, if P.Adj x z ∧ owner z = b then (1 : K) else 0 := by
            apply Finset.sum_congr rfl
            intro z _
            by_cases hp : P.Adj x z <;>
              by_cases ho : owner z = b <;> simp [hp, ho]
      _ = _ := by
        simpa using (Finset.sum_boole (R := K)
          (fun z : X => P.Adj x z ∧ owner z = b) Finset.univ)
  rw [hleft]
  have hright :
      (Matrix.transpose (ownerIncidenceMatrix (K := K) owner) *
        relationMatrix (K := K) R) x b =
      if R (owner x) b then 1 else 0 := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply,
      ownerIncidenceMatrix, relationMatrix]
    rw [Finset.sum_eq_single (owner x)]
    · by_cases hb : R (owner x) b <;> simp [hb]
    · intro a _ ha
      have hne : owner x ≠ a := Ne.symm ha
      simp [hne]
    · simp
  rw [hright]
  by_cases hb : R (owner x) b
  · rw [if_pos hb]
    obtain ⟨z, hz, huniq⟩ := hlift x b hb
    have hfilter :
        Finset.univ.filter (fun w => P.Adj x w ∧ owner w = b) = {z} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_singleton]
      constructor
      · exact fun hw => huniq w hw
      · intro hw
        subst w
        exact hz
    rw [hfilter]
    simp
  · rw [if_neg hb]
    have hempty :
        Finset.univ.filter (fun z => P.Adj x z ∧ owner z = b) = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      rintro ⟨z, hz⟩
      have hz' := (Finset.mem_filter.mp hz).2
      exact hb (by simpa [hz'.2] using hmap hz'.1)
    rw [hempty]
    simp

/-- For a symmetric base relation, its locally bijective lift commutes with
the owner-fiber Gram operator `CᵀC`.  Unlike the simple-graph version, this
applies to reflexive relations and hence to the saturated exterior graph. -/
theorem adjMatrix_comm_ownerFiberGram_relation
    {X Y K : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] [CommSemiring K]
    (P : SimpleGraph X) [DecidableRel P.Adj]
    (R : Y → Y → Prop) [DecidableRel R]
    (owner : X → Y) (hsymm : Symmetric R)
    (hmap : ∀ {x z}, P.Adj x z → R (owner x) (owner z))
    (hlift : ∀ (x : X) (b : Y), R (owner x) b →
      ∃! z : X, P.Adj x z ∧ owner z = b) :
    P.adjMatrix K *
        (Matrix.transpose (ownerIncidenceMatrix (K := K) owner) *
          ownerIncidenceMatrix (K := K) owner) =
      (Matrix.transpose (ownerIncidenceMatrix (K := K) owner) *
          ownerIncidenceMatrix (K := K) owner) * P.adjMatrix K := by
  let C := ownerIncidenceMatrix (K := K) owner
  let B := relationMatrix (K := K) R
  have hPC : P.adjMatrix K * Matrix.transpose C = Matrix.transpose C * B :=
    adjMatrix_mul_ownerIncidence_transpose_relation P R owner hmap hlift
  have hBT : Matrix.transpose B = B := by
    exact transpose_relationMatrix R hsymm
  have hCP : C * P.adjMatrix K = B * C := by
    have h := congrArg Matrix.transpose hPC
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
      SimpleGraph.transpose_adjMatrix] at h
    rw [hBT] at h
    exact h
  calc
    P.adjMatrix K * (Matrix.transpose C * C) =
        (P.adjMatrix K * Matrix.transpose C) * C := by
          rw [Matrix.mul_assoc]
    _ = (Matrix.transpose C * B) * C := by rw [hPC]
    _ = Matrix.transpose C * (B * C) := by rw [Matrix.mul_assoc]
    _ = Matrix.transpose C * (C * P.adjMatrix K) := by rw [hCP]
    _ = (Matrix.transpose C * C) * P.adjMatrix K := by
      rw [Matrix.mul_assoc]

/-- The original exterior adjacency is a locally bijective lift of the
reflexive child-nonadjacency relation.  Thus every child nonedge, including
the diagonal, carries one perfect matching of owner fibers, while child
edges carry empty blocks. -/
theorem exists_minimumLayer_saturated_exteriorRelationCover
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hspos : 0 < s) (hsd : s < d)
    (hsat : d = (s - 1) * (s - 1) + 3) :
    let D := secondOrderDefectGraph G
    let X := minimumLayerExteriorVertex D c₀
    let H := minimumLayerGraph G D c₀
    let E := minimumLayerExternalNeighborFinset G D c₀
    ∃ owner : X → minimumLayerVertex D c₀,
      (∀ z : X, z.1 ∈ E (owner z)) ∧
      (∀ {z w : X}, (G.comap Subtype.val).Adj z w →
        ¬H.Adj (owner z) (owner w)) ∧
      (∀ (z : X) (b : minimumLayerVertex D c₀),
        ¬H.Adj (owner z) b →
          ∃! w : X, (G.comap Subtype.val).Adj z w ∧ owner w = b) := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let X := minimumLayerExteriorVertex D c₀
  let H := minimumLayerGraph G D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  have hownerExists : ∀ z : X, ∃! a : minimumLayerVertex D c₀,
      z.1 ∈ E a := by
    intro z
    exact minimumLayer_existsUnique_externalOwner_of_saturated
      G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat z.2
  let owner : X → minimumLayerVertex D c₀ := fun z =>
    Classical.choose (hownerExists z)
  have hownerMem : ∀ z : X, z.1 ∈ E (owner z) := fun z =>
    (Classical.choose_spec (hownerExists z)).1
  have hownerUnique : ∀ (z : X) (a : minimumLayerVertex D c₀),
      z.1 ∈ E a → a = owner z := by
    intro z a hza
    exact (Classical.choose_spec (hownerExists z)).2 a hza
  refine ⟨owner, hownerMem, ?_, ?_⟩
  · intro z w hzw hH
    have hempty := minimumLayer_saturated_externalBlock_eq_empty_of_adj
      G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
        (owner w) (owner z) (hownerMem z) hH.symm
    have hw : w.1 ∈ G.neighborFinset z.1 ∩ E (owner w) :=
      Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset z.1 w.1).mpr hzw, hownerMem w⟩
    rw [hempty] at hw
    exact Finset.notMem_empty w.1 hw
  · intro z b hzb
    obtain ⟨r, hr, hruniq⟩ :=
      minimumLayer_saturated_externalBlock_existsUnique_of_not_adj
        G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
          b (owner z) (hownerMem z) (fun h => hzb h.symm)
    have hrOutside : r ∉ minimumLayerImageFinset D c₀ :=
      (Finset.mem_sdiff.mp hr.1).2
    let w : X := ⟨r, hrOutside⟩
    have hwowner : owner w = b := (hownerUnique w b hr.1).symm
    refine ⟨w, ⟨hr.2, hwowner⟩, ?_⟩
    intro w' hw'
    apply Subtype.ext
    change w'.1 = r
    have hw'mem : w'.1 ∈ E b := by
      rw [← hw'.2]
      exact hownerMem w'
    exact hruniq w'.1 ⟨hw'mem, hw'.1⟩

/-- Graph-facing operator bridge for the saturated exterior. -/
theorem exists_minimumLayer_saturated_exteriorAdjacency_intertwining
    {V K : Type*} [Fintype V] [DecidableEq V] [CommSemiring K]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hspos : 0 < s) (hsd : s < d)
    (hsat : d = (s - 1) * (s - 1) + 3) :
    let D := secondOrderDefectGraph G
    let X := minimumLayerExteriorVertex D c₀
    let H := minimumLayerGraph G D c₀
    ∃ owner : X → minimumLayerVertex D c₀,
      (G.comap (fun z : X => z.1)).adjMatrix K *
          Matrix.transpose (ownerIncidenceMatrix (K := K) owner) =
        Matrix.transpose (ownerIncidenceMatrix (K := K) owner) *
          relationMatrix (K := K) (fun a b => ¬H.Adj a b) := by
  classical
  dsimp only
  obtain ⟨owner, _hmem, hmap, hlift⟩ :=
    exists_minimumLayer_saturated_exteriorRelationCover
      G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
  refine ⟨owner, ?_⟩
  exact adjMatrix_mul_ownerIncidence_transpose_relation
    (G.comap (fun z : minimumLayerExteriorVertex
      (secondOrderDefectGraph G) c₀ => z.1)) (fun a b =>
      ¬(minimumLayerGraph G (secondOrderDefectGraph G) c₀).Adj a b)
      owner hmap hlift

end

end Erdos85
