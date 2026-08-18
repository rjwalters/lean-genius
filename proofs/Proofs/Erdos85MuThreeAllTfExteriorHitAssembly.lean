import Proofs.Erdos85MuThreeAllTfExteriorHitReindex

/-! # Assemble ambient signed-grid hit laws on the induced exterior graph -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The existing ambient positive/negative image laws, transported through an
internal coordinate model, give the certificate-facing exterior hit interface. -/
def mu3ExteriorHitImages_of_ambient_signed_images
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (s : V → ℤ)
    (shape : Mu3AllTfShape)
    (label : {u : V // u ∉ c.supp} →
      {z : V // z ∈ c.supp ∧ s z = 1} ×
        {z : V // z ∈ c.supp ∧ s z = -1})
    (hadj : ∀ u, G.Adj u.1 (label u).1.1 ∧
      G.Adj u.1 (label u).2.1)
    (model : Mu3InternalCoordinateModel (G.induce c.supp)
      {z : V // z ∈ c.supp ∧ s z = 1}
      {z : V // z ∈ c.supp ∧ s z = -1}
      (fun p => ⟨p.1, p.2.1⟩) (fun n => ⟨n.1, n.2.1⟩) shape)
    (e : Fin 48 ≃ {u : V // u ∉ c.supp})
    (hcoord : ∀ i,
      (model.row (label (e i)).1).val * 8 +
          (model.column (label (e i)).2).val =
        (mu3AllTfCells shape).getD i.val 0)
    (hpositive : ∀ u,
      (Finset.univ.filter fun v : {v : V // v ∉ c.supp} =>
          G.Adj u.1 v.1).image (fun v => (label v).1) =
        Finset.univ.filter fun p : {z : V // z ∈ c.supp ∧ s z = 1} =>
          ¬ G.Adj p.1 (label u).2.1)
    (hnegative : ∀ u,
      (Finset.univ.filter fun v : {v : V // v ∉ c.supp} =>
          G.Adj u.1 v.1).image (fun v => (label v).2) =
        Finset.univ.filter fun n : {z : V // z ∈ c.supp ∧ s z = -1} =>
          ¬ G.Adj n.1 (label u).1.1) :
    Mu3ExteriorHitImages shape
      (G.induce {u : V | u ∉ c.supp}) e where
  rowCoord u := model.row (label u).1
  columnCoord u := model.column (label u).2
  coord := hcoord
  rowInjective u := by
    intro v hv w hw hvw
    have hrook :=
      (c4Free_exteriorGridLabel_neighbor_coordinate_injective
        G hfree c s label hadj u).1
    let v' : {v : {v : V // v ∉ c.supp} // G.Adj u.1 v.1} :=
      ⟨v, hv⟩
    let w' : {v : {v : V // v ∉ c.supp} // G.Adj u.1 v.1} :=
      ⟨w, hw⟩
    have hlabel : (label v).1 = (label w).1 :=
      model.row.injective hvw
    have heq : v' = w' := hrook hlabel
    exact congrArg (fun z => z.1) heq
  columnInjective u := by
    intro v hv w hw hvw
    have hrook :=
      (c4Free_exteriorGridLabel_neighbor_coordinate_injective
        G hfree c s label hadj u).2
    let v' : {v : {v : V // v ∉ c.supp} // G.Adj u.1 v.1} :=
      ⟨v, hv⟩
    let w' : {v : {v : V // v ∉ c.supp} // G.Adj u.1 v.1} :=
      ⟨w, hw⟩
    have hlabel : (label v).2 = (label w).2 :=
      model.column.injective hvw
    have heq : v' = w' := hrook hlabel
    exact congrArg (fun z => z.1) heq
  rowImage u := by
    have hp := hpositive u
    ext x
    constructor
    · intro hx
      obtain ⟨v, hv, hvx⟩ := Finset.mem_image.mp hx
      have hvAdj : G.Adj u.1 v.1 := (Finset.mem_filter.mp hv).2
      have hpMem : (label v).1 ∈
          Finset.univ.filter fun p : {z : V // z ∈ c.supp ∧ s z = 1} =>
            ¬ G.Adj p.1 (label u).2.1 := by
        rw [← hp]
        exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
      have hnot : ¬ G.Adj (label v).1.1 (label u).2.1 :=
        (Finset.mem_filter.mp hpMem).2
      have hnotInternal :
          ¬ mu3AllTfInternal shape x.val
            (model.column (label u).2).val := by
        intro hi
        have hind := (model.hole_iff (label v).1 (label u).2).2 (by
          simpa [hvx] using hi)
        exact hnot hind
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnotInternal⟩
    · intro hx
      have hnotInternal := (Finset.mem_filter.mp hx).2
      let p := model.row.symm x
      have hnot : ¬ G.Adj p.1 (label u).2.1 := by
        intro hadjpn
        have hi := (model.hole_iff p (label u).2).1 hadjpn
        exact hnotInternal (by simpa [p] using hi)
      have hpMem : p ∈
          Finset.univ.filter fun p : {z : V // z ∈ c.supp ∧ s z = 1} =>
            ¬ G.Adj p.1 (label u).2.1 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnot⟩
      rw [← hp] at hpMem
      obtain ⟨v, hv, hvp⟩ := Finset.mem_image.mp hpMem
      exact Finset.mem_image.mpr ⟨v, hv, by
        calc
          model.row (label v).1 = model.row p := congrArg model.row hvp
          _ = x := model.row.apply_symm_apply x⟩
  columnImage u := by
    have hn := hnegative u
    ext y
    constructor
    · intro hy
      obtain ⟨v, hv, hvy⟩ := Finset.mem_image.mp hy
      have hnMem : (label v).2 ∈
          Finset.univ.filter fun n : {z : V // z ∈ c.supp ∧ s z = -1} =>
            ¬ G.Adj n.1 (label u).1.1 := by
        rw [← hn]
        exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
      have hnot : ¬ G.Adj (label v).2.1 (label u).1.1 :=
        (Finset.mem_filter.mp hnMem).2
      have hnotInternal :
          ¬ mu3AllTfInternal shape (model.row (label u).1).val y.val := by
        intro hi
        have hind := (model.hole_iff (label u).1 (label v).2).2 (by
          simpa [hvy] using hi)
        exact hnot hind.symm
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnotInternal⟩
    · intro hy
      have hnotInternal := (Finset.mem_filter.mp hy).2
      let n := model.column.symm y
      have hnot : ¬ G.Adj n.1 (label u).1.1 := by
        intro hadjnp
        have hi := (model.hole_iff (label u).1 n).1 hadjnp.symm
        exact hnotInternal (by simpa [n] using hi)
      have hnMem : n ∈
          Finset.univ.filter fun n : {z : V // z ∈ c.supp ∧ s z = -1} =>
            ¬ G.Adj n.1 (label u).1.1 :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnot⟩
      rw [← hn] at hnMem
      obtain ⟨v, hv, hvn⟩ := Finset.mem_image.mp hnMem
      exact Finset.mem_image.mpr ⟨v, hv, by
        calc
          model.column (label v).2 = model.column n := congrArg model.column hvn
          _ = y := model.column.apply_symm_apply y⟩

theorem not_containsC4_induce_set
    {V : Type*} (G : SimpleGraph V) (S : Set V)
    (hfree : ¬ containsC4 V G) :
    ¬ containsC4 S (G.induce S) := by
  rintro ⟨f, hf, hadj⟩
  apply hfree
  exact ⟨fun i => (f i).1, Subtype.val_injective.comp hf,
    fun i j hij => hadj i j hij⟩

/-- Once the ambient signed-image laws have been assembled, the checked
all-triangle-free certificate contradicts ambient C4-freeness immediately. -/
theorem false_of_c4Free_mu3AllTf_ambientHitImages
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (shape : Mu3AllTfShape)
    (e : Fin 48 ≃ {u : V // u ∉ c.supp})
    (h : Mu3ExteriorHitImages shape
      (G.induce {u : V | u ∉ c.supp}) e) : False :=
  false_of_c4Free_mu3AllTfGraphGridHitCounts shape
    (G.induce {u : V | u ∉ c.supp})
    (not_containsC4_induce_set G {u : V | u ∉ c.supp} hfree) e
    (mu3GraphGridHitCounts_of_exteriorHitImages shape
      (G.induce {u : V | u ∉ c.supp}) e h)

#print axioms false_of_c4Free_mu3AllTf_ambientHitImages

end

end Erdos85
