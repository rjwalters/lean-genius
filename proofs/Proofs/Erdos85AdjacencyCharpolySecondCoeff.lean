import Mathlib

/-!
# The second adjacency characteristic coefficient

For a simple graph, every two-vertex principal adjacency minor is zero on a
nonedge and minus one on an edge.  Combining this with the principal-minor
formula for the characteristic polynomial identifies its second coefficient.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem det_adjMatrix_submatrix_card_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (hs : s.card = 2) :
    ((G.adjMatrix ℚ).submatrix
        (Subtype.val : s → V) (Subtype.val : s → V)).det =
      if ∃ x ∈ s, ∃ y ∈ s, G.Adj x y then -1 else 0 := by
  classical
  let e : s ≃ Fin 2 := s.equivFinOfCardEq hs
  let x : s := e.symm 0
  let y : s := e.symm 1
  have hxy : x ≠ y := by
    intro h
    have := e.symm.injective h
    norm_num at this
  have hpred : (∃ u ∈ s, ∃ v ∈ s, G.Adj u v) ↔ G.Adj x.1 y.1 := by
    constructor
    · rintro ⟨u, hu, v, hv, huv⟩
      let u' : s := ⟨u, hu⟩
      let v' : s := ⟨v, hv⟩
      have huvne : u' ≠ v' := by
        intro h
        have huvEq : u = v := congrArg Subtype.val h
        subst v
        exact G.loopless.irrefl u huv
      have heu : e u' = 0 ∨ e u' = 1 := by
        have := (e u').isLt
        omega
      have hev : e v' = 0 ∨ e v' = 1 := by
        have := (e v').isLt
        omega
      rcases heu with heu | heu <;> rcases hev with hev | hev
      · exact False.elim (huvne (e.injective (heu.trans hev.symm)))
      · have hu'x : u' = x :=
          e.injective (heu.trans (e.apply_symm_apply 0).symm)
        have hv'y : v' = y :=
          e.injective (hev.trans (e.apply_symm_apply 1).symm)
        have hu : u = x.1 := congrArg Subtype.val hu'x
        have hv : v = y.1 := congrArg Subtype.val hv'y
        simpa [hu, hv] using huv
      · have hu'y : u' = y :=
          e.injective (heu.trans (e.apply_symm_apply 1).symm)
        have hv'x : v' = x :=
          e.injective (hev.trans (e.apply_symm_apply 0).symm)
        have hu : u = y.1 := congrArg Subtype.val hu'y
        have hv : v = x.1 := congrArg Subtype.val hv'x
        simpa [hu, hv, G.adj_comm] using huv
      · exact False.elim (huvne (e.injective (heu.trans hev.symm)))
    · intro h
      exact ⟨x.1, x.2, y.1, y.2, h⟩
  simp only [hpred]
  rw [← Matrix.det_reindex_self e
    ((G.adjMatrix ℚ).submatrix
      (Subtype.val : s → V) (Subtype.val : s → V))]
  rw [Matrix.det_fin_two]
  simp [Matrix.reindex_apply, SimpleGraph.adjMatrix_apply, x, y,
    G.adj_comm]
  by_cases h : G.Adj (e.symm 0).1 (e.symm 1).1 <;> simp [h]

theorem adjMatrix_charpoly_secondCoeff_eq_neg_adjacentPairCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 2 ≤ Fintype.card V) :
    (G.adjMatrix ℚ).charpoly.coeff (Fintype.card V - 2) =
      -(((Finset.univ.powersetCard 2).filter
        (fun s => ∃ x ∈ s, ∃ y ∈ s, G.Adj x y)).card : ℚ) := by
  rw [Matrix.charpoly_coeff_eq_sum_minors (G.adjMatrix ℚ) 2 hcard]
  norm_num
  let P : Finset V → Prop := fun s => ∃ x ∈ s, ∃ y ∈ s, G.Adj x y
  have hminor :
      (∑ s ∈ Finset.univ.powersetCard 2,
          ((G.adjMatrix ℚ).submatrix
            (Subtype.val : s → V) (Subtype.val : s → V)).det) =
        ∑ s ∈ Finset.univ.powersetCard 2,
          if P s then (-1 : ℚ) else 0 := by
    apply Finset.sum_congr rfl
    intro s hs
    rw [det_adjMatrix_submatrix_card_two G s
      (Finset.mem_powersetCard.mp hs).2]
  have hsum :
      (∑ s ∈ Finset.univ.powersetCard 2,
          if P s then (-1 : ℚ) else 0) =
        ∑ _s ∈ (Finset.univ.powersetCard 2).filter P, (-1 : ℚ) := by
    rw [Finset.sum_filter]
  rw [hminor, hsum]
  simp [P]

theorem card_adjacentPairFinset_eq_card_edgeFinset
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ((Finset.univ.powersetCard 2).filter
        (fun s => ∃ x ∈ s, ∃ y ∈ s, G.Adj x y)).card =
      G.edgeFinset.card := by
  classical
  let f : G.edgeFinset → Finset V := fun e => (e.1 : Sym2 V).toFinset
  have hf : Function.Injective f := by
    intro e₁ e₂ h
    apply Subtype.ext
    apply Sym2.ext
    intro x
    rw [← Sym2.mem_toFinset, ← Sym2.mem_toFinset]
    exact Finset.ext_iff.mp h x
  have himage :
      G.edgeFinset.attach.image f =
        (Finset.univ.powersetCard 2).filter
          (fun s => (∃ x ∈ s, ∃ y ∈ s, G.Adj x y)) := by
    ext s
    constructor
    · intro hs
      rw [Finset.mem_image] at hs
      obtain ⟨e, _he, rfl⟩ := hs
      rcases e with ⟨eval, heval⟩
      induction eval using Sym2.inductionOn with
      | _ x y =>
          have hxy : G.Adj x y := by
            simpa [SimpleGraph.mem_edgeSet] using
              (G.mem_edgeFinset.mp heval)
          have hxyne : x ≠ y := fun h => G.loopless.irrefl x (h ▸ hxy)
          rw [Finset.mem_filter]
          constructor
          · rw [Finset.mem_powersetCard]
            exact ⟨by simp, by simp [f, Sym2.toFinset_mk_eq, hxyne]⟩
          · exact ⟨x, by simp [f, Sym2.toFinset_mk_eq],
              y, by simp [f, Sym2.toFinset_mk_eq], hxy⟩
    · intro hs
      rw [Finset.mem_filter, Finset.mem_powersetCard] at hs
      obtain ⟨_ssub, hscard⟩ := hs.1
      obtain ⟨x, hx, y, hy, hxy⟩ := hs.2
      have hxyne : x ≠ y := fun h => G.loopless.irrefl x (h ▸ hxy)
      have hsxy : s = {x, y} := by
        symm
        apply Finset.eq_of_subset_of_card_le
        · intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact hx
          · exact hy
        · rw [Finset.card_pair hxyne, hscard]
      let e : G.edgeFinset := ⟨s(x, y), by
        rw [G.mem_edgeFinset]
        simpa [SimpleGraph.mem_edgeSet] using hxy⟩
      apply Finset.mem_image.mpr
      refine ⟨e, Finset.mem_attach _ _, ?_⟩
      simpa [f, e, Sym2.toFinset_mk_eq] using hsxy.symm
  rw [← himage, Finset.card_image_of_injective _ hf]
  simp

/-- Newton's second-coefficient identity specialized to a simple adjacency
matrix, in denominator-free form. -/
theorem twice_adjMatrix_charpoly_secondCoeff_eq_neg_sum_degrees
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 2 ≤ Fintype.card V) :
    2 * (G.adjMatrix ℚ).charpoly.coeff (Fintype.card V - 2) =
      -(∑ x : V, (G.degree x : ℚ)) := by
  rw [adjMatrix_charpoly_secondCoeff_eq_neg_adjacentPairCount G hcard,
    card_adjacentPairFinset_eq_card_edgeFinset G]
  have hhandshake := G.sum_degrees_eq_twice_card_edges
  norm_cast at hhandshake ⊢
  omega

end

end Erdos85
