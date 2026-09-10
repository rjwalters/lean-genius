import Proofs.Erdos85TriangleMatchingCover

/-! Preserve covering-triangle witnesses when extracting a matching. -/
namespace Erdos85
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Edges supported by a member of a finite triangle family. -/
def triangleWitnessGraph (K : Finset (Finset V)) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ∃ t ∈ K, u ∈ t ∧ v ∈ t
  symm := by
    constructor
    intro u v h
    obtain ⟨hne, t, ht, hu, hv⟩ := h
    exact ⟨hne.symm, t, ht, hv, hu⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

noncomputable instance (K : Finset (Finset V)) :
    DecidableRel (triangleWitnessGraph K).Adj := Classical.decRel _

/-- Each extracted edge belongs to one of the actual covering triangles,
which lets later bounds use additional restrictions on such edges. -/
theorem triangle_cover_extract_witnessed_disjoint_pairs
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (K : Finset (Finset V))
    (hK : K ⊆ G.cliqueFinset 3)
    (hcover : ∀ v ∈ S, ∃ t ∈ K, v ∈ t)
    (hcap : ∀ t ∈ K, (S ∩ t).card ≤ 2) :
    ∃ P : Finset (Finset V),
      (∀ e ∈ P, G.IsNClique 2 e ∧ e ⊆ S ∧ ∃ t ∈ K, e ⊆ t) ∧
      (∀ e ∈ P, ∀ d ∈ P, e ≠ d → Disjoint e d) ∧
      S.card ≤ K.card + P.card := by
  classical
  let H := triangleWitnessGraph K
  have hKH : K ⊆ H.cliqueFinset 3 := by
    intro t ht
    apply H.mem_cliqueFinset_iff.mpr
    refine ⟨?_, (G.mem_cliqueFinset_iff.mp (hK ht)).card_eq⟩
    intro u hu v hv hne
    exact ⟨hne, t, ht, hu, hv⟩
  obtain ⟨P, hP, hdis, hcount⟩ :=
    triangle_cover_extract_disjoint_pairs H S K hKH hcover hcap
  refine ⟨P, ?_, hdis, hcount⟩
  intro e he
  obtain ⟨hc, hs⟩ := hP e he
  obtain ⟨u, v, hne, heq⟩ := Finset.card_eq_two.mp hc.card_eq
  have huv : H.Adj u v := hc.isClique (by simp [heq]) (by simp [heq]) hne
  obtain ⟨_, t, ht, hu, hv⟩ := huv
  have het : e ⊆ t := by
    intro x hx
    rw [heq] at hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hu
    · exact Finset.mem_singleton.mp hx ▸ hv
  refine ⟨⟨?_, hc.card_eq⟩, hs, t, ht, het⟩
  intro a ha b hb hab
  exact (G.mem_cliqueFinset_iff.mp (hK ht)).isClique (het ha) (het hb) hab


/-- If every covering triangle exits E, all matching edges have a common
neighbor outside E. This is the additional exterior-pair restriction. -/
theorem triangle_cover_extract_exterior_disjoint_pairs
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (E S : Finset V) (K : Finset (Finset V))
    (hSE : S ⊆ E)
    (hK : K ⊆ G.cliqueFinset 3)
    (hcover : ∀ v ∈ S, ∃ t ∈ K, v ∈ t)
    (hexit : ∀ t ∈ K, ¬ t ⊆ E) :
    ∃ P : Finset (Finset V),
      (∀ e ∈ P, G.IsNClique 2 e ∧ e ⊆ S ∧
        ∃ z ∉ E, ∀ v ∈ e, G.Adj v z) ∧
      (∀ e ∈ P, ∀ d ∈ P, e ≠ d → Disjoint e d) ∧
      S.card ≤ K.card + P.card := by
  classical
  have hcap : ∀ t ∈ K, (S ∩ t).card ≤ 2 := by
    intro t ht
    have hc := (G.mem_cliqueFinset_iff.mp (hK ht)).card_eq
    by_contra hn
    have heq : S ∩ t = t := Finset.eq_of_subset_of_card_le
      Finset.inter_subset_right (by omega)
    apply hexit t ht
    intro v hv
    have hvs : v ∈ S := Finset.mem_of_mem_inter_left (heq.symm ▸ hv)
    exact hSE hvs
  obtain ⟨P, hP, hdis, hcount⟩ :=
    triangle_cover_extract_witnessed_disjoint_pairs G S K hK hcover hcap
  refine ⟨P, ?_, hdis, hcount⟩
  intro e he
  obtain ⟨hc, hs, t, ht, het⟩ := hP e he
  obtain ⟨z, hzt, hzE⟩ := Finset.not_subset.mp (hexit t ht)
  refine ⟨hc, hs, z, hzE, ?_⟩
  intro v hv
  exact (G.mem_cliqueFinset_iff.mp (hK ht)).isClique (het hv) hzt
    (fun heq => hzE (heq ▸ hSE (hs hv)))

end Erdos85
#print axioms Erdos85.triangle_cover_extract_witnessed_disjoint_pairs

#print axioms Erdos85.triangle_cover_extract_exterior_disjoint_pairs
