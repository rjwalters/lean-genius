import Proofs.Erdos85Problem

open SimpleGraph Finset

namespace Erdos85

theorem four_regular_of_fourteen_minDegree_four_not_containsC4
    (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj]
    (hmin : 4 ≤ G.minDegree) (hfree : ¬ containsC4 (Fin 14) G) :
    ∀ v, G.degree v = 4 := by
  classical
  have hdeg : ∀ v : Fin 14, 4 ≤ G.degree v :=
    fun v => le_trans hmin (G.minDegree_le_degree v)
  have hch : ∑ v : Fin 14, (G.degree v).choose 2 ≤ 91 := by
    by_contra h
    rw [not_le] at h
    exact hfree (containsC4_of_card_choose_two_lt G (by norm_num; exact h))
  intro v
  by_contra hv
  have hv4 := hdeg v
  have hv5 : 5 ≤ G.degree v := by omega
  by_cases hv6 : 6 ≤ G.degree v
  · have hrest : 78 ≤ ∑ u ∈ (univ : Finset (Fin 14)).erase v,
        (G.degree u).choose 2 := by
      calc
        78 = ∑ _u ∈ (univ : Finset (Fin 14)).erase v, 6 := by simp
        _ ≤ _ := Finset.sum_le_sum fun u _ =>
          Nat.choose_le_choose 2 (hdeg u)
    have hv15 : 15 ≤ (G.degree v).choose 2 := by
      norm_num at hv6 ⊢
      exact Nat.choose_le_choose 2 hv6
    have hsplit := Finset.add_sum_erase univ (fun u => (G.degree u).choose 2)
      (Finset.mem_univ v)
    omega
  · have hv_eq : G.degree v = 5 := by omega
    have hu : ∃ u : Fin 14, u ≠ v ∧ G.degree u ≠ 4 := by
      by_contra h
      push_neg at h
      have hsum : ∑ u : Fin 14, G.degree u = 57 := by
        rw [← Finset.add_sum_erase univ (fun u => G.degree u) (Finset.mem_univ v), hv_eq]
        have : ∑ u ∈ (univ : Finset (Fin 14)).erase v, G.degree u = 52 := by
          calc
            _ = ∑ _u ∈ (univ : Finset (Fin 14)).erase v, 4 := by
              apply Finset.sum_congr rfl
              intro u hu
              exact h u (Finset.ne_of_mem_erase hu)
            _ = 52 := by simp
        omega
      have hhs := SimpleGraph.sum_degrees_eq_twice_card_edges G
      omega
    obtain ⟨u, huv, hu4⟩ := hu
    have hu5 : 5 ≤ G.degree u := by have := hdeg u; omega
    have hrest : 72 ≤ ∑ w ∈ ((univ : Finset (Fin 14)).erase v).erase u,
        (G.degree w).choose 2 := by
      calc
        72 = ∑ _w ∈ ((univ : Finset (Fin 14)).erase v).erase u, 6 := by simp [huv]
        _ ≤ _ := Finset.sum_le_sum fun w _ => Nat.choose_le_choose 2 (hdeg w)
    have hv10 : 10 ≤ (G.degree v).choose 2 := by rw [hv_eq]; decide
    have hu10 : 10 ≤ (G.degree u).choose 2 := by
      norm_num at hu5 ⊢
      exact Nat.choose_le_choose 2 hu5
    have hsv := Finset.add_sum_erase univ (fun w => (G.degree w).choose 2)
      (Finset.mem_univ v)
    have hsu := Finset.add_sum_erase (univ.erase v) (fun w => (G.degree w).choose 2)
      (Finset.mem_erase.mpr ⟨huv, Finset.mem_univ u⟩)
    omega

theorem neighbor_induced_edges_eq_two_of_four_regular_not_containsC4
    (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = 4) (hfree : ¬ containsC4 (Fin 14) G)
    (v : Fin 14) :
    (G.induce (G.neighborSet v)).edgeFinset.card = 2 := by
  classical
  let N := G.neighborFinset v
  let H := G.induce (G.neighborSet v)
  have hNcard : N.card = 4 := by
    change (G.neighborFinset v).card = 4
    rw [G.card_neighborFinset_eq_degree, hreg v]
  have hHcard : Fintype.card {x // x ∈ G.neighborSet v} = 4 := by
    rw [Fintype.card_subtype]
    have heq : (univ.filter fun x => x ∈ G.neighborSet v) = N := by
      ext z
      simp [N]
    rw [heq, hNcard]
  have hHcardAdj : Fintype.card {x // G.Adj v x} = 4 := by
    let e : {x // x ∈ G.neighborSet v} ≃ {x // G.Adj v x} :=
      Equiv.subtypeEquivRight (fun _ => Iff.rfl)
    rw [← Fintype.card_congr e]
    exact hHcard
  have hHdeg : ∀ x, H.degree x ≤ 1 := by
    intro x
    have hxv : x.1 ≠ v := by
      exact G.ne_of_adj x.2.symm
    have hc := common_le_one_of_not_containsC4 hfree x.1 v hxv
    rw [← H.card_neighborFinset_eq_degree,
      ← Finset.card_map (f := .subtype (fun z => z ∈ G.neighborSet v)),
      G.map_neighborFinset_induce]
    have ht : (G.neighborSet v).toFinset = N := by ext z; simp [N]
    rw [ht]
    simpa [N, Finset.inter_comm] using hc
  have hHedges_le : H.edgeFinset.card ≤ 2 := by
    have hs : ∑ x, H.degree x ≤ 4 := by
      calc
        _ ≤ ∑ _x : {x // x ∈ G.neighborSet v}, 1 :=
          Finset.sum_le_sum fun x _ => hHdeg x
        _ = 4 := by
          rw [Finset.sum_const, Finset.card_univ, hHcard]
          norm_num
    have hhs := SimpleGraph.sum_degrees_eq_twice_card_edges H
    omega
  let E : {x // x ∈ G.neighborSet v} → Finset (Fin 14) := fun x =>
    G.neighborFinset x.1 \ insert v N
  have hEdisj : (↑(univ : Finset {x // x ∈ G.neighborSet v}) : Set _).PairwiseDisjoint E := by
    intro x _ y _ hxy
    change Disjoint (E x) (E y)
    rw [Finset.disjoint_left]
    intro z hzx hzy
    have hzxa : G.Adj x.1 z := by
      exact (G.mem_neighborFinset x.1 z).mp (Finset.mem_sdiff.mp hzx).1
    have hzya : G.Adj y.1 z := by
      exact (G.mem_neighborFinset y.1 z).mp (Finset.mem_sdiff.mp hzy).1
    have hvx : G.Adj v x.1 := x.2
    have hvy : G.Adj v y.1 := y.2
    have hxyv : x.1 ≠ y.1 := by exact fun h => hxy (Subtype.ext h)
    have hvz : v ≠ z := by
      exact fun h => (Finset.mem_sdiff.mp hzx).2 (by simp [h])
    exact hfree (containsC4_of_two_common hxyv hvz hvx hvy hzxa.symm hzya.symm)
  have hEsub : univ.biUnion E ⊆ univ \ insert v N := by
    intro z hz
    rw [Finset.mem_biUnion] at hz
    obtain ⟨x, -, hx⟩ := hz
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hx).2⟩
  have hUcard : (univ.biUnion E).card ≤ 9 := by
    calc
      _ ≤ (univ \ insert v N).card := Finset.card_le_card hEsub
      _ = 9 := by
        rw [Finset.card_sdiff]
        have hvN : v ∉ N := by simp [N]
        simp [hNcard, hvN]
  have hEcard : ∀ x, (E x).card + 1 + H.degree x = 4 := by
    intro x
    have hinter : insert v N ∩ G.neighborFinset x.1 =
        insert v (N ∩ G.neighborFinset x.1) := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      · rintro ⟨hzv | hzN, hzx⟩
        · exact Or.inl hzv
        · exact Or.inr ⟨hzN, hzx⟩
      · rintro (rfl | ⟨hzN, hzx⟩)
        · exact ⟨Or.inl rfl, by simpa using x.2.symm⟩
        · exact ⟨Or.inr hzN, hzx⟩
    have hvnot : v ∉ N ∩ G.neighborFinset x.1 := by simp [N]
    have hinternal : (N ∩ G.neighborFinset x.1).card = H.degree x := by
      rw [← H.card_neighborFinset_eq_degree,
        ← Finset.card_map (f := .subtype (fun z => z ∈ G.neighborSet v)),
        G.map_neighborFinset_induce]
      have ht : (G.neighborSet v).toFinset = N := by ext z; simp [N]
      rw [ht]
      simp [N, Finset.inter_comm]
    have hpart := Finset.card_sdiff_add_card_inter (G.neighborFinset x.1) (insert v N)
    rw [Finset.inter_comm] at hpart
    change (E x).card + (insert v N ∩ G.neighborFinset x.1).card =
      (G.neighborFinset x.1).card at hpart
    rw [hinter, Finset.card_insert_of_notMem hvnot, hinternal,
      G.card_neighborFinset_eq_degree, hreg x.1] at hpart
    omega
  have hsumE : ∑ x, (E x).card + 4 + 2 * H.edgeFinset.card = 16 := by
    have hs := Finset.sum_congr rfl (fun x (_ : x ∈ (univ : Finset _)) => hEcard x)
    have hhs := SimpleGraph.sum_degrees_eq_twice_card_edges H
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul] at hs
    rw [hHcard] at hs
    rw [hhs] at hs
    omega
  have hsumEle : ∑ x, (E x).card ≤ 9 := by
    rw [← Finset.card_biUnion hEdisj]
    exact hUcard
  change H.edgeFinset.card = 2
  omega

theorem existsUnique_common_of_four_regular_not_containsC4
    (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = 4) (hfree : ¬ containsC4 (Fin 14) G)
    {x y : Fin 14} (hxy : G.Adj x y) :
    ∃! z, G.Adj x z ∧ G.Adj y z := by
  classical
  let H := G.induce (G.neighborSet x)
  let yy : {z // z ∈ G.neighborSet x} := ⟨y, hxy⟩
  have hle : ∀ z, H.degree z ≤ 1 := by
    intro z
    have hzx : z.1 ≠ x := G.ne_of_adj z.2.symm
    have hc := common_le_one_of_not_containsC4 hfree z.1 x hzx
    rw [← H.card_neighborFinset_eq_degree,
      ← Finset.card_map (f := .subtype (fun w => w ∈ G.neighborSet x)),
      G.map_neighborFinset_induce]
    have ht : (G.neighborSet x).toFinset = G.neighborFinset x := by ext w; simp
    rw [ht]
    simpa [Finset.inter_comm] using hc
  have hsum : ∑ z, H.degree z = 4 := by
    have he := neighbor_induced_edges_eq_two_of_four_regular_not_containsC4
      G hreg hfree x
    change H.edgeFinset.card = 2 at he
    have hhs := SimpleGraph.sum_degrees_eq_twice_card_edges H
    omega
  have hcard : Fintype.card {z // z ∈ G.neighborSet x} = 4 := by
    rw [Fintype.card_subtype]
    have hxcard : (G.neighborFinset x).card = 4 := by
      rw [G.card_neighborFinset_eq_degree, hreg x]
    have heq : (univ.filter fun z => z ∈ G.neighborSet x) = G.neighborFinset x := by
      ext z
      simp
    rw [heq, hxcard]
  have hcardAdj : Fintype.card {z // G.Adj x z} = 4 := by
    let e : {z // z ∈ G.neighborSet x} ≃ {z // G.Adj x z} :=
      Equiv.subtypeEquivRight (fun _ => Iff.rfl)
    rw [← Fintype.card_congr e]
    exact hcard
  have hydeg : H.degree yy = 1 := by
    by_contra hy
    have hy0 : H.degree yy = 0 := by have := hle yy; omega
    have hrest : ∑ z ∈ (univ : Finset {z // z ∈ G.neighborSet x}).erase yy,
        H.degree z ≤ 3 := by
      calc
        _ ≤ ∑ _z ∈ (univ : Finset {z // z ∈ G.neighborSet x}).erase yy, 1 :=
          Finset.sum_le_sum fun z _ => hle z
        _ = 3 := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ yy),
            Finset.card_univ, hcard]
          norm_num
    have hsplit := Finset.add_sum_erase univ (fun z => H.degree z) (Finset.mem_univ yy)
    have htotal : H.degree yy + ∑ z ∈ (univ : Finset {z // z ∈ G.neighborSet x}).erase yy,
        H.degree z = 4 := hsplit.trans hsum
    omega
  have hnon : (H.neighborFinset yy).Nonempty := by
    rw [← Finset.card_pos, H.card_neighborFinset_eq_degree, hydeg]
    decide
  obtain ⟨zz, hzz⟩ := hnon
  refine ⟨zz.1, ⟨zz.2, (H.mem_neighborFinset yy zz).mp hzz⟩, ?_⟩
  intro z hz
  have hc := common_le_one_of_not_containsC4 hfree x y (G.ne_of_adj hxy)
  have h1 : zz.1 ∈ G.neighborFinset x ∩ G.neighborFinset y := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨zz.2, (H.mem_neighborFinset yy zz).mp hzz⟩
  have h2 : z ∈ G.neighborFinset x ∩ G.neighborFinset y := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact hz
  exact (Finset.card_le_one.mp hc _ h1 _ h2).symm

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2000 in
theorem locallyLinear_of_four_regular_not_containsC4
    (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = 4) (hfree : ¬ containsC4 (Fin 14) G) :
    G.LocallyLinear := by
  classical
  have huniq : ∀ x y, G.Adj x y → ∃! z, G.Adj x z ∧ G.Adj y z := by
    intro x y hxy
    exact existsUnique_common_of_four_regular_not_containsC4 G hreg hfree hxy
  have common_eq : ∀ {a b c d}, G.Adj a b → G.Adj a c → G.Adj b c →
      G.Adj a d → G.Adj b d → c = d := by
    intro a b c d hab hac hbc had hbd
    exact (huniq a b hab).unique ⟨hac, hbc⟩ ⟨had, hbd⟩
  constructor
  · rw [edgeDisjointTriangles_iff_mem_sym2_subsingleton, Sym2.forall]
    intro x y hxy
    simp only [Sym2.mk_isDiag_iff] at hxy
    have hdesc :
        {s ∈ (G.cliqueSet 3 : Set (Finset (Fin 14))) | s(x, y) ∈ (s : Finset (Fin 14)).sym2} =
          {s | G.Adj x y ∧ ∃ z, G.Adj x z ∧ G.Adj y z ∧ s = {x, y, z}} := by
      ext s
      simp only [mem_sym2_iff, Sym2.mem_iff, forall_eq_or_imp, forall_eq,
        mem_cliqueSet_iff, Set.mem_setOf_eq, is3Clique_iff]
      constructor
      · rintro ⟨⟨a, b, c, hab, hac, hbc, rfl⟩, hmem⟩
        simp only [mem_insert, mem_singleton] at hmem
        obtain ⟨rfl | rfl | rfl, rfl | rfl | rfl⟩ := hmem
        any_goals simp only [*, adj_comm, true_and, Ne, not_true] at *
        any_goals
          first
          | exact ⟨a, by aesop⟩
          | exact ⟨b, by aesop⟩
          | exact ⟨c, by aesop⟩
          | simp only [*, true_and] at *
            exact ⟨a, by aesop⟩
          | simp only [*, true_and] at *
            exact ⟨b, by aesop⟩
          | simp only [*, true_and] at *
            exact ⟨c, by aesop⟩
      · rintro ⟨hxy, z, hxz, hyz, rfl⟩
        refine ⟨⟨x, y, z, ?_⟩, ?_⟩ <;> simp [*]
    rw [hdesc]
    rintro _ ⟨hxy, z, hxz, hyz, rfl⟩ _ ⟨_, w, hxw, hyw, rfl⟩
    rw [common_eq hxy hxz hyz hxw hyw]
  · intro x y hxy
    obtain ⟨z, hz, -⟩ := huniq x y hxy
    exact ⟨{x, y, z}, (is3Clique_triple_iff.mpr ⟨hxy, hz.1, hz.2⟩), by simp, by simp⟩
theorem containsC4_of_fourteen_minDegree_four
    (G : SimpleGraph (Fin 14)) [DecidableRel G.Adj]
    (hmin : 4 ≤ G.minDegree) : containsC4 (Fin 14) G := by
  classical
  by_contra hfree
  have hreg := four_regular_of_fourteen_minDegree_four_not_containsC4
    G hmin hfree
  have hsum : ∑ v : Fin 14, G.degree v = 56 := by
    calc
      _ = ∑ _v : Fin 14, 4 := Finset.sum_congr rfl (fun v _ => hreg v)
      _ = 56 := by norm_num
  have hedge : G.edgeFinset.card = 28 := by
    have hhs := SimpleGraph.sum_degrees_eq_twice_card_edges G
    omega
  have hlocal := locallyLinear_of_four_regular_not_containsC4 G hreg hfree
  have htri := hlocal.card_edgeFinset
  rw [hedge] at htri
  omega

theorem minDegreeForC4_le_four_fourteen : minDegreeForC4 14 ≤ 4 := by
  apply Nat.sInf_le
  intro G _ hmin
  exact containsC4_of_fourteen_minDegree_four G hmin

theorem minDegreeForC4_fourteen : minDegreeForC4 14 = 4 := by
  exact le_antisymm minDegreeForC4_le_four_fourteen
    four_le_minDegreeForC4_fourteen

end Erdos85
