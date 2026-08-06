import Proofs.Erdos85PositiveExcessOne

/-!
# Local parity at arbitrary positive excess

At order `d(d-1)+3+e`, the combined defect graph has degree `e+2`.
The triangle-free incident edges at a vertex form one part of its defect
neighbourhood, so there are at most `e+2` of them.  On the other hand, all
remaining incident edges are paired by edges of the induced neighbourhood;
the triangle-free count therefore has the same parity as `d`.

For excess two this leaves only `{0,2,4}` in even degree and `{1,3}` in odd
degree.  This is the local starting point for a canonical-form analysis of
the four-regular defect graph.
-/

open SimpleGraph

namespace Erdos85

/-- Triangle-free incident edges occupy part of the `(e+2)`-regular combined
defect neighbourhood. -/
theorem triangleFreeNeighbors_card_le_excess_add_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ}
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (x : V) :
    (triangleFreeNeighbors G x).card ≤ e + 2 := by
  have hsub : triangleFreeNeighbors G x ⊆
      (secondOrderDefectGraph G).neighborFinset x := by
    intro y hy
    rw [secondOrderDefectGraph_neighborFinset]
    exact Finset.mem_union_right _ hy
  calc
    (triangleFreeNeighbors G x).card ≤
        ((secondOrderDefectGraph G).neighborFinset x).card :=
      Finset.card_le_card hsub
    _ = (secondOrderDefectGraph G).degree x :=
      (secondOrderDefectGraph G).card_neighborFinset_eq_degree x
    _ = e + 2 :=
      secondOrderDefectGraph_degree_eq_excess_add_two
        G hfree hreg hcard x

/-- The triangle-free incident-edge count has the same parity as the ambient
regular degree. -/
theorem triangleFreeNeighbors_card_mod_two_eq_degree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d) (x : V) :
    (triangleFreeNeighbors G x).card % 2 = d % 2 := by
  have hsum := card_triangleFreeNeighbors_add_localDegreeSum_of_regular
    G hfree hreg x
  let H := G.induce (G.neighborSet x)
  have hhand :
      (∑ y : {z : V // z ∈ G.neighborSet x}, H.degree y) =
        2 * H.edgeFinset.card :=
    SimpleGraph.sum_degrees_eq_twice_card_edges H
  rw [hhand] at hsum
  omega

/-- At excess two and even degree, the local triangle-free degree is
`0`, `2`, or `4`. -/
theorem excessTwo_triangleFreeNeighbors_card_eq_zero_or_two_or_four_of_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (heven : Even d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 5) (x : V) :
    (triangleFreeNeighbors G x).card = 0 ∨
      (triangleFreeNeighbors G x).card = 2 ∨
      (triangleFreeNeighbors G x).card = 4 := by
  have hle := triangleFreeNeighbors_card_le_excess_add_two
    G hfree (e := 2) hreg (by omega) x
  have hmod := triangleFreeNeighbors_card_mod_two_eq_degree G hfree hreg x
  obtain ⟨k, hk⟩ := heven
  omega

/-- At excess two and odd degree, the local triangle-free degree is `1` or
`3`. -/
theorem excessTwo_triangleFreeNeighbors_card_eq_one_or_three_of_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hodd : Odd d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 5) (x : V) :
    (triangleFreeNeighbors G x).card = 1 ∨
      (triangleFreeNeighbors G x).card = 3 := by
  have hle := triangleFreeNeighbors_card_le_excess_add_two
    G hfree (e := 2) hreg (by omega) x
  have hmod := triangleFreeNeighbors_card_mod_two_eq_degree G hfree hreg x
  obtain ⟨k, hk⟩ := hodd
  omega

/-- If a vertex attains the maximum possible triangle-free degree `e+2`,
then its distance-two branches cover the whole complement of its closed
neighbourhood.  Equivalently, its third distance layer is empty. -/
theorem positiveExcess_maxTriangleFree_secondLayer_eq_outsideClosedNeighborhood
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ}
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (x : V) (hx : (triangleFreeNeighbors G x).card = e + 2) :
    secondLayer G x = outsideClosedNeighborhood G x := by
  classical
  have hlocalsum :
      (∑ y : {z : V // z ∈ G.neighborSet x},
        (G.induce (G.neighborSet x)).degree y) = d - (e + 2) := by
    have hsum := card_triangleFreeNeighbors_add_localDegreeSum_of_regular
      G hfree hreg x
    rw [hx] at hsum
    omega
  have hextid := card_external_add_degree_sq_add_one_eq_card_add_localDegreeSum
    G hfree hreg x
  rw [hcard, hlocalsum] at hextid
  have hde : e + 2 ≤ d := by
    have hsub : triangleFreeNeighbors G x ⊆ G.neighborFinset x := by
      intro y hy
      exact (G.mem_neighborFinset x y).mpr
        ((mem_triangleFreeNeighbors G x y).mp hy).1
    have hle := Finset.card_le_card hsub
    rw [hx, G.card_neighborFinset_eq_degree, hreg x] at hle
    exact hle
  have hmul : d * d = d * (d - 1) + d := by
    calc
      d * d = d * ((d - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ d)]
      _ = d * (d - 1) + d := by ring
  rw [hmul] at hextid
  have hextcard : (externalRepairCandidates G x).card = 0 := by omega
  have hext : externalRepairCandidates G x = ∅ :=
    Finset.card_eq_zero.mp hextcard
  apply Finset.Subset.antisymm
  · intro y hy
    simp only [outsideClosedNeighborhood, Finset.mem_filter]
    change y ∈ secondLayer G x at hy
    rw [secondLayer, Finset.mem_biUnion] at hy
    obtain ⟨z, _, hz⟩ := hy
    have hout := (Finset.mem_sdiff.mp hz).2
    refine ⟨Finset.mem_univ y, ?_, ?_⟩
    · intro hyx
      exact hout (Finset.mem_insert.mpr (Or.inl hyx))
    · intro hyadj
      exact hout (Finset.mem_insert.mpr (Or.inr
        ((G.mem_neighborFinset x y).mpr hyadj.symm)))
  · intro y hy
    have hcover := closedNeighborhood_union_secondLayer_union_external_eq_univ G x
    have hycover : y ∈ insert x (G.neighborFinset x) ∪ secondLayer G x ∪
        (externalRepairCandidates G x).map
          ⟨Subtype.val, Subtype.val_injective⟩ := by
      rw [hcover]
      exact Finset.mem_univ y
    rw [hext] at hycover
    simp only [Finset.map_empty, Finset.union_empty] at hycover
    rcases Finset.mem_union.mp hycover with hclosed | hsecond
    · have hyout := (Finset.mem_filter.mp hy).2
      rcases Finset.mem_insert.mp hclosed with rfl | hneighbor
      · exact (hyout.1 rfl).elim
      · exact (hyout.2
          ((G.mem_neighborFinset x y).mp hneighbor).symm).elim
    · exact hsecond

/-- **Full second-layer cover obstruction.**  In an odd-regular `C₄`-free
graph, if not every neighbour of `x` is triangle-free, then the second layer
cannot cover the whole complement of the closed neighbourhood.  The proof is
the excess-independent core of the old excess-one terminal: an isolated
vertex in an odd branch produces an injection of `d-1` neighbours into only
`d-2` available roots. -/
theorem false_of_triangleFreeNeighbors_lt_degree_of_secondLayer_cover
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d) (x : V)
    (hlt : (triangleFreeNeighbors G x).card < d)
    (hlayer : secondLayer G x = outsideClosedNeighborhood G x) : False := by
  classical
  let N := G.neighborFinset x
  let H := G.induce (G.neighborSet x)
  have hNcard : N.card = d := by
    simp only [N]
    rw [G.card_neighborFinset_eq_degree, hreg x]
  have hltN : (triangleFreeNeighbors G x).card < N.card := by
    rwa [hNcard]
  obtain ⟨u0, huN, huTF⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hltN
  let u : {z : V // z ∈ G.neighborSet x} :=
    ⟨u0, by simpa [N] using huN⟩
  have huLocal : H.degree u = 1 := by
    have hle : H.degree u ≤ 1 := by
      change (G.induce (G.neighborSet x)).degree u ≤ 1
      rw [degree_induce_neighborSet_eq_card_common]
      exact common_le_one_of_not_containsC4 hfree x u.1 (G.ne_of_adj u.2)
    have hne : H.degree u ≠ 0 := by
      intro hz
      apply huTF
      rw [mem_triangleFreeNeighbors]
      refine ⟨u.2, ?_⟩
      change (G.induce (G.neighborSet x)).degree u = 0 at hz
      rw [degree_induce_neighborSet_eq_card_common] at hz
      exact hz
    omega
  have huNonempty : (H.neighborFinset u).Nonempty := by
    rw [← Finset.card_pos, H.card_neighborFinset_eq_degree, huLocal]
    decide
  obtain ⟨v0, hv0⟩ := huNonempty
  let v : {z : V // z ∈ G.neighborSet x} := v0
  have huv : G.Adj u.1 v.1 := by
    simpa [H, SimpleGraph.mem_neighborFinset] using hv0
  have huv_ne : u ≠ v := by
    intro h
    exact (G.ne_of_adj huv) (congrArg Subtype.val h)
  let A := secondLayerBranch G x u
  have hAcard : A.card = d - 2 := by
    have hcardA := card_secondLayerBranch_eq_degree_sub_localDegree_sub_one
      G hreg x u
    rw [huLocal] at hcardA
    change A.card = d - 1 - 1 at hcardA
    omega
  have hAodd : Odd (Fintype.card A) := by
    rw [Fintype.card_coe, hAcard]
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k - 1, by omega⟩
  let K := G.induce A
  have hKle : ∀ a : A, K.degree a ≤ 1 := by
    intro a
    exact degree_induce_secondLayerBranch_le_one G hfree x u a
  obtain ⟨a, haIso⟩ :=
    exists_degree_eq_zero_of_odd_card_of_degree_le_one K hAodd hKle
  let B := (G.neighborFinset a.1).erase u.1
  have hua : G.Adj u.1 a.1 :=
    (G.mem_neighborFinset u.1 a.1).mp (Finset.mem_sdiff.mp a.2).1
  have huMem : u.1 ∈ G.neighborFinset a.1 :=
    (G.mem_neighborFinset a.1 u.1).mpr hua.symm
  have hBcard : B.card = d - 1 := by
    simp only [B]
    rw [Finset.card_erase_of_mem huMem,
      G.card_neighborFinset_eq_degree, hreg a.1]
  have hroot : ∀ b, b ∈ B →
      ∃ r : {z : V // z ∈ G.neighborSet x},
        b ∈ secondLayerBranch G x r := by
    intro b hb
    have hab : G.Adj a.1 b :=
      (G.mem_neighborFinset a.1 b).mp (Finset.mem_erase.mp hb).2
    have hbu : b ≠ u.1 := (Finset.mem_erase.mp hb).1
    have hbOut : b ∈ outsideClosedNeighborhood G x := by
      simp only [outsideClosedNeighborhood, Finset.mem_filter]
      refine ⟨Finset.mem_univ b, ?_, ?_⟩
      · intro hbx
        subst b
        have hnax : ¬ G.Adj x a.1 := by
          intro hxa
          exact (Finset.mem_sdiff.mp a.2).2
            (Finset.mem_insert.mpr (Or.inr
              ((G.mem_neighborFinset x a.1).mpr hxa)))
        exact hnax hab.symm
      · intro hbx
        have hxu : G.Adj x u.1 := u.2
        have hxa : x ≠ a.1 := by
          intro h
          have hax : a.1 = x := h.symm
          exact (Finset.mem_sdiff.mp a.2).2
            (Finset.mem_insert.mpr (Or.inl hax))
        exact hfree (containsC4_of_two_common
          (x := x) (y := a.1) (v := u.1) (v' := b)
          hxa hbu.symm hxu.symm hua hbx hab.symm)
    rw [← hlayer, secondLayer, Finset.mem_biUnion] at hbOut
    obtain ⟨r, _, hr⟩ := hbOut
    exact ⟨r, hr⟩
  let root : B → {z : V // z ∈ G.neighborSet x} := fun b =>
    Classical.choose (hroot b.1 b.2)
  have hrootMem : ∀ b : B, b.1 ∈ secondLayerBranch G x (root b) := by
    intro b
    exact Classical.choose_spec (hroot b.1 b.2)
  have hroot_ne_u : ∀ b : B, root b ≠ u := by
    intro b hru
    have hbA : b.1 ∈ A := by simpa [A, hru] using hrootMem b
    have habK : K.Adj a ⟨b.1, hbA⟩ := by
      change G.Adj a.1 b.1
      exact (G.mem_neighborFinset a.1 b.1).mp
        (Finset.mem_erase.mp b.2).2
    have hbK : (⟨b.1, hbA⟩ : A) ∈ K.neighborFinset a :=
      (K.mem_neighborFinset a _).mpr habK
    have hempty : K.neighborFinset a = ∅ := by
      apply Finset.card_eq_zero.mp
      rwa [K.card_neighborFinset_eq_degree]
    rw [hempty] at hbK
    exact Finset.notMem_empty _ hbK
  have hroot_ne_v : ∀ b : B, root b ≠ v := by
    intro b hrv
    have hbV : b.1 ∈ secondLayerBranch G x v := by
      simpa [hrv] using hrootMem b
    have hab : G.Adj a.1 b.1 :=
      (G.mem_neighborFinset a.1 b.1).mp (Finset.mem_erase.mp b.2).2
    exact (not_adj_between_secondLayerBranches_of_adj_roots
      G hfree x u v huv a ⟨b.1, hbV⟩) hab
  have hrootInj : Function.Injective root := by
    intro b c hbc
    apply Subtype.ext
    by_contra hbval
    have htwo : 2 ≤
        (G.neighborFinset a.1 ∩ secondLayerBranch G x (root b)).card := by
      have hcMem : c.1 ∈ secondLayerBranch G x (root b) := by
        rw [hbc]
        exact hrootMem c
      have hsub : ({b.1, c.1} : Finset V) ⊆
          G.neighborFinset a.1 ∩ secondLayerBranch G x (root b) := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_inter.mpr
            ⟨(Finset.mem_erase.mp b.2).2, hrootMem b⟩
        · exact Finset.mem_inter.mpr
            ⟨(Finset.mem_erase.mp c.2).2, hcMem⟩
      have hpair : ({b.1, c.1} : Finset V).card = 2 := by
        simp [hbval]
      rw [← hpair]
      exact Finset.card_le_card hsub
    have hroot_ne_a : a.1 ≠ (root b).1 := by
      intro h
      have haN : a.1 ∈ G.neighborFinset x := by
        rw [h]
        exact (G.mem_neighborFinset x (root b).1).mpr (root b).2
      exact (Finset.mem_sdiff.mp a.2).2
        (Finset.mem_insert.mpr (Or.inr haN))
    have hone := card_neighborFinset_inter_secondLayerBranch_le_one
      G hfree x a.1 (root b) hroot_ne_a
    omega
  let target := (Finset.univ.erase u).erase v
  let root' : B → target := fun b => ⟨root b, by
    simp only [target, Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨hroot_ne_v b, hroot_ne_u b⟩⟩
  have hroot'Inj : Function.Injective root' := by
    intro b c h
    apply hrootInj
    exact congrArg Subtype.val h
  have hlecard : Fintype.card B ≤ Fintype.card target :=
    Fintype.card_le_of_injective root' hroot'Inj
  have htargetcard : Fintype.card target = d - 2 := by
    simp only [target, Fintype.card_coe]
    rw [Finset.card_erase_of_mem]
    · rw [Finset.card_erase_of_mem (Finset.mem_univ u),
        Finset.card_univ, Fintype.card_subtype]
      have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet x) = N := by
        ext z
        simp [N]
      rw [heq, hNcard]
      omega
    · exact Finset.mem_erase.mpr ⟨huv_ne.symm, Finset.mem_univ v⟩
  rw [Fintype.card_coe, hBcard, htargetcard] at hlecard
  omega

/-- A vertex can never attain the maximum allowed triangle-free degree
`e+2` in the odd-degree plateau band `e ≤ d-4`. -/
theorem false_of_positiveExcess_maxTriangleFreeNeighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d) (hodd : Odd d)
    (he : e ≤ d - 4) (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (x : V) (hx : (triangleFreeNeighbors G x).card = e + 2) : False := by
  have hlt : (triangleFreeNeighbors G x).card < d := by
    rw [hx]
    omega
  exact false_of_triangleFreeNeighbors_lt_degree_of_secondLayer_cover
    G hfree hd hodd hreg x hlt
      (positiveExcess_maxTriangleFree_secondLayer_eq_outsideClosedNeighborhood
        G hfree hreg hcard x hx)

/-- In the surviving odd-degree/odd-excess band, the local triangle-free
degree improves from the automatic bound `e+2` to `e`. -/
theorem triangleFreeNeighbors_card_le_excess_of_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d)
    (hoddD : Odd d) (hoddE : Odd e) (he : e ≤ d - 4)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (x : V) : (triangleFreeNeighbors G x).card ≤ e := by
  have hle := triangleFreeNeighbors_card_le_excess_add_two
    G hfree hreg hcard x
  have htfOdd : Odd (triangleFreeNeighbors G x).card := by
    apply Nat.odd_iff.mpr
    rw [triangleFreeNeighbors_card_mod_two_eq_degree G hfree hreg x]
    exact Nat.odd_iff.mp hoddD
  by_contra hnot
  have hgt : e < (triangleFreeNeighbors G x).card := Nat.lt_of_not_ge hnot
  obtain ⟨a, ha⟩ := hoddE
  obtain ⟨b, hb⟩ := htfOdd
  have heq : (triangleFreeNeighbors G x).card = e + 2 := by omega
  exact false_of_positiveExcess_maxTriangleFreeNeighbors
    G hfree hd hoddD he hreg hcard x heq

/-- At excess three and odd degree, the triangle-free-edge graph has local
degree exactly `1` or `3`. -/
theorem excessThree_triangleFreeNeighbors_card_eq_one_or_three_of_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6)
    (x : V) :
    (triangleFreeNeighbors G x).card = 1 ∨
      (triangleFreeNeighbors G x).card = 3 := by
  have hle := triangleFreeNeighbors_card_le_excess_of_odd
    G hfree (e := 3) (by omega) hodd (by norm_num) (by omega) hreg (by omega) x
  have hmod := triangleFreeNeighbors_card_mod_two_eq_degree G hfree hreg x
  obtain ⟨k, hk⟩ := hodd
  omega

/-- **Odd excess-two terminal.**  No odd-degree regular `C₄`-free graph can
have order `d(d-1)+5`.  Every vertex would have odd degree in the
triangle-free-edge graph, whereas the ambient vertex set has odd cardinality,
contradicting the handshaking lemma. -/
theorem false_of_odd_regular_excessTwo
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hodd : Odd d)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 5) : False := by
  let T := triangleFreeEdgeGraph G
  have hall : ∀ x : V, Odd (T.degree x) := by
    intro x
    have hx := excessTwo_triangleFreeNeighbors_card_eq_one_or_three_of_odd
      G hfree hodd hreg hcard x
    rw [← T.card_neighborFinset_eq_degree,
      triangleFreeEdgeGraph_neighborFinset]
    rcases hx with hx | hx <;> rw [hx] <;> norm_num
  have hevenCard : Even (Fintype.card V) := by
    have hfilter :
        (Finset.univ.filter fun x : V => Odd (T.degree x)) = Finset.univ := by
      ext x
      simp [hall x]
    have hhand := T.even_card_odd_degree_vertices
    rw [hfilter, Finset.card_univ] at hhand
    exact hhand
  have hoddCard : Odd (Fintype.card V) := by
    rw [hcard]
    have hpred : Even (d - 1) := by
      apply (Nat.even_sub' (m := d) (n := 1) hodd.pos).2
      simpa using hodd
    exact (hpred.mul_left d).add_odd (by norm_num)
  obtain ⟨a, ha⟩ := hevenCard
  obtain ⟨b, hb⟩ := hoddCard
  omega

/-- **Uniform odd-degree excess parity.**  An odd-degree regular `C₄`-free
graph cannot have even second-order excess.  This removes every even stratum
of the positive-excess plateau band at once. -/
theorem false_of_odd_degree_even_excess
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ}
    (hodd : Odd d) (heven : Even e)
    (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e) : False := by
  let T := triangleFreeEdgeGraph G
  letI : DecidableRel T.Adj := Classical.decRel _
  have hall : ∀ x : V, Odd (T.degree x) := by
    intro x
    have hmod := triangleFreeNeighbors_card_mod_two_eq_degree G hfree hreg x
    rw [← T.card_neighborFinset_eq_degree,
      triangleFreeEdgeGraph_neighborFinset]
    apply Nat.odd_iff.mpr
    rw [hmod]
    exact Nat.odd_iff.mp hodd
  have hevenCard : Even (Fintype.card V) := by
    have hfilter :
        (Finset.univ.filter fun x : V => Odd (T.degree x)) = Finset.univ := by
      ext x
      simp [hall x]
    have hhand := T.even_card_odd_degree_vertices
    rw [hfilter, Finset.card_univ] at hhand
    exact hhand
  have hoddCard : Odd (Fintype.card V) := by
    rw [hcard]
    have hpred : Even (d - 1) := by
      apply (Nat.even_sub' (m := d) (n := 1) hodd.pos).2
      simpa using hodd
    have htail : Odd (3 + e) := by
      simpa [Nat.add_comm] using heven.add_odd (by norm_num : Odd 3)
    simpa [Nat.add_assoc] using (hpred.mul_left d).add_odd htail
  exact (Nat.not_even_iff_odd.mpr hoddCard) hevenCard

/-- Equivalently, every odd-degree regular `C₄`-free graph in the
second-order parametrization has odd excess. -/
theorem excess_odd_of_odd_degree_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {d e : ℕ}
    (hodd : Odd d) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e) : Odd e := by
  rw [← Nat.not_even_iff_odd]
  exact fun heven =>
    false_of_odd_degree_even_excess G hfree hodd heven hreg hcard

end Erdos85
