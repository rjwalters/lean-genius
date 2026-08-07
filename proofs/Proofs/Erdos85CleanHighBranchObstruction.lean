import Proofs.Erdos85HighRootZeroSlack
import Proofs.Erdos85CommonNeighborPigeonhole

/-!
# Uniform clean high-branch obstruction

Fix two paired parents `s,t` in the neighborhood of a square-order high
root.  If an outer vertex in the `s`-branch has a neighbor in every other
branch, and each of those neighbors in turn has a neighbor in the `t`-branch,
then the `d-1` intermediate branches inject into a target branch of size
`d-2`.  This is impossible.  It is the graph-facing core of the clean-sector
obstruction, uniform in `d`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- At a saturated high root, if every branch is internally independent,
then an outer degree-`d` vertex has exactly one neighbor in every branch
other than its own branch and its paired branch. -/
theorem card_neighbors_inter_farBranch_eq_one_of_clean
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 3 ≤ d) {v : V}
    (hv : G.degree v = d + 1)
    (hexternal : externalRepairCandidates G v = ∅)
    (hclean : ∀ u : {z : V // z ∈ G.neighborSet v},
      ∀ {p q : V}, p ∈ secondLayerBranch G v u →
        q ∈ secondLayerBranch G v u → ¬ G.Adj p q)
    (s t u : {z : V // z ∈ G.neighborSet v})
    (hst : G.Adj s.1 t.1) (hus : u ≠ s) (hut : u ≠ t)
    (a : V) (ha : a ∈ secondLayerBranch G v s)
    (hadegree : G.degree a = d) :
    (G.neighborFinset a ∩ secondLayerBranch G v u).card = 1 := by
  classical
  let P := {z : V // z ∈ G.neighborSet v}
  let branchCount : P → ℕ := fun w =>
    (G.neighborFinset a ∩ secondLayerBranch G v w).card
  have haOutside : a ∉ insert v (G.neighborFinset v) :=
    (Finset.mem_sdiff.mp ha).2
  have hparentAdj : G.Adj a s.1 := by
    have := (Finset.mem_sdiff.mp ha).1
    simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using this
  have hneighbors : G.neighborFinset a =
      insert s.1 (G.neighborFinset a ∩ secondLayer G v) := by
    ext q
    constructor
    · intro hq
      have haq : G.Adj a q := (G.mem_neighborFinset a q).mp hq
      have hcover : q ∈ (Finset.univ : Finset V) := by simp
      have hpartition :=
        closedNeighborhood_union_secondLayer_union_external_eq_univ G v
      rw [← hpartition, hexternal] at hcover
      simp only [Finset.map_empty, Finset.union_empty, Finset.mem_union,
        Finset.mem_insert, SimpleGraph.mem_neighborFinset] at hcover
      rcases hcover with (rfl | hqNv) | hqSecond
      · exact (haOutside (by
          simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
          exact Or.inr haq.symm)).elim
      · let r : P := ⟨q, hqNv⟩
        have haBranchR : a ∈ secondLayerBranch G v r := by
          apply Finset.mem_sdiff.mpr
          refine ⟨(G.mem_neighborFinset q a).mpr haq.symm, haOutside⟩
        have hrs : r = s := by
          by_contra hrs
          have hdisj := secondLayerBranch_pairwiseDisjoint G hfree v
            (by simp : r ∈ (Finset.univ : Finset P))
            (by simp : s ∈ (Finset.univ : Finset P)) hrs
          exact (Finset.disjoint_left.mp hdisj) haBranchR ha
        exact Finset.mem_insert.mpr (Or.inl (congrArg Subtype.val hrs))
      · exact Finset.mem_insert.mpr (Or.inr
          (Finset.mem_inter.mpr ⟨hq, hqSecond⟩))
    · intro hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact (G.mem_neighborFinset a s.1).mpr hparentAdj
      · exact (Finset.mem_inter.mp hq).1
  have hsNotSecond : s.1 ∉ secondLayer G v := by
    intro hs
    rw [secondLayer] at hs
    rcases Finset.mem_biUnion.mp hs with ⟨w, _, hsw⟩
    exact (Finset.mem_sdiff.mp hsw).2 (by
      simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
      exact Or.inr s.2)
  have hsum : ∑ w : P, branchCount w = d - 1 := by
    have hbranchDisj := secondLayerBranch_pairwiseDisjoint G hfree v
    have hinter : G.neighborFinset a ∩ secondLayer G v =
        Finset.univ.biUnion fun w : P =>
          G.neighborFinset a ∩ secondLayerBranch G v w := by
      ext q
      constructor
      · intro hq
        have hqa := (Finset.mem_inter.mp hq).1
        rw [secondLayer] at hq
        rcases Finset.mem_biUnion.mp (Finset.mem_inter.mp hq).2 with
          ⟨w, _, hqw⟩
        exact Finset.mem_biUnion.mpr ⟨w, by simp,
          Finset.mem_inter.mpr ⟨hqa, hqw⟩⟩
      · intro hq
        rcases Finset.mem_biUnion.mp hq with ⟨w, _, hqw⟩
        exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp hqw).1,
          Finset.mem_biUnion.mpr ⟨w, by simp,
            (Finset.mem_inter.mp hqw).2⟩⟩
    have hinterDisj :
        (↑(Finset.univ : Finset P) : Set P).PairwiseDisjoint
          (fun w => G.neighborFinset a ∩ secondLayerBranch G v w) := by
      intro w _ z _ hwz
      change Disjoint
        (G.neighborFinset a ∩ secondLayerBranch G v w)
        (G.neighborFinset a ∩ secondLayerBranch G v z)
      rw [Finset.disjoint_left]
      intro q hqw hqz
      exact (Finset.disjoint_left.mp
        (hbranchDisj (by simp) (by simp) hwz))
          (Finset.mem_inter.mp hqw).2 (Finset.mem_inter.mp hqz).2
    have hcardNeighbors :
        (G.neighborFinset a).card =
          1 + (G.neighborFinset a ∩ secondLayer G v).card := by
      calc
        (G.neighborFinset a).card =
            (insert s.1 (G.neighborFinset a ∩ secondLayer G v)).card := by
          exact congrArg Finset.card hneighbors
        _ = 1 + (G.neighborFinset a ∩ secondLayer G v).card := by
          rw [Finset.card_insert_of_notMem]
          · omega
          · intro hs
            exact hsNotSecond (Finset.mem_inter.mp hs).2
    rw [G.card_neighborFinset_eq_degree, hadegree, hinter,
      Finset.card_biUnion hinterDisj] at hcardNeighbors
    dsimp [branchCount]
    omega
  have hle : ∀ w : P, branchCount w ≤ 1 := by
    intro w
    have haw : a ≠ w.1 := by
      intro haw
      apply haOutside
      simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
      exact Or.inr (haw ▸ w.2)
    exact card_neighborFinset_inter_secondLayerBranch_le_one
      G hfree v a w haw
  have hsZero : branchCount s = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    exact hclean s ha (Finset.mem_inter.mp hq).2
      ((G.mem_neighborFinset a q).mp (Finset.mem_inter.mp hq).1)
  have htZero : branchCount t = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro q hq
    exact not_adj_between_secondLayerBranches_of_adj_roots
      G hfree v s t hst ⟨a, ha⟩ ⟨q, (Finset.mem_inter.mp hq).2⟩
        ((G.mem_neighborFinset a q).mp (Finset.mem_inter.mp hq).1)
  by_contra hnot
  change branchCount u ≠ 1 at hnot
  have huZero : branchCount u = 0 := by
    have := hle u
    omega
  let R : Finset P := ((Finset.univ.erase s).erase t).erase u
  have hRcard : R.card = d - 2 := by
    have hstne : s ≠ t := fun h => G.loopless.irrefl s.1
      (congrArg Subtype.val h ▸ hst)
    dsimp [R]
    rw [Finset.card_erase_of_mem (by simp [hus, hut] :
      u ∈ ((Finset.univ : Finset P).erase s).erase t)]
    rw [Finset.card_erase_of_mem (by simp [hstne.symm] :
      t ∈ (Finset.univ : Finset P).erase s)]
    rw [Finset.card_erase_of_mem (by simp : s ∈ (Finset.univ : Finset P))]
    rw [Finset.card_univ]
    have hPcard : Fintype.card P = d + 1 := by
      rw [Fintype.card_subtype]
      have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet v) =
          G.neighborFinset v := by ext z; simp
      rw [heq, G.card_neighborFinset_eq_degree, hv]
    rw [hPcard]
    omega
  have hsumR : (∑ w ∈ R, branchCount w) ≤ R.card := by
    calc
      (∑ w ∈ R, branchCount w) ≤ ∑ _w ∈ R, 1 := by
        apply Finset.sum_le_sum
        intro w _
        exact hle w
      _ = R.card := by simp
  have hsumErase : (∑ w ∈ R, branchCount w) = d - 1 := by
    have hsMem : s ∈ (Finset.univ : Finset P) := by simp
    have htMem : t ∈ (Finset.univ : Finset P).erase s := by
      have hstne : s ≠ t := fun h => G.loopless.irrefl s.1
        (congrArg Subtype.val h ▸ hst)
      simp [hstne.symm]
    have huMem : u ∈ ((Finset.univ : Finset P).erase s).erase t := by
      simp [hus, hut]
    have huSum := Finset.sum_erase_add
      ((Finset.univ : Finset P).erase s |>.erase t) branchCount huMem
    have htSum := Finset.sum_erase_add
      ((Finset.univ : Finset P).erase s) branchCount htMem
    have hsSum := Finset.sum_erase_add
      (Finset.univ : Finset P) branchCount hsMem
    dsimp [R]
    calc
      (∑ w ∈ ((Finset.univ.erase s).erase t).erase u, branchCount w) =
          ∑ w ∈ (Finset.univ.erase s).erase t, branchCount w := by
        rw [← huSum, huZero, add_zero]
      _ = ∑ w ∈ Finset.univ.erase s, branchCount w := by
        rw [← htSum, htZero, add_zero]
      _ = ∑ w ∈ (Finset.univ : Finset P), branchCount w := by
        rw [← hsSum, hsZero, add_zero]
      _ = d - 1 := hsum
  rw [hsumErase, hRcard] at hsumR
  omega

/-- A full two-step fan between paired high-root branches contradicts
`C₄`-freeness: its `d-1` distinct intermediate branches would need distinct
endpoints in a branch of size `d-2`. -/
theorem false_of_squareOrder_pairedBranch_fullFan
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 3 ≤ d) {v : V}
    (hv : G.degree v = d + 1)
    (hneigh : ∀ y, G.Adj v y → G.degree y = d)
    (hlocal : ∀ u : {z : V // z ∈ G.neighborSet v},
      (G.induce (G.neighborSet v)).degree u = 1)
    (s t : {z : V // z ∈ G.neighborSet v})
    (hst : G.Adj s.1 t.1)
    (a : V) (ha : a ∈ secondLayerBranch G v s)
    (hfirst : ∀ u : {u : {z : V // z ∈ G.neighborSet v} //
        u ∈ (Finset.univ.erase s).erase t},
      (G.neighborFinset a ∩ secondLayerBranch G v u.1).card = 1)
    (hsecond : ∀ u : {u : {z : V // z ∈ G.neighborSet v} //
        u ∈ (Finset.univ.erase s).erase t},
      ∀ q ∈ G.neighborFinset a ∩ secondLayerBranch G v u.1,
        (G.neighborFinset q ∩ secondLayerBranch G v t).card = 1) :
    False := by
  classical
  let P := {z : V // z ∈ G.neighborSet v}
  let M : Finset P := (Finset.univ.erase s).erase t
  let K := {u : P // u ∈ M}
  have hstne : s ≠ t := by
    intro h
    exact G.loopless.irrefl s.1 (congrArg Subtype.val h ▸ hst)
  have hPcard : Fintype.card P = d + 1 := by
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet v) =
        G.neighborFinset v := by ext z; simp
    rw [heq, G.card_neighborFinset_eq_degree, hv]
  have hMcard : M.card = d - 1 := by
    dsimp [M]
    rw [Finset.card_erase_of_mem (by simp [hstne.symm] :
      t ∈ (Finset.univ : Finset P).erase s)]
    rw [Finset.card_erase_of_mem (by simp : s ∈ (Finset.univ : Finset P))]
    rw [Finset.card_univ, hPcard]
    omega
  have htargetCard : (secondLayerBranch G v t).card = d - 2 :=
    card_secondLayerBranch_eq_sub_two_of_squareOrder_highRoot
      G (by omega) hv hneigh hlocal t
  let firstSet : K → Finset V := fun u =>
    G.neighborFinset a ∩ secondLayerBranch G v u.1
  have hfirstPos : ∀ u : K, 0 < (firstSet u).card := by
    intro u
    have hu : (firstSet u).card = 1 := by
      simpa [P, M, K, firstSet] using hfirst u
    rw [hu]
    norm_num
  let middle : K → V := fun u =>
    (Finset.card_pos.mp (hfirstPos u)).choose
  have hmiddle_mem : ∀ u : K, middle u ∈ firstSet u := by
    intro u
    exact (Finset.card_pos.mp (hfirstPos u)).choose_spec
  let lastSet : K → Finset V := fun u =>
    G.neighborFinset (middle u) ∩ secondLayerBranch G v t
  have hlastPos : ∀ u : K, 0 < (lastSet u).card := by
    intro u
    have huMiddle : middle u ∈
        G.neighborFinset a ∩ secondLayerBranch G v u.1 := by
      simpa [firstSet] using hmiddle_mem u
    have hu : (lastSet u).card = 1 := by
      simpa [lastSet] using hsecond u (middle u) huMiddle
    rw [hu]
    norm_num
  let endpoint : K → V := fun u =>
    (Finset.card_pos.mp (hlastPos u)).choose
  have hendpoint_mem : ∀ u : K, endpoint u ∈ lastSet u := by
    intro u
    exact (Finset.card_pos.mp (hlastPos u)).choose_spec
  have hmiddle_inj : ∀ i ∈ (Finset.univ : Finset K),
      ∀ j ∈ (Finset.univ : Finset K), i ≠ j → middle i ≠ middle j := by
    intro i _ j _ hij hm
    have hiBranch : middle i ∈ secondLayerBranch G v i.1 :=
      (Finset.mem_inter.mp (hmiddle_mem i)).2
    have hjBranch : middle j ∈ secondLayerBranch G v j.1 :=
      (Finset.mem_inter.mp (hmiddle_mem j)).2
    rw [hm] at hiBranch
    have hijParent : i.1 ≠ j.1 := by
      intro h
      apply hij
      exact Subtype.ext h
    have hdisj := secondLayerBranch_pairwiseDisjoint G hfree v
      (by simp : i.1 ∈ (Finset.univ : Finset P))
      (by simp : j.1 ∈ (Finset.univ : Finset P)) hijParent
    exact (Finset.disjoint_left.mp hdisj) hiBranch hjBranch
  have hendpointTarget : ∀ i ∈ (Finset.univ : Finset K),
      endpoint i ∈ secondLayerBranch G v t := by
    intro i _
    exact (Finset.mem_inter.mp (hendpoint_mem i)).2
  have haEndpoint : ∀ i ∈ (Finset.univ : Finset K),
      a ≠ endpoint i := by
    intro i _ hae
    have htmem : a ∈ secondLayerBranch G v t := by
      rw [hae]
      exact hendpointTarget i (by simp)
    have hdisj := secondLayerBranch_pairwiseDisjoint G hfree v
      (by simp : s ∈ (Finset.univ : Finset P))
      (by simp : t ∈ (Finset.univ : Finset P)) hstne
    exact (Finset.disjoint_left.mp hdisj) ha htmem
  have hmiddleAdjA : ∀ i ∈ (Finset.univ : Finset K),
      G.Adj (middle i) a := by
    intro i _
    have := (Finset.mem_inter.mp (hmiddle_mem i)).1
    simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using this
  have hmiddleAdjEndpoint : ∀ i ∈ (Finset.univ : Finset K),
      G.Adj (middle i) (endpoint i) := by
    intro i _
    have := (Finset.mem_inter.mp (hendpoint_mem i)).1
    simpa [SimpleGraph.mem_neighborFinset, G.adj_comm] using this
  have hle := card_le_of_commonNeighbor_selectors
    G hfree (Finset.univ : Finset K) (secondLayerBranch G v t) a
      middle endpoint hmiddle_inj hendpointTarget haEndpoint
      hmiddleAdjA hmiddleAdjEndpoint
  have hKcard : Fintype.card K = d - 1 := by
    change Fintype.card ↥M = d - 1
    rw [Fintype.card_coe]
    exact hMcard
  rw [Finset.card_univ, hKcard, htargetCard] at hle
  omega

/-- **Uniform clean-sector terminal.**  A saturated square-order high root
whose outer vertices all have degree `d` cannot have every second-layer
branch internally independent.  Degree saturation creates the full fans
killed by `false_of_squareOrder_pairedBranch_fullFan`. -/
theorem false_of_squareOrder_clean_highRoot
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 3 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcard : Fintype.card V = d * d) {v : V}
    (hv : G.degree v = d + 1)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = d)
    (hclean : ∀ u : {z : V // z ∈ G.neighborSet v},
      ∀ {p q : V}, p ∈ secondLayerBranch G v u →
        q ∈ secondLayerBranch G v u → ¬ G.Adj p q) : False := by
  classical
  rcases squareOrder_degree_succ_highRoot_structure
    G hfree (by omega) hmin hcard hv with ⟨_, hneigh, hlocal⟩
  have hexternal := externalRepairCandidates_eq_empty_of_squareOrder_highRoot
    G hfree (by omega) hcard hv hneigh hlocal
  let P := {z : V // z ∈ G.neighborSet v}
  have hPcard : Fintype.card P = d + 1 := by
    rw [Fintype.card_subtype]
    have heq : Finset.univ.filter (fun z => z ∈ G.neighborSet v) =
        G.neighborFinset v := by ext z; simp
    rw [heq, G.card_neighborFinset_eq_degree, hv]
  have hPnonempty : Nonempty P := Fintype.card_pos_iff.mp (by
    rw [hPcard]
    omega)
  let s : P := Classical.choice hPnonempty
  have hsNeighborCard :
      ((G.induce (G.neighborSet v)).neighborFinset s).card = 1 := by
    rw [(G.induce (G.neighborSet v)).card_neighborFinset_eq_degree,
      hlocal s]
  have hsNeighborNonempty :
      ((G.induce (G.neighborSet v)).neighborFinset s).Nonempty := by
    rw [← Finset.card_pos, hsNeighborCard]
    norm_num
  let t : P := hsNeighborNonempty.choose
  have htMem : t ∈ (G.induce (G.neighborSet v)).neighborFinset s :=
    hsNeighborNonempty.choose_spec
  have hst : G.Adj s.1 t.1 := by
    exact ((G.induce (G.neighborSet v)).mem_neighborFinset s t).mp htMem
  have hsne : s ≠ t := fun h => G.loopless.irrefl s.1
    (congrArg Subtype.val h ▸ hst)
  have hsBranchCard : (secondLayerBranch G v s).card = d - 2 :=
    card_secondLayerBranch_eq_sub_two_of_squareOrder_highRoot
      G (by omega) hv hneigh hlocal s
  have hsBranchNonempty : (secondLayerBranch G v s).Nonempty := by
    rw [← Finset.card_pos, hsBranchCard]
    omega
  let a : V := hsBranchNonempty.choose
  have ha : a ∈ secondLayerBranch G v s := hsBranchNonempty.choose_spec
  have haSecond : a ∈ secondLayer G v := by
    rw [secondLayer]
    exact Finset.mem_biUnion.mpr ⟨s, by simp, ha⟩
  have hadegree : G.degree a = d := houterDegree haSecond
  let M : Finset P := (Finset.univ.erase s).erase t
  have hfar_not_adj_t : ∀ u : {u : P // u ∈ M}, ¬ G.Adj u.1.1 t.1 := by
    intro u hutAdj
    have hsMem : s ∈
        (G.induce (G.neighborSet v)).neighborFinset t := by
      exact ((G.induce (G.neighborSet v)).mem_neighborFinset t s).mpr hst.symm
    have huMem : u.1 ∈
        (G.induce (G.neighborSet v)).neighborFinset t := by
      exact ((G.induce (G.neighborSet v)).mem_neighborFinset t u.1).mpr
        hutAdj.symm
    have hcardT :
        ((G.induce (G.neighborSet v)).neighborFinset t).card = 1 := by
      rw [(G.induce (G.neighborSet v)).card_neighborFinset_eq_degree,
        hlocal t]
    rcases Finset.card_eq_one.mp hcardT with ⟨r, hr⟩
    have hsr : s = r := by simpa [hr] using hsMem
    have hur : u.1 = r := by simpa [hr] using huMem
    have hus : u.1 ≠ s := (Finset.mem_erase.mp
      (Finset.mem_erase.mp u.2).2).1
    exact hus (hur.trans hsr.symm)
  have hfirst : ∀ u : {u : P // u ∈ M},
      (G.neighborFinset a ∩ secondLayerBranch G v u.1).card = 1 := by
    intro u
    have hus : u.1 ≠ s := (Finset.mem_erase.mp
      (Finset.mem_erase.mp u.2).2).1
    have hut : u.1 ≠ t := (Finset.mem_erase.mp u.2).1
    exact card_neighbors_inter_farBranch_eq_one_of_clean
      G hfree hd hv hexternal hclean s t u.1 hst hus hut a ha hadegree
  have hsecond : ∀ u : {u : P // u ∈ M},
      ∀ q ∈ G.neighborFinset a ∩ secondLayerBranch G v u.1,
        (G.neighborFinset q ∩ secondLayerBranch G v t).card = 1 := by
    intro u q hq
    have huNeighborCard :
        ((G.induce (G.neighborSet v)).neighborFinset u.1).card = 1 := by
      rw [(G.induce (G.neighborSet v)).card_neighborFinset_eq_degree,
        hlocal u.1]
    have huNeighborNonempty :
        ((G.induce (G.neighborSet v)).neighborFinset u.1).Nonempty := by
      rw [← Finset.card_pos, huNeighborCard]
      norm_num
    let w : P := huNeighborNonempty.choose
    have hwMem : w ∈
        (G.induce (G.neighborSet v)).neighborFinset u.1 :=
      huNeighborNonempty.choose_spec
    have huw : G.Adj u.1.1 w.1 :=
      ((G.induce (G.neighborSet v)).mem_neighborFinset u.1 w).mp hwMem
    have htu : t ≠ u.1 := by
      exact (Finset.mem_erase.mp u.2).1.symm
    have htw : t ≠ w := by
      intro htw
      exact hfar_not_adj_t u (htw ▸ huw)
    have hqBranch : q ∈ secondLayerBranch G v u.1 :=
      (Finset.mem_inter.mp hq).2
    have hqSecond : q ∈ secondLayer G v := by
      rw [secondLayer]
      exact Finset.mem_biUnion.mpr ⟨u.1, by simp, hqBranch⟩
    exact card_neighbors_inter_farBranch_eq_one_of_clean
      G hfree hd hv hexternal hclean u.1 w t huw htu htw q hqBranch
        (houterDegree hqSecond)
  exact false_of_squareOrder_pairedBranch_fullFan
    G hfree hd hv hneigh hlocal s t hst a ha hfirst hsecond

/-- In particular, the clean sector is impossible when `v` is the unique
degree-`d+1` vertex of a tight-edge-cover square-order witness. -/
theorem false_of_squareOrder_uniqueHigh_clean
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d : ℕ} (hd : 3 ≤ d) (hmin : ∀ x : V, d ≤ G.degree x)
    (hcover : ∀ {x y}, G.Adj x y → G.degree x = d ∨ G.degree y = d)
    (hcard : Fintype.card V = d * d) {v : V}
    (hv : G.degree v = d + 1)
    (hunique : ∀ {w : V}, G.degree w = d + 1 → w = v)
    (hclean : ∀ u : {z : V // z ∈ G.neighborSet v},
      ∀ {p q : V}, p ∈ secondLayerBranch G v u →
        q ∈ secondLayerBranch G v u → ¬ G.Adj p q) : False := by
  have houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = d := by
    intro a haSecond
    rcases squareOrder_degree_eq_or_succ_of_tightEdgeCover
      G hfree (by omega) hmin hcover hcard a with ha | ha
    · exact ha
    · have hav : a = v := hunique ha
      rw [secondLayer] at haSecond
      rcases Finset.mem_biUnion.mp haSecond with ⟨u, _, hau⟩
      have haOutside := (Finset.mem_sdiff.mp hau).2
      exact (haOutside (by simp [hav])).elim
  exact false_of_squareOrder_clean_highRoot
    G hfree hd hmin hcard hv houterDegree hclean

end

end Erdos85
