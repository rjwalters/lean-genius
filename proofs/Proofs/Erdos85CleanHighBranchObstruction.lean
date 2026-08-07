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

end

end Erdos85
