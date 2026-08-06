import Proofs.Erdos85SmallBlockBalance
import Proofs.Erdos85ResidueSignedCount
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Components of a local matching

A graph whose vertex degrees are at most one is a disjoint union of isolated
vertices and edges.  We record the cardinality consequence in the precise
connected-component vocabulary needed by adjacent-clone splitting.
-/

open SimpleGraph

namespace Erdos85

/-- Every connected component of a finite graph of maximum degree at most one
has at most two vertices. -/
theorem connectedComponent_supp_ncard_le_two_of_degree_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdegree : ∀ v, H.degree v ≤ 1)
    (c : H.ConnectedComponent) :
    c.supp.ncard ≤ 2 := by
  classical
  let K : SimpleGraph c := c.toSimpleGraph
  let inclusion : K.Copy H :=
    ⟨c.toSimpleGraph_hom, Subtype.val_injective⟩
  have hdegreeK : ∀ v : c, K.degree v ≤ 1 := by
    intro v
    exact (inclusion.degree_le v).trans (hdegree v.1)
  have hsum : (∑ v : c, K.degree v) ≤ Fintype.card c := by
    calc
      (∑ v : c, K.degree v) ≤ ∑ _v : c, 1 :=
        Finset.sum_le_sum fun _ _ ↦ hdegreeK _
      _ = Fintype.card c := by simp
  have hedge : 2 * K.edgeFinset.card ≤ Fintype.card c := by
    rw [← K.sum_degrees_eq_twice_card_edges]
    exact hsum
  have hconn : Fintype.card c ≤ K.edgeFinset.card + 1 := by
    have hc := c.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
    rw [Nat.card_eq_fintype_card] at hc
    have hedgecard : Nat.card c.toSimpleGraph.edgeSet =
        Fintype.card c.toSimpleGraph.edgeSet := Nat.card_eq_fintype_card
    rw [hedgecard, ← c.toSimpleGraph.edgeFinset_card] at hc
    simpa [K] using hc
  have hcard : Fintype.card c ≤ 2 := by omega
  have hcardNat : Nat.card c ≤ 2 := by
    simpa [Nat.card_eq_fintype_card] using hcard
  rw [← Nat.card_coe_set_eq c.supp]
  exact hcardNat

/-- The connected components of a degree-at-most-one graph can be cut into
two consecutive component lists, each carrying any requested weight `target`
once the total order is at least `2 * target + 1`. -/
theorem exists_balanced_connectedComponent_cut_of_degree_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdegree : ∀ v, H.degree v ≤ 1)
    (target : ℕ) (hcard : 2 * target + 1 ≤ Fintype.card V) :
    ∃ k,
      target ≤ ((Finset.univ.toList.take k).map
        fun c : H.ConnectedComponent ↦ c.supp.ncard).sum ∧
      target ≤ ((Finset.univ.toList.drop k).map
        fun c : H.ConnectedComponent ↦ c.supp.ncard).sum := by
  classical
  let components : List H.ConnectedComponent := Finset.univ.toList
  let weights : List ℕ := components.map fun c ↦ c.supp.ncard
  have hpos : ∀ w ∈ weights, 1 ≤ w := by
    intro w hw
    rcases List.mem_map.mp hw with ⟨c, _hc, rfl⟩
    exact c.nonempty_supp.ncard_pos
  have hle : ∀ w ∈ weights, w ≤ 2 := by
    intro w hw
    rcases List.mem_map.mp hw with ⟨c, _hc, rfl⟩
    exact connectedComponent_supp_ncard_le_two_of_degree_le_one H hdegree c
  have htotal : 2 * target + 1 ≤ weights.sum := by
    have hsum : weights.sum = Fintype.card V := by
      simpa [weights, components] using sum_connectedComponent_supp_ncard H
    rwa [hsum]
  obtain ⟨k, hkleft, hkright⟩ :=
    exists_take_balanced_of_le_two weights target hpos hle htotal
  refine ⟨k, ?_, ?_⟩
  · simpa [weights, components] using hkleft
  · simpa [weights, components] using hkright

/-- A finite graph of maximum degree at most one admits a balanced vertex
partition which cuts no edge.  Each side is a union of whole connected
components. -/
theorem exists_balanced_noCross_partition_of_degree_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hdegree : ∀ v, H.degree v ≤ 1)
    (target : ℕ) (hcard : 2 * target + 1 ≤ Fintype.card V) :
    ∃ S T : Finset V,
      Disjoint S T ∧ S ∪ T = Finset.univ ∧
      target ≤ S.card ∧ target ≤ T.card ∧
      ∀ ⦃a⦄, a ∈ S → ∀ ⦃b⦄, b ∈ T → ¬ H.Adj a b := by
  classical
  obtain ⟨k, hkleft, hkright⟩ :=
    exists_balanced_connectedComponent_cut_of_degree_le_one
      H hdegree target hcard
  let components : List H.ConnectedComponent := Finset.univ.toList
  let leftComponents : Finset H.ConnectedComponent :=
    (components.take k).toFinset
  let rightComponents : Finset H.ConnectedComponent :=
    (components.drop k).toFinset
  let S : Finset V := leftComponents.biUnion fun c ↦ c.supp.toFinset
  let T : Finset V := rightComponents.biUnion fun c ↦ c.supp.toFinset
  have hcomponentsNodup : components.Nodup := by
    exact Finset.nodup_toList _
  have happNodup : (components.take k ++ components.drop k).Nodup := by
    simpa only [List.take_append_drop] using hcomponentsNodup
  have hcomponentDisjoint : Disjoint leftComponents rightComponents := by
    have hlist := happNodup.disjoint
    rw [Finset.disjoint_left]
    intro c hcL hcR
    exact hlist (by simpa [leftComponents] using hcL)
      (by simpa [rightComponents] using hcR)
  have hcomponentCover : leftComponents ∪ rightComponents = Finset.univ := by
    calc
      leftComponents ∪ rightComponents =
          (components.take k ++ components.drop k).toFinset := by
            ext c
            simp only [leftComponents, rightComponents, Finset.mem_union,
              List.mem_toFinset, List.mem_append]
      _ = components.toFinset := by rw [List.take_append_drop]
      _ = Finset.univ := by simp [components]
  have hcardS : S.card =
      ∑ c ∈ leftComponents, c.supp.ncard := by
    dsimp [S]
    rw [Finset.card_biUnion]
    · simp [Set.ncard_eq_toFinset_card']
    · intro c _ e _ hce
      exact Set.disjoint_toFinset.mpr
        (pairwise_disjoint_supp_connectedComponent H hce)
  have hcardT : T.card =
      ∑ c ∈ rightComponents, c.supp.ncard := by
    dsimp [T]
    rw [Finset.card_biUnion]
    · simp [Set.ncard_eq_toFinset_card']
    · intro c _ e _ hce
      exact Set.disjoint_toFinset.mpr
        (pairwise_disjoint_supp_connectedComponent H hce)
  have hsumToFinset (l : List H.ConnectedComponent) (hl : l.Nodup) :
      (∑ c ∈ l.toFinset, c.supp.ncard) =
        (l.map fun c ↦ c.supp.ncard).sum := by
    induction l with
    | nil => simp
    | cons c l ih =>
        rw [List.nodup_cons] at hl
        simp [hl.1, ih hl.2]
  have hkleft' : target ≤ S.card := by
    rw [hcardS]
    rw [show (∑ c ∈ leftComponents, c.supp.ncard) =
        ((components.take k).map fun c ↦ c.supp.ncard).sum by
      exact hsumToFinset _ hcomponentsNodup.take]
    simpa [components] using hkleft
  have hkright' : target ≤ T.card := by
    rw [hcardT]
    rw [show (∑ c ∈ rightComponents, c.supp.ncard) =
        ((components.drop k).map fun c ↦ c.supp.ncard).sum by
      exact hsumToFinset _ hcomponentsNodup.drop]
    simpa [components] using hkright
  have hcover : S ∪ T = Finset.univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    have hcMem : H.connectedComponentMk v ∈
        leftComponents ∪ rightComponents := by
      rw [hcomponentCover]
      simp
    rcases Finset.mem_union.mp hcMem with hc | hc
    · left
      change v ∈ leftComponents.biUnion (fun c ↦ c.supp.toFinset)
      rw [Finset.mem_biUnion]
      exact ⟨H.connectedComponentMk v, hc, by simp⟩
    · right
      change v ∈ rightComponents.biUnion (fun c ↦ c.supp.toFinset)
      rw [Finset.mem_biUnion]
      exact ⟨H.connectedComponentMk v, hc, by simp⟩
  have hdisjoint : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro v hvS hvT
    change v ∈ leftComponents.biUnion (fun c ↦ c.supp.toFinset) at hvS
    change v ∈ rightComponents.biUnion (fun c ↦ c.supp.toFinset) at hvT
    rw [Finset.mem_biUnion] at hvS hvT
    obtain ⟨c, hcL, hvc⟩ := hvS
    obtain ⟨e, heR, hve⟩ := hvT
    have hce : c = e := ConnectedComponent.eq_of_common_vertex
      (by simpa using hvc) (by simpa using hve)
    exact (Finset.disjoint_left.mp hcomponentDisjoint) hcL (hce ▸ heR)
  refine ⟨S, T, hdisjoint, hcover, hkleft', hkright', ?_⟩
  intro a ha b hb hab
  change a ∈ leftComponents.biUnion (fun c ↦ c.supp.toFinset) at ha
  change b ∈ rightComponents.biUnion (fun c ↦ c.supp.toFinset) at hb
  rw [Finset.mem_biUnion] at ha hb
  obtain ⟨c, hcL, hac⟩ := ha
  obtain ⟨e, heR, hbe⟩ := hb
  have hca : H.connectedComponentMk a = c :=
    (ConnectedComponent.mem_supp_iff c a).mp (by simpa using hac)
  have heb : H.connectedComponentMk b = e :=
    (ConnectedComponent.mem_supp_iff e b).mp (by simpa using hbe)
  have hce : c = e := hca.symm.trans
    ((ConnectedComponent.connectedComponentMk_eq_of_adj hab).trans heb)
  exact (Finset.disjoint_left.mp hcomponentDisjoint) hcL (hce ▸ heR)

/-- Finset-facing form: a vertex set whose induced graph has degree at most
one admits a balanced partition, subordinate to that set, which cuts no
ambient edge. -/
theorem exists_balanced_noCross_partition_finset
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (U : Finset V) (target : ℕ)
    (hdegree : ∀ v : {x : V // x ∈ (U : Set V)},
      ((H.induce (fun x ↦ x ∈ (U : Set V))).neighborSet v).ncard ≤ 1)
    (hcard : 2 * target + 1 ≤ U.card) :
    ∃ S T : Finset V,
      S ⊆ U ∧ T ⊆ U ∧ Disjoint S T ∧ S ∪ T = U ∧
      target ≤ S.card ∧ target ≤ T.card ∧
      ∀ ⦃a⦄, a ∈ S → ∀ ⦃b⦄, b ∈ T → ¬ H.Adj a b := by
  classical
  let K : SimpleGraph {x : V // x ∈ (U : Set V)} :=
    H.induce (fun x ↦ x ∈ (U : Set V))
  have hdegreeK : ∀ v, K.degree v ≤ 1 := by
    intro v
    have heq : K.degree v = (K.neighborSet v).ncard := by
      rw [Set.ncard_eq_toFinset_card']
      rfl
    rw [heq]
    change ((H.induce (fun x ↦ x ∈ (U : Set V))).neighborSet v).ncard ≤ 1
    exact hdegree v
  have hKcard : Fintype.card {x : V // x ∈ (U : Set V)} = U.card := by simp
  obtain ⟨S₀, T₀, hdisj₀, hcover₀, hScard₀, hTcard₀, hcross₀⟩ :=
    exists_balanced_noCross_partition_of_degree_le_one K hdegreeK target
      (by rwa [hKcard])
  let e : {x : V // x ∈ (U : Set V)} ↪ V :=
    ⟨Subtype.val, Subtype.val_injective⟩
  let S := S₀.map e
  let T := T₀.map e
  have hSsub : S ⊆ U := by
    intro x hx
    change x ∈ S₀.map e at hx
    rw [Finset.mem_map] at hx
    obtain ⟨y, _hy, rfl⟩ := hx
    exact y.2
  have hTsub : T ⊆ U := by
    intro x hx
    change x ∈ T₀.map e at hx
    rw [Finset.mem_map] at hx
    obtain ⟨y, _hy, rfl⟩ := hx
    exact y.2
  refine ⟨S, T, hSsub, hTsub, ?_, ?_, ?_, ?_, ?_⟩
  · change Disjoint (S₀.map e) (T₀.map e)
    exact (Finset.disjoint_map e).2 hdisj₀
  · apply Finset.Subset.antisymm
    · exact Finset.union_subset hSsub hTsub
    · intro x hx
      let y : {x : V // x ∈ (U : Set V)} := ⟨x, hx⟩
      have hy : y ∈ S₀ ∪ T₀ := by rw [hcover₀]; simp
      rcases Finset.mem_union.mp hy with hyS | hyT
      · exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨y, hyS, rfl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_map.mpr ⟨y, hyT, rfl⟩)
  · simpa [S] using hScard₀
  · simpa [T] using hTcard₀
  · intro a ha b hb hab
    change a ∈ S₀.map e at ha
    change b ∈ T₀.map e at hb
    rw [Finset.mem_map] at ha hb
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    exact hcross₀ ha₀ hb₀ hab

end Erdos85
