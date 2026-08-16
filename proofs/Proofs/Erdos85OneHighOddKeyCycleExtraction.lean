import Proofs.Erdos85OneHighOddKeySupportPropagation
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-! # Cycle extraction from odd exchanged-key propagation

The parity argument supplies two distinct continuations at every vertex of
the odd-key support.  This file isolates the finite graph-theoretic step that
turns that local continuation property into an actual cycle.
-/

namespace Erdos85

open SimpleGraph

/-- A finite simple graph in which every vertex has two distinct neighbours
contains a cycle. -/
theorem exists_isCycle_of_two_distinct_neighbors
    {V : Type*} [Fintype V] (G : SimpleGraph V) (v₀ : V)
    (hnext : ∀ v : V, ∃ x y : V, x ≠ y ∧ G.Adj v x ∧ G.Adj v y) :
    ∃ v : V, ∃ c : G.Walk v v, c.IsCycle := by
  by_contra hcycle
  have hacyc : G.IsAcyclic := by
    intro v c hc
    exact hcycle ⟨v, c, hc⟩
  let C : G.ConnectedComponent := G.connectedComponentMk v₀
  let T : SimpleGraph C.supp := C.toSimpleGraph
  have hTtree : T.IsTree := hacyc.isTree_connectedComponent C
  have hnontrivial : Nontrivial C.supp := by
    obtain ⟨x, y, hxy, hx, hy⟩ := hnext v₀
    have hv₀C : v₀ ∈ C.supp := by simp [C]
    have hxC : x ∈ C.supp :=
      C.mem_supp_of_adj_mem_supp hv₀C hx
    exact ⟨⟨v₀, hv₀C⟩, ⟨x, hxC⟩, by
      intro h
      have : v₀ = x := congrArg Subtype.val h
      subst x
      exact G.loopless.irrefl v₀ hx⟩
  letI : Nontrivial C.supp := hnontrivial
  classical
  obtain ⟨v, hvdeg⟩ := hTtree.exists_vert_degree_one_of_nontrivial
  obtain ⟨x, y, hxy, hvx, hvy⟩ := hnext v.1
  have hvC : v.1 ∈ C.supp := v.2
  have hxC : x ∈ C.supp := C.mem_supp_of_adj_mem_supp hvC hvx
  have hyC : y ∈ C.supp := C.mem_supp_of_adj_mem_supp hvC hvy
  have hTx : T.Adj v ⟨x, hxC⟩ := by
    simpa [T, ConnectedComponent.toSimpleGraph] using hvx
  have hTy : T.Adj v ⟨y, hyC⟩ := by
    simpa [T, ConnectedComponent.toSimpleGraph] using hvy
  obtain ⟨w, hvw, hwunique⟩ := degree_eq_one_iff_existsUnique_adj.mp hvdeg
  have hxw : (⟨x, hxC⟩ : C.supp) = w := hwunique _ hTx
  have hyw : (⟨y, hyC⟩ : C.supp) = w := hwunique _ hTy
  exact hxy (congrArg Subtype.val (hxw.trans hyw.symm))

/-- The genuine exchanged keys occurring with odd multiplicity. -/
def OddExchangedKey {L : Type*} [Fintype L] [LinearOrder L]
    (m : L × L → Nat) :=
  {k : L × L // k ∈ exchangedMissPairKeys L ∧ Odd (m k)}

/-- Two odd exchanged keys are adjacent when they share a label. -/
def oddExchangedKeyGraph {L : Type*} [Fintype L] [LinearOrder L]
    (m : L × L → Nat) : SimpleGraph (OddExchangedKey m) :=
  SimpleGraph.fromRel fun p q =>
    ∃ l : L, unorderedKeyIncidence p.1 l = 1 ∧
      unorderedKeyIncidence q.1 l = 1

/-- Even weighted incidence at every label forces any nonempty odd exchanged-
key support to contain a cycle in its shared-label graph. -/
theorem exists_oddExchangedKey_isCycle
    {L : Type*} [Fintype L] [LinearOrder L]
    (m : L × L → Nat) (k₀ : L × L)
    (hk₀ : k₀ ∈ exchangedMissPairKeys L) (hk₀odd : Odd (m k₀))
    (heven : ∀ l, Even
      (∑ q ∈ exchangedMissPairKeys L,
        unorderedKeyIncidence q l * m q)) :
    ∃ k : OddExchangedKey m,
      ∃ c : (oddExchangedKeyGraph m).Walk k k, c.IsCycle := by
  classical
  letI : Fintype (OddExchangedKey m) :=
    Fintype.subtype ((exchangedMissPairKeys L).filter fun k => Odd (m k)) (by
      simp)
  let v₀ : OddExchangedKey m := ⟨k₀, hk₀, hk₀odd⟩
  apply exists_isCycle_of_two_distinct_neighbors (oddExchangedKeyGraph m) v₀
  intro k
  obtain ⟨q, hq, r, hr, hqk, hrk, hqr, hqinc, hrinc, hqodd, hrodd⟩ :=
    exists_two_distinct_odd_exchangedKeys_at_endpoints m k.2.1 k.2.2 heven
  let q' : OddExchangedKey m := ⟨q, hq, hqodd⟩
  let r' : OddExchangedKey m := ⟨r, hr, hrodd⟩
  refine ⟨q', r', ?_, ?_, ?_⟩
  · intro h
    exact hqr (congrArg Subtype.val h)
  · simp only [oddExchangedKeyGraph, SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl ⟨k.1.1, ?_, hqinc⟩⟩
    · intro h
      exact hqk (congrArg Subtype.val h).symm
    · simp [unorderedKeyIncidence]
  · simp only [oddExchangedKeyGraph, SimpleGraph.fromRel_adj]
    refine ⟨?_, Or.inl ⟨k.1.2, ?_, hrinc⟩⟩
    · intro h
      exact hrk (congrArg Subtype.val h).symm
    · have hklt : k.1.1 < k.1.2 := by
        simpa [exchangedMissPairKeys] using k.2.1
      simp [unorderedKeyIncidence]

end Erdos85
