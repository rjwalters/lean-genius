import Proofs.Erdos85TwoSeparatorLowSetSplit
import Proofs.Erdos85SplitCocliqueInducedEdgeBound

/-! # Induced edge upper bound for a two-pole low set -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A finset split into one center and two cocliques has at most the product
of the two side cardinalities many induced edges. -/
theorem induced_edgeFinset_card_le_of_center_split_cocliques
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (Z P Q : Finset V) (c : V)
    (hcP : c ∉ P) (hcQ : c ∉ Q) (hPQ : Disjoint P Q)
    (hsplit : Z = insert c (P ∪ Q))
    (hPind : D.IsIndepSet (↑(insert c P) : Set V))
    (hQind : D.IsIndepSet (↑(insert c Q) : Set V)) :
    (D.induce (↑Z : Set V)).edgeFinset.card ≤ P.card * Q.card := by
  let ZV := {v : V // v ∈ Z}
  let H : SimpleGraph ZV := D.induce (↑Z : Set V)
  have hPZ : P ⊆ Z := by
    intro v hv
    rw [hsplit]
    simp [hv]
  have hQZ : Q ⊆ Z := by
    intro v hv
    rw [hsplit]
    simp [hv]
  let fP : {v : V // v ∈ P} ↪ ZV :=
    ⟨fun v => ⟨v.1, hPZ v.2⟩, fun _ _ h =>
      Subtype.ext (congrArg (fun z : ZV => z.1) h)⟩
  let fQ : {v : V // v ∈ Q} ↪ ZV :=
    ⟨fun v => ⟨v.1, hQZ v.2⟩, fun _ _ h =>
      Subtype.ext (congrArg (fun z : ZV => z.1) h)⟩
  let Pz : Finset ZV := P.attach.map fP
  let Qz : Finset ZV := Q.attach.map fQ
  have hmemPz (v : ZV) : v ∈ Pz ↔ v.1 ∈ P := by
    change v ∈ P.attach.map fP ↔ v.1 ∈ P
    constructor
    · rw [Finset.mem_map]
      rintro ⟨a, _, ha⟩
      subst v
      change a.1 ∈ P
      exact a.2
    · intro hv
      rw [Finset.mem_map]
      exact ⟨⟨v.1, hv⟩, by simp, Subtype.ext rfl⟩
  have hmemQz (v : ZV) : v ∈ Qz ↔ v.1 ∈ Q := by
    change v ∈ Q.attach.map fQ ↔ v.1 ∈ Q
    constructor
    · rw [Finset.mem_map]
      rintro ⟨a, _, ha⟩
      subst v
      change a.1 ∈ Q
      exact a.2
    · intro hv
      rw [Finset.mem_map]
      exact ⟨⟨v.1, hv⟩, by simp, Subtype.ext rfl⟩
  have hcardP : Pz.card = P.card := by simp [Pz]
  have hcardQ : Qz.card = Q.card := by simp [Qz]
  have hdisj : Disjoint Pz Qz := by
    rw [Finset.disjoint_left]
    intro v hvP hvQ
    exact (Finset.disjoint_left.mp hPQ) (hmemPz v |>.mp hvP)
      (hmemQz v |>.mp hvQ)
  have hPcoc : ∀ ⦃u v⦄, u ∈ Pz → v ∈ Pz → ¬ H.Adj u v := by
    intro u v hu hv huv
    exact hPind (by simp [hmemPz u |>.mp hu])
      (by simp [hmemPz v |>.mp hv]) (D.ne_of_adj huv) huv
  have hQcoc : ∀ ⦃u v⦄, u ∈ Qz → v ∈ Qz → ¬ H.Adj u v := by
    intro u v hu hv huv
    exact hQind (by simp [hmemQz u |>.mp hu])
      (by simp [hmemQz v |>.mp hv]) (D.ne_of_adj huv) huv
  have hout : ∀ ⦃u⦄, u ∉ Pz → u ∉ Qz → H.degree u = 0 := by
    intro u huP huQ
    have huNotP : u.1 ∉ P := fun h => huP ((hmemPz u).mpr h)
    have huNotQ : u.1 ∉ Q := fun h => huQ ((hmemQz u).mpr h)
    have huc : u.1 = c := by
      have huZ : u.1 ∈ Z := u.2
      have huSplit : u.1 ∈ insert c (P ∪ Q) := by rw [← hsplit]; exact huZ
      simp only [Finset.mem_insert, Finset.mem_union] at huSplit
      rcases huSplit with h | h | h
      · exact h
      · exact (huNotP h).elim
      · exact (huNotQ h).elim
    rw [← H.card_neighborFinset_eq_degree u]
    apply Finset.card_eq_zero.mpr
    ext v
    constructor
    · intro hv
      have hvAdj : D.Adj u.1 v.1 :=
        (SimpleGraph.mem_neighborFinset H u v).mp hv
      have hvZ : v.1 ∈ Z := v.2
      have hvSplit : v.1 ∈ insert c (P ∪ Q) := by rw [← hsplit]; exact hvZ
      simp only [Finset.mem_insert, Finset.mem_union] at hvSplit
      rcases hvSplit with hvc | hvP | hvQ
      · exact (D.loopless.irrefl c (by simpa [huc, hvc] using hvAdj)).elim
      · exact (hPind (by simp [huc]) (by simp [hvP])
          (D.ne_of_adj hvAdj) hvAdj).elim
      · exact (hQind (by simp [huc]) (by simp [hvQ])
          (D.ne_of_adj hvAdj) hvAdj).elim
    · intro hv
      simpa using hv
  have hedge := card_edgeFinset_le_splitCoclique_product
    H Pz Qz hdisj hPcoc hQcoc hout
  simpa [H, hcardP, hcardQ] using hedge

/-- Coupled low sets across nonadjacent defect poles satisfy the sharp
split-product induced-edge upper bound. -/
theorem exists_twoPole_lowSet_inducedEdges_le_splitProduct
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {x y : V} (hxy : x ≠ y)
    (hnotD : ¬ (secondOrderDefectGraph G).Adj x y)
    (Z Z' : Finset V) (q : ℕ) (hZcard : Z.card = q)
    (hcoup : ∀ v,
      (if v ∈ Z then 1 else 0) + (if v ∈ Z' then 1 else 0) =
        (if G.Adj v x then 1 else 0) + (if G.Adj v y then 1 else 0)) :
    ∃ (P Q : Finset V), P.card + Q.card = q - 1 ∧
      ((secondOrderDefectGraph G).induce (↑Z : Set V)).edgeFinset.card ≤
        P.card * Q.card := by
  obtain ⟨c, P, Q, _, _, hcP, hcQ, hPQ, hsplit, hcards, hPind, hQind⟩ :=
    exists_twoPole_puncturedParts_with_defect_independence
      G hfree hxy hnotD Z Z' q hZcard hcoup
  refine ⟨P, Q, hcards, ?_⟩
  exact induced_edgeFinset_card_le_of_center_split_cocliques
    (secondOrderDefectGraph G) Z P Q c hcP hcQ hPQ hsplit hPind hQind

#print axioms induced_edgeFinset_card_le_of_center_split_cocliques
#print axioms exists_twoPole_lowSet_inducedEdges_le_splitProduct

end

end Erdos85
