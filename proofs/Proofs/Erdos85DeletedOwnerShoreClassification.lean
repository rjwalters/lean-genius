import Proofs.Erdos85OddSquareOrderNineArticulationGraphBridge
import Proofs.Erdos85NearRegularCutLowerParametric
import Proofs.Erdos85C4FreeDefectCutIdentity

/-!
# Generic deleted-owner shore classification

This module extracts the graph-theoretic part of the order-nine articulation
argument with no order, degree, or profile specialization.  If `D[O]` is
connected but deleting an owner disconnects it, the two component shores are
nonempty, complementary and relatively closed.  When `E` is exactly the
owner neighborhood in `O`, both shores meet `E`, and their full ambient
boundaries are exactly their respective `E`-masses.

This is the reusable articulation interface for the general binary-square
`A-REG-NONBIP` program; later arithmetic may classify the two boundary
masses without rebuilding the component-selection layer.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Algebraic regular-square cut conversion.  With total incidence `q*s`,
the exact defect cut identity is equivalent to the square moment
`sum f² = s² + delta`. -/
theorem regularSquare_square_moment_of_cut
    {O : Type*} [Fintype O] [DecidableEq O]
    (f : O → ℕ) (q s delta : ℕ)
    (hfle : ∀ x, f x ≤ q)
    (hs : s ≤ q * q)
    (hsum : (∑ x, f x) = q * s)
    (hcut : delta + (∑ x, f x * (q - f x)) =
      s * (q * q - s)) :
    (∑ x, (f x) ^ 2) = s ^ 2 + delta := by
  have hcutZ := congrArg (fun n : ℕ => (n : ℤ)) hcut
  push_cast at hcutZ
  simp_rw [Nat.cast_sub (hfle _)] at hcutZ
  rw [Nat.cast_sub hs] at hcutZ
  have hsumZ : (∑ x, (f x : ℤ)) = (q : ℤ) * s := by
    exact_mod_cast hsum
  have hincidenceAlg : (∑ x, (f x : ℤ) * (q - f x)) =
      (q : ℤ) * (∑ x, (f x : ℤ)) -
        ∑ x, (f x : ℤ) ^ 2 := by
    simp_rw [mul_sub, mul_comm (f _ : ℤ) q]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [pow_two]
  rw [hincidenceAlg, hsumZ] at hcutZ
  have hgoalZ : ((∑ x, f x ^ 2 : ℕ) : ℤ) =
      ((s ^ 2 + delta : ℕ) : ℤ) := by
    push_cast
    norm_num [pow_two] at hcutZ ⊢
    ring_nf at hcutZ ⊢
    linarith
  exact_mod_cast hgoalZ

/-- Graph-facing meeting point between the exact C4-free defect cut identity
and the parametric near-regular arithmetic engine.  At regular square order,
every shore realizes the empty-exceptional-root moment package, so its
parametric cut lower expression is bounded by its actual defect boundary. -/
theorem binarySquare_regular_nearRegularCutLower_le_boundary
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 1 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V) :
    nearRegularCutLower (q * q) q S.card (fun _ : Fin 0 => 0) ≤
      ∑ x ∈ S, ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ S)).card := by
  classical
  let f : V → ℕ := fun x => (G.neighborFinset x ∩ S).card
  let delta := ∑ x ∈ S,
    ((secondOrderDefectGraph G).neighborFinset x ∩
      (Finset.univ \ S)).card
  have hfle : ∀ x, f x ≤ q := by
    intro x
    calc
      f x ≤ (G.neighborFinset x).card :=
        Finset.card_le_card Finset.inter_subset_left
      _ = G.degree x := G.card_neighborFinset_eq_degree x
      _ = q := hreg x
  have hs : S.card ≤ q * q := by
    rw [← hcard, ← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ S)
  have hsum : (∑ x, f x) = q * S.card := by
    calc
      ∑ x, f x = ∑ x ∈ (Finset.univ : Finset V),
          (G.neighborFinset x ∩ S).card := by simp [f]
      _ = ∑ y ∈ S, (G.neighborFinset y ∩ Finset.univ).card :=
        sum_card_neighbor_inter_comm G Finset.univ S
      _ = ∑ _y ∈ S, q := by
        apply Finset.sum_congr rfl
        intro y _
        simp [G.card_neighborFinset_eq_degree, hreg y]
      _ = q * S.card := by simp [mul_comm]
  have hcut : delta + (∑ x, f x * (q - f x)) =
      S.card * (q * q - S.card) := by
    have hc := c4Free_defect_cut_add_degree_product_eq_complete_cut
      G hfree S
    dsimp only at hc
    rw [hcard] at hc
    simpa only [delta, f, hreg] using hc
  have hmoment : (∑ x, (f x) ^ 2) = S.card ^ 2 + delta :=
    regularSquare_square_moment_of_cut f q S.card delta hfle hs hsum hcut
  have hlower := nearRegularCutLower_le_of_moments
    (O := V) (ι := Fin 0) (q * q) q (by positivity) hcard
      f S.card delta (fun _ => 0) (by simpa using hsum) (by
        simpa using hmoment.le)
  simpa [delta] using hlower

/-- A connected induced graph whose owner deletion disconnects admits two
nonempty complementary punctured shores.  Each shore is closed in the
deleted-owner graph, meets the owner neighborhood, and has ambient boundary
equal to the size of that intersection. -/
theorem exists_deletedOwner_complementary_shores_with_exact_boundaries
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (O E : Finset V) (owner : V)
    (hownerO : owner ∈ O)
    (hneighborsO : ∀ u ∈ O, D.neighborFinset u ⊆ O)
    (hownerAdj : ∀ u ∈ O, D.Adj u owner ↔ u ∈ E)
    (hconnected : (D.induce (↑O : Set V)).Connected)
    (hpuncturedNonempty : (O.erase owner).Nonempty)
    (hnot : ¬ (D.induce (↑(O.erase owner) : Set V)).Connected) :
    ∃ S T : Finset V,
      S.Nonempty ∧ T.Nonempty ∧
      S ∪ T = O.erase owner ∧ Disjoint S T ∧
      (∀ x ∈ S, D.neighborFinset x ∩ (O.erase owner) ⊆ S) ∧
      (∀ x ∈ T, D.neighborFinset x ∩ (O.erase owner) ⊆ T) ∧
      (E ∩ S).Nonempty ∧ (E ∩ T).Nonempty ∧
      (∑ x ∈ S,
        (D.neighborFinset x ∩ (Finset.univ \ S)).card) = (E ∩ S).card ∧
      (∑ x ∈ T,
        (D.neighborFinset x ∩ (Finset.univ \ T)).card) = (E ∩ T).card := by
  classical
  obtain ⟨S, T, hSnonempty, hTnonempty, hunion, hdisj, hSclosed, hTclosed⟩ :=
    exists_two_nonempty_complementary_relativeClosedShores_of_induce_not_connected
      D (O.erase owner) hpuncturedNonempty hnot
  have hSsubErase : S ⊆ O.erase owner := by
    intro x hx
    rw [← hunion]
    exact Finset.mem_union_left T hx
  have hTsubErase : T ⊆ O.erase owner := by
    intro x hx
    rw [← hunion]
    exact Finset.mem_union_right S hx
  have hSsub : S ⊆ O := fun _ hx => (Finset.mem_erase.mp (hSsubErase hx)).2
  have hTsub : T ⊆ O := fun _ hx => (Finset.mem_erase.mp (hTsubErase hx)).2
  have hownerS : owner ∉ S := fun h =>
    (Finset.mem_erase.mp (hSsubErase h)).1 rfl
  have hownerT : owner ∉ T := fun h =>
    (Finset.mem_erase.mp (hTsubErase h)).1 rfl
  have hScardLt : S.card < O.card := by
    have hproper : S ⊂ O := Finset.ssubset_iff_subset_ne.mpr ⟨hSsub, by
      intro hSO
      exact hownerS (hSO ▸ hownerO)⟩
    exact Finset.card_lt_card hproper
  have hTcardLt : T.card < O.card := by
    have hproper : T ⊂ O := Finset.ssubset_iff_subset_ne.mpr ⟨hTsub, by
      intro hTO
      exact hownerT (hTO ▸ hownerO)⟩
    exact Finset.card_lt_card hproper
  have hSmeet := exceptional_inter_nonempty_of_connected_and_erase_owner_closed
    D O S E owner hconnected hSnonempty hScardLt hSsub hSclosed hownerAdj
  have hTmeet := exceptional_inter_nonempty_of_connected_and_erase_owner_closed
    D O T E owner hconnected hTnonempty hTcardLt hTsub hTclosed hownerAdj
  have hSboundary := sum_boundary_eq_card_exceptional_of_erase_owner_closed
    D O E S owner hownerS hSsub hneighborsO hSclosed hownerAdj
  have hTboundary := sum_boundary_eq_card_exceptional_of_erase_owner_closed
    D O E T owner hownerT hTsub hneighborsO hTclosed hownerAdj
  exact ⟨S, T, hSnonempty, hTnonempty, hunion, hdisj,
    hSclosed, hTclosed, hSmeet, hTmeet, hSboundary, hTboundary⟩

/-- Pure graph-theoretic specialization.  At an articulation vertex of a
connected finite graph, two complementary component shores after deletion
have positive ambient boundaries whose sum is exactly the degree of the
deleted vertex.  This is the order-free cut budget behind the order-nine
`e_S + e_T` calculation. -/
theorem exists_complementary_shores_boundary_sum_eq_degree_of_erase_not_connected
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj] (owner : V)
    (hconnected : D.Connected)
    (hpuncturedNonempty : ((Finset.univ : Finset V).erase owner).Nonempty)
    (hnot : ¬ (D.induce
      (↑((Finset.univ : Finset V).erase owner) : Set V)).Connected) :
    ∃ S T : Finset V,
      S.Nonempty ∧ T.Nonempty ∧
      S ∪ T = (Finset.univ : Finset V).erase owner ∧ Disjoint S T ∧
      (∀ x ∈ S, D.neighborFinset x ∩
        ((Finset.univ : Finset V).erase owner) ⊆ S) ∧
      (∀ x ∈ T, D.neighborFinset x ∩
        ((Finset.univ : Finset V).erase owner) ⊆ T) ∧
      0 < (∑ x ∈ S,
        (D.neighborFinset x ∩ (Finset.univ \ S)).card) ∧
      0 < (∑ x ∈ T,
        (D.neighborFinset x ∩ (Finset.univ \ T)).card) ∧
      (∑ x ∈ S,
          (D.neighborFinset x ∩ (Finset.univ \ S)).card) +
        (∑ x ∈ T,
          (D.neighborFinset x ∩ (Finset.univ \ T)).card) = D.degree owner := by
  classical
  let E := D.neighborFinset owner
  have hownerAdj : ∀ u ∈ (Finset.univ : Finset V),
      D.Adj u owner ↔ u ∈ E := by
    intro u _
    simp [E, SimpleGraph.mem_neighborFinset, D.adj_comm]
  obtain ⟨S, T, hSnonempty, hTnonempty, hunion, hdisj,
      hSclosed, hTclosed, hSmeet, hTmeet, hSboundary, hTboundary⟩ :=
    exists_deletedOwner_complementary_shores_with_exact_boundaries
      D Finset.univ E owner (Finset.mem_univ owner)
      (by intro u _; exact Finset.subset_univ _)
      hownerAdj (by
        have hc : (D.induce Set.univ).Connected :=
          (D.induceUnivIso.connected_iff).2 hconnected
        rw [show (↑(Finset.univ : Finset V) : Set V) = Set.univ by
          ext x
          simp]
        exact hc) hpuncturedNonempty hnot
  have hEsub : E ⊆ (Finset.univ : Finset V).erase owner := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨by
      intro hxo
      subst x
      exact D.loopless.irrefl owner
        ((D.mem_neighborFinset owner owner).mp hx), Finset.mem_univ x⟩
  have hEunion : (E ∩ S) ∪ (E ∩ T) = E := by
    rw [← Finset.inter_union_distrib_left, hunion]
    exact Finset.inter_eq_left.mpr hEsub
  have hEdisj : Disjoint (E ∩ S) (E ∩ T) := by
    rw [Finset.disjoint_left]
    intro x hxS hxT
    exact Finset.disjoint_left.mp hdisj
      (Finset.mem_inter.mp hxS).2 (Finset.mem_inter.mp hxT).2
  have hEcard : (E ∩ S).card + (E ∩ T).card = E.card := by
    rw [← Finset.card_union_of_disjoint hEdisj, hEunion]
  refine ⟨S, T, hSnonempty, hTnonempty, hunion, hdisj,
    hSclosed, hTclosed, ?_, ?_, ?_⟩
  · rw [hSboundary]
    exact Finset.card_pos.mpr hSmeet
  · rw [hTboundary]
    exact Finset.card_pos.mpr hTmeet
  · rw [hSboundary, hTboundary, hEcard]
    exact D.card_neighborFinset_eq_degree owner

/-- Binary-square graph-facing form of the articulation cut budget.  The
second-order defect graph is `(q-1)`-regular, so every deleted-owner
disconnection splits the defect boundary into two positive parts summing to
`q-1`.  Eliminating these splits is the remaining arithmetic task in a
general-q lift of the order-nine two-connectivity argument. -/
theorem binarySquare_regular_exists_punctured_shores_boundary_sum_eq_q_sub_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (owner : V)
    (hconnected : (secondOrderDefectGraph G).Connected)
    (hpuncturedNonempty :
      ((Finset.univ : Finset V).erase owner).Nonempty)
    (hnot : ¬ ((secondOrderDefectGraph G).induce
      (↑((Finset.univ : Finset V).erase owner) : Set V)).Connected) :
    ∃ S T : Finset V,
      S.Nonempty ∧ T.Nonempty ∧
      S ∪ T = (Finset.univ : Finset V).erase owner ∧ Disjoint S T ∧
      (∀ x ∈ S, (secondOrderDefectGraph G).neighborFinset x ∩
        ((Finset.univ : Finset V).erase owner) ⊆ S) ∧
      (∀ x ∈ T, (secondOrderDefectGraph G).neighborFinset x ∩
        ((Finset.univ : Finset V).erase owner) ⊆ T) ∧
      0 < (∑ x ∈ S, ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ S)).card) ∧
      0 < (∑ x ∈ T, ((secondOrderDefectGraph G).neighborFinset x ∩
        (Finset.univ \ T)).card) ∧
      (∑ x ∈ S, ((secondOrderDefectGraph G).neighborFinset x ∩
          (Finset.univ \ S)).card) +
        (∑ x ∈ T, ((secondOrderDefectGraph G).neighborFinset x ∩
          (Finset.univ \ T)).card) = q - 1 := by
  have hcensus : Fintype.card V = q * (q - 1) + 3 + (q - 3) := by
    rw [hcard]
    calc
      q * q = q * ((q - 1) + 1) := by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * (q - 1) + q := by ring
      _ = q * (q - 1) + 3 + (q - 3) := by omega
  have hDdegree : (secondOrderDefectGraph G).degree owner = q - 1 := by
    have h := secondOrderDefectGraph_degree_eq_excess_add_two
      G hfree hreg hcensus owner
    change (secondOrderDefectGraph G).degree owner = (q - 3) + 2 at h
    omega
  obtain ⟨S, T, hS, hT, hunion, hdisj, hSclosed, hTclosed,
      hSpos, hTpos, hsum⟩ :=
    exists_complementary_shores_boundary_sum_eq_degree_of_erase_not_connected
      (secondOrderDefectGraph G) owner hconnected hpuncturedNonempty hnot
  exact ⟨S, T, hS, hT, hunion, hdisj, hSclosed, hTclosed,
    hSpos, hTpos, hsum.trans hDdegree⟩

end

end Erdos85

#print axioms Erdos85.exists_deletedOwner_complementary_shores_with_exact_boundaries
#print axioms Erdos85.exists_complementary_shores_boundary_sum_eq_degree_of_erase_not_connected
#print axioms Erdos85.binarySquare_regular_exists_punctured_shores_boundary_sum_eq_q_sub_one
#print axioms Erdos85.regularSquare_square_moment_of_cut
#print axioms Erdos85.binarySquare_regular_nearRegularCutLower_le_boundary
