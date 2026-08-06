import Proofs.Erdos85PositiveExcessLocalParity

/-!
# Sector count at odd excess three

In the odd excess-three stratum, the triangle-free-edge graph has degree one
or three at every vertex.  If `a` vertices have degree three, splitting the
original edges into triangle-free and triangular edges and using local
linearity gives the exact congruence

`|V| (d-1) = 2a + 6q`.

In particular the degree-three sector is nonempty when `d ≡ 2 (mod 3)`.
-/

open SimpleGraph

namespace Erdos85

/-- Exact edge-count identity for the two triangle-free color sectors at
odd excess three. -/
theorem excessThree_degreeThreeSector_count_identity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) :
    ∃ q : ℕ,
      Fintype.card V * (d - 1) =
        2 * (Finset.univ.filter fun x : V =>
          (triangleFreeEdgeGraph G).degree x = 3).card + 6 * q := by
  classical
  let T := triangleFreeEdgeGraph G
  let H := triangularEdgeGraph G
  let S := Finset.univ.filter fun x : V => T.degree x = 3
  have hdegT : ∀ x : V, T.degree x = 1 ∨ T.degree x = 3 := by
    intro x
    rw [← T.card_neighborFinset_eq_degree,
      triangleFreeEdgeGraph_neighborFinset]
    exact excessThree_triangleFreeNeighbors_card_eq_one_or_three_of_odd
      G hfree hd hodd hreg hcard x
  have hpoint : ∀ x : V,
      T.degree x = 1 + if T.degree x = 3 then 2 else 0 := by
    intro x
    rcases hdegT x with hx | hx
    · rw [hx]
      norm_num
    · rw [hx]
      norm_num
  have hsumT : ∑ x : V, T.degree x = Fintype.card V + 2 * S.card := by
    calc
      (∑ x : V, T.degree x) =
          ∑ x : V, (1 + if T.degree x = 3 then 2 else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        exact hpoint x
      _ = Fintype.card V +
          ∑ x : V, if T.degree x = 3 then 2 else 0 := by
        rw [Finset.sum_add_distrib]
        simp
      _ = Fintype.card V + 2 * S.card := by
        dsimp [S]
        rw [← Finset.sum_filter]
        simp [Finset.sum_const, Nat.mul_comm]
  have hedgeG : 2 * G.edgeFinset.card = Fintype.card V * d := by
    rw [← G.sum_degrees_eq_twice_card_edges]
    simp_rw [hreg]
    simp
  have hedgeT : 2 * T.edgeFinset.card = Fintype.card V + 2 * S.card := by
    rw [← T.sum_degrees_eq_twice_card_edges]
    exact hsumT
  have hTle : T ≤ G := by
    intro x y hxy
    exact ((mem_triangleFreeNeighbors G x y).mp
      ((triangleFreeEdgeGraph_adj G x y).mp hxy)).1
  have hpartition : G.edgeFinset.card = H.edgeFinset.card + T.edgeFinset.card := by
    have heq : H.edgeFinset = G.edgeFinset \ T.edgeFinset := by
      ext e
      simp [H, T, triangularEdgeGraph]
    rw [heq, Finset.card_sdiff_of_subset (edgeFinset_mono hTle)]
    have hle := Finset.card_le_card (edgeFinset_mono hTle)
    omega
  have hlocal : H.LocallyLinear :=
    triangularEdgeGraph_locallyLinear_of_not_containsC4 G hfree
  have htri : H.edgeFinset.card = 3 * (H.cliqueFinset 3).card :=
    hlocal.card_edgeFinset
  refine ⟨(H.cliqueFinset 3).card, ?_⟩
  have hd1 : 1 ≤ d := by omega
  have hprod : Fintype.card V * d =
      Fintype.card V * (d - 1) + Fintype.card V := by
    calc
      Fintype.card V * d = Fintype.card V * ((d - 1) + 1) := by
        rw [Nat.sub_add_cancel hd1]
      _ = Fintype.card V * (d - 1) + Fintype.card V := by ring
  rw [hpartition, htri] at hedgeG
  change Fintype.card V * (d - 1) =
    2 * S.card + 6 * (H.cliqueFinset 3).card
  omega

/-- If `d ≡ 2 (mod 3)`, some vertex belongs to the degree-three
triangle-free sector. -/
theorem exists_excessThree_triangleFreeNeighbors_card_eq_three_of_mod_three_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableRel (triangularEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 7 ≤ d) (hodd : Odd d)
    (hmod : d % 3 = 2) (hreg : ∀ z, G.degree z = d)
    (hcard : Fintype.card V = d * (d - 1) + 6) :
    ∃ x : V, (triangleFreeNeighbors G x).card = 3 := by
  classical
  obtain ⟨q, hcount⟩ := excessThree_degreeThreeSector_count_identity
    G hfree hd hodd hreg hcard
  by_contra hnone
  push_neg at hnone
  have hSzero : (Finset.univ.filter fun x : V =>
      (triangleFreeEdgeGraph G).degree x = 3).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    apply hnone x
    calc
      (triangleFreeNeighbors G x).card =
          ((triangleFreeEdgeGraph G).neighborFinset x).card := by
        rw [triangleFreeEdgeGraph_neighborFinset]
      _ = (triangleFreeEdgeGraph G).degree x :=
        (triangleFreeEdgeGraph G).card_neighborFinset_eq_degree x
      _ = 3 := hx
  rw [hSzero] at hcount
  have hnmod : Fintype.card V % 3 = 2 := by
    rw [hcard, Nat.add_mod, Nat.mul_mod, hmod]
    have hm1 : (d - 1) % 3 = 1 := by omega
    rw [hm1]
  have hleft : (Fintype.card V * (d - 1)) % 3 = 2 := by
    rw [Nat.mul_mod, hnmod]
    have hm1 : (d - 1) % 3 = 1 := by omega
    rw [hm1]
  have hright := congrArg (fun n : ℕ => n % 3) hcount
  simp at hright
  omega

end Erdos85
