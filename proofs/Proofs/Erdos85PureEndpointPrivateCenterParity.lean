import Proofs.Erdos85PureEndpointCenterPrivateIntersection

/-!
# Handshake parity for private endpoint centers

The graph induced by the pure exceptional centers has maximum degree two.
Its odd-degree vertices are therefore exactly its degree-one vertices, so
the handshake lemma makes that stratum even.  The private-range
characterization identifies this with the exceptional centers which are
themselves private points.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- In any finite induced graph of maximum degree two, the ambient vertices
with internal degree one form an even set. -/
theorem even_card_internalDegreeOne_of_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (C : Finset V)
    (hle : ∀ v ∈ C, (G.neighborFinset v ∩ C).card ≤ 2) :
    Even (C.filter fun v => (G.neighborFinset v ∩ C).card = 1).card := by
  classical
  let s : Set V := {v | v ∈ C}
  letI : Fintype s := Subtype.fintype _
  have hto : s.toFinset = C := by
    ext v
    simp [s]
  have hdegree : ∀ x : {v // v ∈ s},
      ((G.induce s).neighborFinset x).card =
        (G.neighborFinset x.1 ∩ C).card := by
    intro x
    have hmap := G.map_neighborFinset_induce (s := s) x
    have hcard := congrArg Finset.card hmap
    rw [Finset.card_map, hto] at hcard
    exact hcard
  have hodd_iff : ∀ x : {v // v ∈ s},
      Odd (((G.induce s).neighborFinset x).card) ↔
        (G.neighborFinset x.1 ∩ C).card = 1 := by
    intro x
    rw [hdegree x]
    have hxle := hle x.1 (by simpa [s] using x.2)
    constructor
    · rintro ⟨k, hk⟩
      omega
    · intro hx
      rw [hx]
      decide
  have hcardEq :
      ((Finset.univ : Finset {v // v ∈ s}).filter fun x =>
        Odd (((G.induce s).neighborFinset x).card)).card =
      (C.filter fun v => (G.neighborFinset v ∩ C).card = 1).card := by
    apply Finset.card_bij (fun x _ => x.1)
    · intro x hx
      have hxData := Finset.mem_filter.mp hx
      apply Finset.mem_filter.mpr
      exact ⟨by simpa [s] using x.2, (hodd_iff x).mp hxData.2⟩
    · intro x₁ hx₁ x₂ hx₂ hval
      exact Subtype.ext hval
    · intro v hv
      have hvData := Finset.mem_filter.mp hv
      let x : {v // v ∈ s} := ⟨v, by simpa [s] using hvData.1⟩
      refine ⟨x, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ x, (hodd_iff x).mpr hvData.2⟩
  rw [← hcardEq]
  have hhand := (G.induce s).even_card_odd_degree_vertices
  simpa only [← (G.induce s).card_neighborFinset_eq_degree] using hhand

/-- At the pure endpoint, the full centers which occur in the private-point
matching form an even set. -/
theorem c4Free_binarySquare_pureEndpoint_privateCenter_card_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    ∃ p : {i // i ∈ fullLineCenters G S q} → V,
      Function.Injective p ∧
      (∀ i, G.Adj i.1 (p i) ∧
        G.neighborFinset (p i) ∩ fullLineCenters G S q = {i.1}) ∧
      Even ((fullLineCenters G S q ∩ Finset.univ.image p).card) := by
  classical
  obtain ⟨p, hpInjective, hp, hiff⟩ :=
    c4Free_binarySquare_pureEndpoint_center_mem_privateRange_iff_degree_one
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hshape := c4Free_binarySquare_pureEndpoint_centerGraph_degree_shape
    G hfree hq hqm hreg hcard S hempty hshore htri
  have heven := even_card_internalDegreeOne_of_le_two G
    (fullLineCenters G S q) (fun v hv => (hshape v hv).1)
  refine ⟨p, hpInjective, hp, ?_⟩
  have heq : fullLineCenters G S q ∩ Finset.univ.image p =
      (fullLineCenters G S q).filter fun v =>
        (G.neighborFinset v ∩ fullLineCenters G S q).card = 1 := by
    ext v
    simp only [Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨hvC, hvRange⟩
      exact ⟨hvC, (hiff v hvC).mp hvRange⟩
    · rintro ⟨hvC, hvOne⟩
      exact ⟨hvC, (hiff v hvC).mpr hvOne⟩
  rw [heq]
  exact heven

end

end Erdos85

#print axioms Erdos85.even_card_internalDegreeOne_of_le_two
#print axioms Erdos85.c4Free_binarySquare_pureEndpoint_privateCenter_card_even
