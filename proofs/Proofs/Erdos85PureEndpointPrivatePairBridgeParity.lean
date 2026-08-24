import Proofs.Erdos85PureEndpointPrivatePairDefectBridge
import Proofs.Erdos85DefectPairsComplementBalance

/-!
# Parity of the private-to-pair defect bridge mass

At the pure endpoint the shore is the disjoint union of replication-one and
replication-two points.  Every replication-one point has all `q - 1` defect
neighbors on the shore.  Summing these degrees, the incidences internal to
the replication-one class occur twice, so the remaining private-to-pair
incidence mass is even.  Preconnectedness makes that mass positive.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The total number of directed defect incidences from replication-one to
replication-two shore points is even and at least two. -/
theorem c4Free_binarySquare_pureEndpoint_privatePair_bridgeMass_even_two_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m)
    (hreg : ∀ v, G.degree v = q)
    (hcard : Fintype.card V = q * q)
    (hconn : (secondOrderDefectGraph G).Preconnected)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    let R₁ := S.filter fun x =>
      (G.neighborFinset x ∩ fullLineCenters G S q).card = 1
    let R₂ := S.filter fun x =>
      (G.neighborFinset x ∩ fullLineCenters G S q).card = 2
    Even (∑ x ∈ R₁,
      ((secondOrderDefectGraph G).neighborFinset x ∩ R₂).card) ∧
    2 ≤ ∑ x ∈ R₁,
      ((secondOrderDefectGraph G).neighborFinset x ∩ R₂).card := by
  classical
  dsimp only
  let D := secondOrderDefectGraph G
  let R₁ := S.filter fun x =>
    (G.neighborFinset x ∩ fullLineCenters G S q).card = 1
  let R₂ := S.filter fun x =>
    (G.neighborFinset x ∩ fullLineCenters G S q).card = 2
  let X := ∑ x ∈ R₁, (D.neighborFinset x ∩ R₂).card
  have hprofile :=
    c4Free_binarySquare_pureEndpoint_fullLineCenters_exactReplicationProfile
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hR₁card : R₁.card = q := by simpa [R₁] using hprofile.2.1
  have hpartition : S = R₁ ∪ R₂ := by
    ext x
    constructor
    · intro hxS
      rcases (hprofile.1 x).mp hxS with hxOne | hxTwo
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxS, hxOne⟩)
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hxS, hxTwo⟩)
    · intro hx
      rcases Finset.mem_union.mp hx with hx₁ | hx₂
      · exact (Finset.mem_filter.mp hx₁).1
      · exact (Finset.mem_filter.mp hx₂).1
  have hdisjoint : Disjoint R₁ R₂ := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx₁ hx₂
    have hOne := (Finset.mem_filter.mp hx₁).2
    have hTwo := (Finset.mem_filter.mp hx₂).2
    omega
  have hdeg :=
    c4Free_binarySquare_pureEndpoint_defect_biregular_decomposition
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hpoint : ∀ x ∈ R₁,
      (D.neighborFinset x ∩ R₁).card +
          (D.neighborFinset x ∩ R₂).card = q - 1 := by
    intro x hx₁
    have hxData := Finset.mem_filter.mp hx₁
    have hxdeg : (D.neighborFinset x ∩ S).card = q - 1 := by
      simpa [D] using (hdeg x).1 hxData.2
    have hd : Disjoint (D.neighborFinset x ∩ R₁)
        (D.neighborFinset x ∩ R₂) := by
      refine Finset.disjoint_left.mpr ?_
      intro z hz₁ hz₂
      exact Finset.disjoint_left.mp hdisjoint
        (Finset.mem_inter.mp hz₁).2 (Finset.mem_inter.mp hz₂).2
    have hu : (D.neighborFinset x ∩ R₁) ∪
        (D.neighborFinset x ∩ R₂) = D.neighborFinset x ∩ S := by
      rw [hpartition]
      ext z
      simp only [Finset.mem_union, Finset.mem_inter]
      tauto
    calc
      (D.neighborFinset x ∩ R₁).card +
          (D.neighborFinset x ∩ R₂).card =
          ((D.neighborFinset x ∩ R₁) ∪
            (D.neighborFinset x ∩ R₂)).card :=
            (Finset.card_union_of_disjoint hd).symm
      _ = (D.neighborFinset x ∩ S).card := by rw [hu]
      _ = q - 1 := hxdeg
  have hsum :
      (∑ x ∈ R₁, (D.neighborFinset x ∩ R₁).card) + X =
        q * (q - 1) := by
    rw [← Finset.sum_add_distrib]
    calc
      (∑ x ∈ R₁,
          ((D.neighborFinset x ∩ R₁).card +
            (D.neighborFinset x ∩ R₂).card)) =
          ∑ _x ∈ R₁, (q - 1) :=
            Finset.sum_congr rfl hpoint
      _ = R₁.card * (q - 1) := by simp
      _ = q * (q - 1) := by rw [hR₁card]
  have hinternal := sum_internal_incidence_eq_twice_supported_edges D R₁
  let e := (supportedEdgeGraph D R₁).edgeFinset.card
  change (∑ x ∈ R₁, (D.neighborFinset x ∩ R₁).card) = 2 * e at hinternal
  have htotalEven : q * (q - 1) = 2 * (m * (q - 1)) := by
    rw [hqm]
    ring
  have hXeven : Even X := by
    have heLe : e ≤ m * (q - 1) := by omega
    refine ⟨m * (q - 1) - e, ?_⟩
    omega
  obtain ⟨x, hx₁, y, hy₂, hxy⟩ :=
    c4Free_binarySquare_pureEndpoint_exists_private_pair_defectBridge
      G hfree hq hqm hreg hcard hconn S hempty hCcard hshore htri
  have hmem : y ∈ D.neighborFinset x ∩ R₂ := by
    exact Finset.mem_inter.mpr
      ⟨by simpa [D, SimpleGraph.mem_neighborFinset] using hxy, hy₂⟩
  have hXpos : 0 < X := by
    dsimp only [X]
    exact Finset.sum_pos' (fun _ _ => Nat.zero_le _)
      ⟨x, hx₁, Finset.card_pos.mpr ⟨y, hmem⟩⟩
  change Even X ∧ 2 ≤ X
  exact ⟨hXeven, by rcases hXeven with ⟨k, hk⟩; omega⟩

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_privatePair_bridgeMass_even_two_le
