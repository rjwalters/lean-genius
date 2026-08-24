import Proofs.Erdos85PureEndpointFinalLayerPrivateMatching

/-!
# Canonical pair points at the pure endpoint

Defect independence says every two distinct full centers have a common
neighbor, while `C₄`-freeness makes it unique.  The exact replication cap
then identifies that neighbor as the shore point owned by exactly that
unordered pair of centers.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Every pair of distinct full centers has a unique pair point on `S`. -/
theorem c4Free_binarySquare_pureEndpoint_existsUnique_pairPoint
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
      (G.neighborFinset v ∩ S).card = q)
    {i j : V} (hi : i ∈ fullLineCenters G S q)
    (hj : j ∈ fullLineCenters G S q) (hij : i ≠ j) :
    ∃! z, z ∈ S ∧ G.Adj i z ∧ G.Adj j z ∧
      G.neighborFinset z ∩ fullLineCenters G S q = {i, j} := by
  classical
  let F := fullLineCenters G S q
  obtain ⟨hDindependent, hcap, _p, _hpInj, _hp⟩ :=
    c4Free_binarySquare_pureEndpoint_fullLineCenters_structure_withReplicationCap
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hnotMem : j ∉ (secondOrderDefectGraph G).neighborFinset i := by
    simpa [SimpleGraph.mem_neighborFinset] using
      hDindependent i hi j hj hij
  have hcommon := card_common_eq_if_secondOrderDefect G hfree i j hij
  rw [if_neg hnotMem] at hcommon
  obtain ⟨z, hzCommon⟩ := Finset.card_eq_one.mp hcommon
  have hzMem : z ∈ G.neighborFinset i ∩ G.neighborFinset j := by
    rw [hzCommon]
    simp
  have hiz : G.Adj i z :=
    (G.mem_neighborFinset i z).mp (Finset.mem_inter.mp hzMem).1
  have hjz : G.Adj j z :=
    (G.mem_neighborFinset j z).mp (Finset.mem_inter.mp hzMem).2
  have hzS : z ∈ S := by
    have hiFull := (mem_fullLineCenters G S q i).mp hi
    have hiNeighbors : G.neighborFinset i ∩ S = G.neighborFinset i := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      rw [hiFull, G.card_neighborFinset_eq_degree, hreg]
    have hzN : z ∈ G.neighborFinset i :=
      (G.mem_neighborFinset i z).mpr hiz
    have : z ∈ G.neighborFinset i ∩ S := by
      rw [hiNeighbors]
      exact hzN
    exact (Finset.mem_inter.mp this).2
  have hpSub : ({i, j} : Finset V) ⊆ G.neighborFinset z ∩ F := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hwi | hwj
    · subst w
      exact Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset z _).mpr hiz.symm, hi⟩
    · subst w
      exact Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset z _).mpr hjz.symm, hj⟩
  have howners : G.neighborFinset z ∩ F = {i, j} := by
    have hpairCard : ({i, j} : Finset V).card = 2 := Finset.card_pair hij
    have hle : (G.neighborFinset z ∩ F).card ≤ ({i, j} : Finset V).card := by
      rw [hpairCard]
      exact hcap z
    exact (Finset.eq_of_subset_of_card_le hpSub hle).symm
  refine ⟨z, ⟨hzS, hiz, hjz, by simpa [F] using howners⟩, ?_⟩
  intro z' hz'
  have hz'Mem : z' ∈ G.neighborFinset i ∩ G.neighborFinset j :=
    Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset i z').mpr hz'.2.1,
       (G.mem_neighborFinset j z').mpr hz'.2.2.1⟩
  rw [hzCommon] at hz'Mem
  exact Finset.mem_singleton.mp hz'Mem

/-- The replication-two shore points are canonically parametrized by the
two-element subsets of the full-center family. -/
theorem c4Free_binarySquare_pureEndpoint_pairPoint_bijection
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
    ∃ φ : {e : Finset V //
        e ∈ (fullLineCenters G S q).powersetCard 2} → V,
      Function.Injective φ ∧
      (∀ e, φ e ∈ S ∧
        G.neighborFinset (φ e) ∩ fullLineCenters G S q = e.1) ∧
      ∀ z, z ∈ S →
        (G.neighborFinset z ∩ fullLineCenters G S q).card = 2 →
        ∃ e, φ e = z := by
  classical
  let F := fullLineCenters G S q
  let I := {e : Finset V // e ∈ F.powersetCard 2}
  have huniq : ∀ e : I, ∃! z, z ∈ S ∧ G.neighborFinset z ∩ F = e.1 := by
    intro e
    have heData := Finset.mem_powersetCard.mp e.2
    obtain ⟨i, j, hij, hePair⟩ := Finset.card_eq_two.mp heData.2
    have hi : i ∈ F := heData.1 (by rw [hePair]; simp)
    have hj : j ∈ F := heData.1 (by rw [hePair]; simp)
    obtain ⟨z, hz, hzUnique⟩ :=
      c4Free_binarySquare_pureEndpoint_existsUnique_pairPoint
        G hfree hq hqm hreg hcard S hempty hCcard hshore htri
        hi hj hij
    refine ⟨z, ⟨hz.1, by simpa [F, hePair] using hz.2.2.2⟩, ?_⟩
    intro z' hz'
    apply hzUnique z'
    have hiOwner : i ∈ G.neighborFinset z' ∩ F := by
      rw [hz'.2, hePair]
      simp
    have hjOwner : j ∈ G.neighborFinset z' ∩ F := by
      rw [hz'.2, hePair]
      simp
    exact ⟨hz'.1,
      ((G.mem_neighborFinset z' i).mp (Finset.mem_inter.mp hiOwner).1).symm,
      ((G.mem_neighborFinset z' j).mp (Finset.mem_inter.mp hjOwner).1).symm,
      by simpa [F, hePair] using hz'.2⟩
  let φ : I → V := fun e => (huniq e).choose
  have hφ : ∀ e, φ e ∈ S ∧ G.neighborFinset (φ e) ∩ F = e.1 := by
    intro e
    exact (huniq e).choose_spec.1
  have hφInj : Function.Injective φ := by
    intro e f hef
    apply Subtype.ext
    rw [← (hφ e).2, ← (hφ f).2, hef]
  refine ⟨φ, hφInj, ?_, ?_⟩
  · intro e
    simpa [F] using hφ e
  · intro z hzS hzTwo
    have heMem : G.neighborFinset z ∩ F ∈ F.powersetCard 2 :=
      Finset.mem_powersetCard.mpr ⟨Finset.inter_subset_right, by
        simpa [F] using hzTwo⟩
    let e : I := ⟨G.neighborFinset z ∩ F, heMem⟩
    have hzProp : z ∈ S ∧ G.neighborFinset z ∩ F = e.1 := ⟨hzS, rfl⟩
    have heq : z = φ e := (huniq e).unique hzProp (hφ e)
    exact ⟨e, heq.symm⟩

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_existsUnique_pairPoint
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_pairPoint_bijection
