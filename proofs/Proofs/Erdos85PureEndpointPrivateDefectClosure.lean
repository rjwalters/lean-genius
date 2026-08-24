import Proofs.Erdos85PureEndpointInternalDegreeProfile

/-!
# Defect closure of the pure-endpoint private points

The pure endpoint matching lands in replication-one shore points.  The
companion-defect equation then has no slack: every defect neighbor of each
matched private point remains on the occupied shore.  This couples the
partial-Baer matching to the global preconnected defect geometry.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- At the pure endpoint one can choose the private-neighbor matching so that
every matched point lies on `S` and has zero defect boundary across `S`. -/
theorem c4Free_binarySquare_pureEndpoint_privateMatching_defectClosed
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
      ∀ i, G.Adj i.1 (p i) ∧
        G.neighborFinset (p i) ∩ fullLineCenters G S q = {i.1} ∧
        p i ∈ S ∧
        ((secondOrderDefectGraph G).neighborFinset (p i) ∩
          (Sᶜ : Finset V)).card = 0 := by
  classical
  let F := fullLineCenters G S q
  let D := secondOrderDefectGraph G
  obtain ⟨p, hpInj, hp⟩ :=
    c4Free_binarySquare_pureEndpoint_fullLineCenters_privateMatching
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hd : 2 * (S.card : ℤ) - (q * q : ℕ) = 2 * (m : ℤ) := by
    have hshoreZ : 2 * (S.card : ℤ) = (q : ℤ) * q + q := by
      exact_mod_cast hshore
    have hqmZ : (q : ℤ) = 2 * (m : ℤ) := by exact_mod_cast hqm
    push_cast
    nlinarith
  have hDdeg : ∀ x, D.degree x = q - 1 := by
    intro x
    exact binarySquare_regular_secondOrderDefect_degree_eq
      G hfree (by omega) hreg hcard x
  refine ⟨p, hpInj, ?_⟩
  intro i
  have hpData := hp i
  have hpS : p i ∈ S := by
    have hiFull := (mem_fullLineCenters G S q i.1).mp i.2
    have heq : G.neighborFinset i.1 ∩ S = G.neighborFinset i.1 := by
      apply Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      rw [hiFull, G.card_neighborFinset_eq_degree, hreg]
    have hpN : p i ∈ G.neighborFinset i.1 := by
      simpa [SimpleGraph.mem_neighborFinset] using hpData.1
    have : p i ∈ G.neighborFinset i.1 ∩ S := by
      rw [heq]
      exact hpN
    exact (Finset.mem_inter.mp this).2
  have hcomp := binarySquare_trichotomy_companionDefect_apply
    G hfree (by omega) hreg hcard S (m : ℤ) hd
      (fun x => by
        rcases htri x with h0 | hm | hq'
        · exact Or.inl h0
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr hq')) (p i)
  let a := (D.neighborFinset (p i) ∩ S).card
  have hDsum :
      ∑ w ∈ D.neighborFinset (p i),
          (if w ∈ S then (1 : ℤ) else -1) =
        2 * (a : ℤ) - (q - 1 : ℕ) := by
    rw [sum_cutSign_over_finset]
    rw [D.card_neighborFinset_eq_degree, hDdeg]
  have hFsum :
      ∑ w ∈ G.neighborFinset (p i),
          (if (G.neighborFinset w ∩ S).card = q then (1 : ℤ)
           else if (G.neighborFinset w ∩ S).card = 0 then -1 else 0) = 1 := by
    have hpoint : ∀ w ∈ G.neighborFinset (p i),
        (if (G.neighborFinset w ∩ S).card = q then (1 : ℤ)
         else if (G.neighborFinset w ∩ S).card = 0 then -1 else 0) =
          if w ∈ F then 1 else 0 := by
      intro w _hw
      by_cases hwF : w ∈ F
      · have hwq := (mem_fullLineCenters G S q w).mp hwF
        simp [hwF, hwq]
      · have hwNotQ : (G.neighborFinset w ∩ S).card ≠ q := fun h =>
          hwF ((mem_fullLineCenters G S q w).mpr h)
        have hwNotZero : (G.neighborFinset w ∩ S).card ≠ 0 := by
          intro hw0
          have hwEmpty : w ∈ emptyLineCenters G S :=
            (mem_emptyLineCenters G S w).mpr hw0
          rw [hempty] at hwEmpty
          simp at hwEmpty
        simp [hwF, hwNotQ, hwNotZero]
    rw [Finset.sum_congr rfl hpoint, Finset.sum_boole]
    have hrep : (G.neighborFinset (p i) ∩ F).card = 1 := by
      rw [show G.neighborFinset (p i) ∩ F = {i.1} by simpa [F] using hpData.2]
      simp
    change (((G.neighborFinset (p i)).filter fun w => w ∈ F).card : ℤ) = 1
    exact_mod_cast hrep
  rw [hDsum, hFsum, hqm] at hcomp
  simp [hpS] at hcomp
  have hmpos : 0 < m := by omega
  have hmsub : (((2 * m) - 1 : ℕ) : ℤ) = 2 * (m : ℤ) - 1 := by omega
  rw [hmsub] at hcomp
  have ha : a = q - 1 := by
    have haZ : (a : ℤ) = 2 * (m : ℤ) - 1 := by linarith
    have haNat : a = 2 * m - 1 := by
      exact_mod_cast (show (a : ℤ) = ((2 * m - 1 : ℕ) : ℤ) by
        rw [hmsub]
        exact haZ)
    omega
  have hcross := neighbor_inter_complement_card D S (p i)
  rw [hDdeg (p i), show
      (D.neighborFinset (p i) ∩ S).card = q - 1 by exact ha] at hcross
  refine ⟨hpData.1, hpData.2, hpS, ?_⟩
  change (D.neighborFinset (p i) ∩ (Finset.univ \ S)).card = 0
  simpa using hcross

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_privateMatching_defectClosed
