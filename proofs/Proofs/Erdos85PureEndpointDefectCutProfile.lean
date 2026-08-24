import Proofs.Erdos85PureEndpointInternalDegreeProfile

/-!
# Exact pointwise defect-cut profile at the pure endpoint

The exact replication census closes the companion-defect equation at every
vertex.  Private shore points have no defect edge across the shore, pair
points have `m` such edges, and every off-shore point has exactly `m` defect
neighbors on the shore.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Pointwise endpoint defect-cut degrees, split by full-center replication. -/
theorem c4Free_binarySquare_pureEndpoint_defectCutDegree_profile
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
    ∀ x,
      (x ∈ S →
        (G.neighborFinset x ∩ fullLineCenters G S q).card = 1 →
        ((secondOrderDefectGraph G).neighborFinset x ∩
          (Sᶜ : Finset V)).card = 0) ∧
      (x ∈ S →
        (G.neighborFinset x ∩ fullLineCenters G S q).card = 2 →
        ((secondOrderDefectGraph G).neighborFinset x ∩
          (Sᶜ : Finset V)).card = m) ∧
      (x ∉ S →
        ((secondOrderDefectGraph G).neighborFinset x ∩ S).card = m) := by
  classical
  let F := fullLineCenters G S q
  let D := secondOrderDefectGraph G
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
  have hrepSupport :=
    (c4Free_binarySquare_pureEndpoint_fullLineCenters_exactReplicationProfile
      G hfree hq hqm hreg hcard S hempty hCcard hshore htri).1
  intro x
  let a := (D.neighborFinset x ∩ S).card
  let r := (G.neighborFinset x ∩ F).card
  have hcomp := binarySquare_trichotomy_companionDefect_apply
    G hfree (by omega) hreg hcard S (m : ℤ) hd
      (fun v => by
        rcases htri v with h0 | hm | hq'
        · exact Or.inl h0
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr hq')) x
  have hDsum :
      ∑ w ∈ D.neighborFinset x,
          (if w ∈ S then (1 : ℤ) else -1) =
        2 * (a : ℤ) - (q - 1 : ℕ) := by
    rw [sum_cutSign_over_finset]
    rw [D.card_neighborFinset_eq_degree, hDdeg]
  have hFsum :
      ∑ w ∈ G.neighborFinset x,
          (if (G.neighborFinset w ∩ S).card = q then (1 : ℤ)
           else if (G.neighborFinset w ∩ S).card = 0 then -1 else 0) =
        (r : ℤ) := by
    have hpoint : ∀ w ∈ G.neighborFinset x,
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
    change (((G.neighborFinset x).filter fun w => w ∈ F).card : ℤ) = r
    congr 1
  rw [hDsum, hFsum, hqm] at hcomp
  have hmpos : 0 < m := by omega
  have hmsub : (((2 * m) - 1 : ℕ) : ℤ) = 2 * (m : ℤ) - 1 := by omega
  rw [hmsub] at hcomp
  have hcross :
      (D.neighborFinset x ∩ S).card +
          (D.neighborFinset x ∩ (Sᶜ : Finset V)).card = 2 * m - 1 := by
    have h := neighbor_inter_complement_card D S x
    rw [hDdeg x, hqm] at h
    change (D.neighborFinset x ∩ (Sᶜ : Finset V)).card =
      2 * m - 1 - (D.neighborFinset x ∩ S).card at h
    have haLe : (D.neighborFinset x ∩ S).card ≤ 2 * m - 1 := by
      calc
        (D.neighborFinset x ∩ S).card ≤ (D.neighborFinset x).card :=
          Finset.card_le_card Finset.inter_subset_left
        _ = 2 * m - 1 := by
          rw [D.card_neighborFinset_eq_degree, hDdeg, hqm]
    omega
  constructor
  · intro hxS hrOne
    have hr : r = 1 := by simpa [r, F] using hrOne
    simp [hxS, hr] at hcomp
    have ha : a = 2 * m - 1 := by
      have haZ : (a : ℤ) = 2 * (m : ℤ) - 1 := by linarith
      exact_mod_cast (show (a : ℤ) = ((2 * m - 1 : ℕ) : ℤ) by
        rw [hmsub]; exact haZ)
    change (D.neighborFinset x ∩ (Sᶜ : Finset V)).card = 0
    change a + (D.neighborFinset x ∩ (Sᶜ : Finset V)).card =
      2 * m - 1 at hcross
    omega
  constructor
  · intro hxS hrTwo
    have hr : r = 2 := by simpa [r, F] using hrTwo
    simp [hxS, hr] at hcomp
    have ha : a = m - 1 := by
      have haZ : (a : ℤ) = (m : ℤ) - 1 := by linarith
      have hm1 : (((m - 1 : ℕ) : ℤ)) = (m : ℤ) - 1 := by omega
      exact_mod_cast (show (a : ℤ) = ((m - 1 : ℕ) : ℤ) by
        rw [hm1]; exact haZ)
    change (D.neighborFinset x ∩ (Sᶜ : Finset V)).card = m
    change a + (D.neighborFinset x ∩ (Sᶜ : Finset V)).card =
      2 * m - 1 at hcross
    omega
  · intro hxOff
    have hrZero : r = 0 := by
      have hxRep : (G.neighborFinset x ∩ fullLineCenters G S q).card = 0 := by
        by_contra hne
        have hpos : 0 <
            (G.neighborFinset x ∩ fullLineCenters G S q).card :=
          Nat.pos_of_ne_zero hne
        have hxS : x ∈ S := (hrepSupport x).2 (by
          have hcap :=
            (c4Free_binarySquare_pureEndpoint_fullLineCenters_exactReplicationProfile
              G hfree hq hqm hreg hcard S hempty hCcard hshore htri).2.2.2.2.1 x
          omega)
        exact hxOff hxS
      simpa [r, F] using hxRep
    simp [hxOff, hrZero] at hcomp
    change a = m
    have haZ : (a : ℤ) = (m : ℤ) := by linarith
    exact_mod_cast haZ

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_defectCutDegree_profile
