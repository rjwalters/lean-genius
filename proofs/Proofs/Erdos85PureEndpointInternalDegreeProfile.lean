import Proofs.Erdos85PureEndpointFinalLayerPrivateMatching

/-!
# Internal degree profile at the pure exceptional endpoint

The companion-defect equation sees more than the four-class incidence
census.  At a full exceptional center it determines the possible number of
adjacent full centers from which shore the center itself occupies.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Sum of a cut sign over an arbitrary finite set. -/
theorem sum_cutSign_over_finset
    {V : Type*} [Fintype V] [DecidableEq V]
    (N S : Finset V) :
    ∑ x ∈ N, (if x ∈ S then (1 : ℤ) else -1) =
      2 * ((N ∩ S).card : ℤ) - N.card := by
  classical
  rw [show (∑ x ∈ N, (if x ∈ S then (1 : ℤ) else -1)) =
      ∑ x ∈ N, (2 * (if x ∈ S then (1 : ℤ) else 0) - 1) by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : x ∈ S <;> simp [hx]]
  have hind :
      (∑ x ∈ N, if x ∈ S then (1 : ℤ) else 0) =
        ((N ∩ S).card : ℤ) := by
    rw [Finset.sum_boole]
    congr 1
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hind]
  simp

/-- At the pure endpoint, a full center in the shore has one or two full
neighbors, while a full center outside the shore has zero or one. -/
theorem c4Free_binarySquare_pureEndpoint_fullCenter_internalDegree_profile
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
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q)
    (v : V) (_hvFull : v ∈ fullLineCenters G S q) :
    (v ∈ S →
        (G.neighborFinset v ∩ fullLineCenters G S q).card = 1 ∨
        (G.neighborFinset v ∩ fullLineCenters G S q).card = 2) ∧
      (v ∉ S →
        (G.neighborFinset v ∩ fullLineCenters G S q).card = 0 ∨
        (G.neighborFinset v ∩ fullLineCenters G S q).card = 1) := by
  let D := secondOrderDefectGraph G
  let F := fullLineCenters G S q
  let r := (G.neighborFinset v ∩ F).card
  let a := (D.neighborFinset v ∩ S).card
  have hd : 2 * (S.card : ℤ) - (q * q : ℕ) = 2 * (m : ℤ) := by
    have hshoreZ : 2 * (S.card : ℤ) = (q : ℤ) * q + q := by
      exact_mod_cast hshore
    have hqmZ : (q : ℤ) = 2 * (m : ℤ) := by exact_mod_cast hqm
    push_cast
    nlinarith
  have hcomp := binarySquare_trichotomy_companionDefect_apply
    G hfree (by omega) hreg hcard S (m : ℤ) hd
      (fun x => by
        rcases htri x with h0 | hm | hq'
        · exact Or.inl h0
        · exact Or.inr (Or.inl (by omega))
        · exact Or.inr (Or.inr hq')) v
  have hDcard : (D.neighborFinset v).card = q - 1 := by
    rw [D.card_neighborFinset_eq_degree,
      binarySquare_regular_secondOrderDefect_degree_eq
        G hfree (by omega) hreg hcard]
  have hDsum :
      ∑ w ∈ D.neighborFinset v,
          (if w ∈ S then (1 : ℤ) else -1) =
        2 * (a : ℤ) - (q - 1 : ℕ) := by
    rw [sum_cutSign_over_finset]
    rw [hDcard]
  have hFsum :
      ∑ w ∈ G.neighborFinset v,
          (if (G.neighborFinset w ∩ S).card = q then (1 : ℤ)
           else if (G.neighborFinset w ∩ S).card = 0 then -1 else 0) =
        (r : ℤ) := by
    have hpoint : ∀ w ∈ G.neighborFinset v,
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
    rw [Finset.sum_congr rfl hpoint]
    rw [Finset.sum_boole]
    change (((G.neighborFinset v).filter fun w => w ∈ F).card : ℤ) = r
    congr 1
  rw [hDsum, hFsum, hqm] at hcomp
  have haBounds : a ≤ q - 1 := by
    dsimp only [a]
    rw [← hDcard]
    exact Finset.card_le_card Finset.inter_subset_left
  have hmpos : 0 < m := by omega
  have hmsub : (((2 * m) - 1 : ℕ) : ℤ) = 2 * (m : ℤ) - 1 := by
    omega
  rw [hmsub] at hcomp
  have haBounds' : a ≤ 2 * m - 1 := by omega
  have haBoundsZ : (a : ℤ) ≤ 2 * (m : ℤ) - 1 := by
    have h : (a : ℤ) ≤ (((2 * m) - 1 : ℕ) : ℤ) := by
      exact_mod_cast haBounds'
    omega
  constructor
  · intro hvS
    simp [hvS] at hcomp
    have hcompLin : (a : ℤ) + (m : ℤ) * r = 3 * (m : ℤ) - 1 := by
      nlinarith [hcomp]
    change r = 1 ∨ r = 2
    have hrpos : 0 < r := by
      by_contra hr
      have hr0 : r = 0 := by omega
      rw [hr0] at hcomp
      norm_num at hcomp
      omega
    have hrle : r ≤ 2 := by
      by_contra hr
      have hr3 : 3 ≤ r := by omega
      have hmr : m * 3 ≤ m * r := Nat.mul_le_mul_left m hr3
      have hmrZ : (m : ℤ) * 3 ≤ (m : ℤ) * r := by exact_mod_cast hmr
      omega
    omega
  · intro hvNotS
    simp [hvNotS] at hcomp
    have hcompLin : (a : ℤ) + (m : ℤ) * r = m := by
      nlinarith [hcomp]
    change r = 0 ∨ r = 1
    have hrle : r ≤ 1 := by
      by_contra hr
      have hr2 : 2 ≤ r := by omega
      have hmr : m * 2 ≤ m * r := Nat.mul_le_mul_left m hr2
      have hmrZ : (m : ℤ) * 2 ≤ (m : ℤ) * r := by exact_mod_cast hmr
      omega
    omega

end

end Erdos85

#print axioms Erdos85.sum_cutSign_over_finset
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_fullCenter_internalDegree_profile
