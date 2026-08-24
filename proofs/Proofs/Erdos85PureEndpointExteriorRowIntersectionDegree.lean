import Proofs.Erdos85PureEndpointExteriorBlockDesign
import Proofs.Erdos85PureEndpointExteriorParallelClass

/-!
# Degree of an exterior row in the row-intersection graph

The exterior block design has pairwise block intersections of size at most
one.  Consequently incidences through the points of one row count the other
rows meeting it without multiplicity.  Exact point replications turn this
into a closed degree formula whose correction term is the row's number of
singleton owner blocks, equivalently its number of defect holes.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

/-- An exterior row with `k` singleton-owner points meets exactly
`m(q-3)+k` other exterior rows.  The correction `k` is also the number of
full-center defect neighbors of the row base. -/
theorem c4Free_binarySquare_pureEndpoint_exterior_rowIntersection_degree
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
    let F := fullLineCenters G S q
    let R := Fᶜ
    let B := fun w => G.neighborFinset w ∩ S
    let owner := fun y => G.neighborFinset y ∩ F
    ∀ w ∈ R,
      let P := (B w).filter fun y => (owner y).card = 1
      let meet := (R.erase w).filter fun w' =>
        ((B w) ∩ (B w')).Nonempty
      meet.card = m * (q - 3) + P.card ∧
      P.card = ((secondOrderDefectGraph G).neighborFinset w ∩ F).card := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let R := Fᶜ
  let B : V → Finset V := fun w => G.neighborFinset w ∩ S
  let owner : V → Finset V := fun y => G.neighborFinset y ∩ F
  have hdesign := c4Free_binarySquare_pureEndpoint_exterior_blockDesign
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  have hnear := c4Free_binarySquare_pureEndpoint_exterior_nearParallelDesign
    G hfree hq hqm hreg hcard S hempty hCcard hshore htri
  intro w hwR
  have hwF : w ∉ F := by
    change w ∈ Fᶜ at hwR
    exact Finset.mem_compl.mp hwR
  let P := (B w).filter fun y => (owner y).card = 1
  let meet := (R.erase w).filter fun w' => ((B w) ∩ (B w')).Nonempty
  have hBcard : (B w).card = m := by
    simpa [F, B] using hdesign.1 w hwF
  have hpair : ∀ w' ∈ R.erase w,
      ((B w) ∩ (B w')).card ≤ 1 := by
    intro w' hw'
    have hw'R := Finset.mem_of_mem_erase hw'
    have hw'F : w' ∉ F := by
      change w' ∈ Fᶜ at hw'R
      exact Finset.mem_compl.mp hw'R
    exact hdesign.2.1 w hwF w' hw'F (Ne.symm (Finset.ne_of_mem_erase hw'))
  have hright : (∑ w' ∈ R.erase w,
      (G.neighborFinset w' ∩ B w).card) = meet.card := by
    calc
      (∑ w' ∈ R.erase w, (G.neighborFinset w' ∩ B w).card) =
          ∑ w' ∈ R.erase w,
            if ((B w) ∩ (B w')).Nonempty then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro w' hw'
        have heq : G.neighborFinset w' ∩ B w = (B w) ∩ (B w') := by
          ext y
          simp [B, and_left_comm]
        rw [heq]
        by_cases hn : ((B w) ∩ (B w')).Nonempty
        · simp only [hn, if_true]
          exact Nat.le_antisymm (hpair w' hw') (Finset.card_pos.mpr hn)
        · simp only [hn, if_false]
          exact Finset.not_nonempty_iff_eq_empty.mp hn |>
            congrArg Finset.card |>.trans (Finset.card_empty)
      _ = meet.card := by simp [meet]
  have hsym := sum_neighbor_inter_card_comm G (B w) (R.erase w)
  have hleft : (∑ y ∈ B w,
      (G.neighborFinset y ∩ R.erase w).card) = meet.card := by
    rw [hsym, hright]
  have hpoint : ∀ y ∈ B w,
      (G.neighborFinset y ∩ R.erase w).card =
        (q - 3) + if (owner y).card = 1 then 1 else 0 := by
    intro y hyB
    have hyS := (Finset.mem_inter.mp hyB).2
    have hyRep := hdesign.2.2 y hyS
    have hwAdj : G.Adj y w :=
      (G.mem_neighborFinset w y).mp (Finset.mem_inter.mp hyB).1 |>.symm
    have hwExt : w ∈ G.neighborFinset y ∩ R :=
      Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset y w).mpr hwAdj, hwR⟩
    have herase : G.neighborFinset y ∩ R.erase w =
        (G.neighborFinset y ∩ R).erase w := by
      ext x
      simp [and_left_comm]
    rw [herase, Finset.card_erase_of_mem hwExt, hyRep.2]
    rcases hyRep.1 with hone | htwo
    · simp [owner, F, hone]
      omega
    · simp [owner, F, htwo]
      omega
  have hmeet : meet.card = m * (q - 3) + P.card := by
    rw [← hleft]
    calc
      (∑ y ∈ B w, (G.neighborFinset y ∩ R.erase w).card) =
          ∑ y ∈ B w,
            ((q - 3) + if (owner y).card = 1 then 1 else 0) :=
        Finset.sum_congr rfl hpoint
      _ = (B w).card * (q - 3) + P.card := by
        simp [Finset.sum_add_distrib, P]
      _ = m * (q - 3) + P.card := by rw [hBcard]
  have hP : P.card =
      ((secondOrderDefectGraph G).neighborFinset w ∩ F).card := by
    have hc := hnear w hwF
    let R₁ := S.filter fun y => (owner y).card = 1
    have hPeq : P = G.neighborFinset w ∩ R₁ := by
      ext y
      simp [P, B, R₁, owner, and_assoc]
    rw [hPeq]
    simpa [F, owner, R₁] using hc.2.1.symm
  exact ⟨hmeet, hP⟩

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_exterior_rowIntersection_degree
