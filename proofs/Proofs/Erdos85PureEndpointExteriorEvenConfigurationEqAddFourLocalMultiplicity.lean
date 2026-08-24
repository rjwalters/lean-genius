import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEqAddThreeLocalMultiplicity
import Proofs.Erdos85PureEndpointExteriorEvenConfigurationEvenExcessComplementDegree

/-!
# The `m+4` exterior-circuit stratum

The even-excess complement-degree law immediately leaves only one or three
nonmeeting partners at every selected row.  The accompanying local
point-multiplicity classification is supplied below once the generic
row-partner count is available.
-/

open Finset SimpleGraph BigOperators

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000

/-- The local multiplicity classification depends only on whether the fixed
row meets `m` or `m+2` other rows, not on the total configuration size. -/
theorem linear_even_configuration_localMultiplicity_of_internalDegree_eq_or_eq_add_two
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (B : α → Finset β) (T : Finset α) (p : α) (m : ℕ)
    (hp : p ∈ T) (hcard : (B p).card = m)
    (heven : ∀ y : β, Even ((T.filter fun q => y ∈ B q).card))
    (hlinear : ∀ q ∈ T.erase p, ((B p) ∩ (B q)).card ≤ 1)
    (hdegree :
      ((T.erase p).filter fun q => ((B p) ∩ (B q)).Nonempty).card = m ∨
      ((T.erase p).filter fun q => ((B p) ∩ (B q)).Nonempty).card = m + 2) :
    (((T.erase p).filter fun q => ((B p) ∩ (B q)).Nonempty).card = m ∧
      ∀ y ∈ B p, (T.filter fun q => y ∈ B q).card = 2) ∨
    (((T.erase p).filter fun q => ((B p) ∩ (B q)).Nonempty).card = m + 2 ∧
      ∃! y, y ∈ B p ∧ (T.filter fun q => y ∈ B q).card = 4 ∧
        ∀ z ∈ B p, z ≠ y →
          (T.filter fun q => z ∈ B q).card = 2) := by
  classical
  let M := (T.erase p).filter fun q => ((B p) ∩ (B q)).Nonempty
  let d : β → ℕ := fun y => ((T.erase p).filter fun q => y ∈ B q).card
  have hsum : ∑ y ∈ B p, d y = M.card := by
    symm
    simpa [M, d] using
      linear_configuration_internal_meeting_eq_sum_local_partner_degree
        B T p hp hlinear
  have hdSucc : ∀ y ∈ B p,
      (T.filter fun q => y ∈ B q).card = d y + 1 := by
    intro y hy
    have hpfilter : p ∈ T.filter (fun q => y ∈ B q) :=
      mem_filter.mpr ⟨hp, hy⟩
    have herase := card_erase_of_mem hpfilter
    have heraseFilter :
        (T.filter fun q => y ∈ B q).erase p =
          (T.erase p).filter fun q => y ∈ B q := by
      ext q
      simp [and_assoc]
    rw [heraseFilter] at herase
    dsimp [d]
    have hpos : 0 < (T.filter fun q => y ∈ B q).card :=
      card_pos.mpr ⟨p, hpfilter⟩
    omega
  have hdodd : ∀ y ∈ B p, Odd (d y) := by
    intro y hy
    rcases heven y with ⟨a, ha⟩
    refine ⟨a - 1, ?_⟩
    have hs := hdSucc y hy
    omega
  rcases hdegree with hM | hM
  · left
    change M.card = m at hM
    refine ⟨hM, ?_⟩
    have hsumMin : ∑ y ∈ B p, d y = (B p).card := by
      rw [hsum, hcard, hM]
    have hdOne := odd_sum_eq_card_forces_one (B p) d hdodd hsumMin
    intro y hy
    have hs := hdSucc y hy
    have hdy := hdOne y hy
    omega
  · right
    change M.card = m + 2 at hM
    refine ⟨hM, ?_⟩
    have hsumExcess : ∑ y ∈ B p, d y = (B p).card + 2 := by
      rw [hsum, hcard, hM]
    obtain ⟨y, hy, huniq⟩ :=
      odd_sum_eq_card_add_two_classify (B p) d hdodd hsumExcess
    refine ⟨y, ⟨hy.1, ?_, ?_⟩, ?_⟩
    · have hs := hdSucc y hy.1
      have hdy : d y = 3 := hy.2.1
      omega
    · intro z hz hzy
      have hs := hdSucc z hz
      have hdz : d z = 1 := hy.2.2 z hz hzy
      omega
    · intro z hz
      exact huniq z ⟨hz.1, by
        have hs := hdSucc z hz.1
        omega, by
          intro x hx hxz
          have hs := hdSucc x hx
          have htotal := hz.2.2 x hx hxz
          omega⟩

/-- Every row of an endpoint even configuration of size `m+4` has exactly
one or exactly three nonmeeting partners. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_four_complementDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m) (hmEven : Even m)
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
    let W := {w : V // w ∈ Fᶜ}
    let P := {y : V // y ∈ S}
    let row := fun w : W => G.neighborFinset w.1 ∩ S
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      T.card = m + 4 →
      ∀ w ∈ T,
        ((T.erase w).filter fun u =>
          ¬(row w ∩ row u).Nonempty).card = 1 ∨
        ((T.erase w).filter fun u =>
          ¬(row w ∩ row u).Nonempty).card = 3 := by
  classical
  dsimp only
  intro T heven hTcard w hwT
  let missing := (T.erase w).filter fun u =>
    ¬((G.neighborFinset w.1 ∩ S) ∩
      (G.neighborFinset u.1 ∩ S)).Nonempty
  change missing.card = 1 ∨ missing.card = 3
  have hdegree :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_evenExcess_missingDegree
      (s := 2) G hfree hq hqm hmEven (by omega) hreg hcard S hempty
      hCcard hshore htri T heven (by omega) w hwT
  change Odd missing.card ∧ missing.card ≤ 2 * 2 - 1 at hdegree
  rcases hdegree.1 with ⟨k, hk⟩
  rcases hdegree.2 with hle
  omega

/-- In the `m+4` stratum, a row with three nonpartners has only
replication-two points; a row with one nonpartner has one unique
replication-four point and all its other points have replication two. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_four_localMultiplicity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q m : ℕ}
    (hq : 8 ≤ q) (hqm : q = 2 * m) (hmEven : Even m)
    (hreg : ∀ v, G.degree v = q)
    (hcardV : Fintype.card V = q * q)
    (S : Finset V)
    (hempty : emptyLineCenters G S = ∅)
    (hCcard : (fullLineCenters G S q).card = q)
    (hshore : 2 * S.card = q * q + q)
    (htri : ∀ v,
      (G.neighborFinset v ∩ S).card = 0 ∨
      (G.neighborFinset v ∩ S).card = m ∨
      (G.neighborFinset v ∩ S).card = q) :
    let F := fullLineCenters G S q
    let W := {w : V // w ∈ Fᶜ}
    let P := {y : V // y ∈ S}
    let row := fun w : W => G.neighborFinset w.1 ∩ S
    ∀ T : Finset W,
      (∀ y : P, Even ((T.filter fun w => G.Adj w.1 y.1).card)) →
      T.card = m + 4 →
      ∀ w ∈ T,
      ((((T.erase w).filter fun u =>
          ¬(row w ∩ row u).Nonempty).card = 3 ∧
        ∀ y ∈ row w, (T.filter fun u => y ∈ row u).card = 2) ∨
       (((T.erase w).filter fun u =>
          ¬(row w ∩ row u).Nonempty).card = 1 ∧
        ∃! y, y ∈ row w ∧ (T.filter fun u => y ∈ row u).card = 4 ∧
          ∀ z ∈ row w, z ≠ y →
            (T.filter fun u => z ∈ row u).card = 2)) := by
  classical
  dsimp only
  let F := fullLineCenters G S q
  let W := {w : V // w ∈ Fᶜ}
  let P := {y : V // y ∈ S}
  let row : W → Finset V := fun w => G.neighborFinset w.1 ∩ S
  intro T heven hTcard w hw
  have hdesign := c4Free_binarySquare_pureEndpoint_exterior_blockDesign
    G hfree hq hqm hreg hcardV S hempty hCcard hshore htri
  have hrowCard : (row w).card = m :=
    hdesign.1 w.1 (by simpa [F] using (mem_compl.mp w.2))
  have hevenV : ∀ y : V, Even ((T.filter fun u => y ∈ row u).card) := by
    intro y
    by_cases hy : y ∈ S
    · let yy : P := ⟨y, hy⟩
      simpa [row, hy] using heven yy
    · have hz : T.filter (fun u => y ∈ row u) = ∅ := by
        ext u
        simp [row, hy]
      simp [hz]
  have hlinear : ∀ u ∈ T.erase w, ((row w) ∩ (row u)).card ≤ 1 := by
    intro u hu
    exact hdesign.2.1 w.1 (by simpa [F] using (mem_compl.mp w.2))
      u.1 (by simpa [F] using (mem_compl.mp u.2))
      (fun h => (ne_of_mem_erase hu) (Subtype.ext h).symm)
  let M := (T.erase w).filter fun u => (row w ∩ row u).Nonempty
  let N := (T.erase w).filter fun u => ¬(row w ∩ row u).Nonempty
  have hmissing :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_four_complementDegree
      G hfree hq hqm hmEven hreg hcardV S hempty hCcard hshore htri
      T heven hTcard w hw
  have hpart : M.card + N.card = m + 3 := by
    have hsplit := card_filter_add_card_filter_not
      (s := T.erase w) (fun u => (row w ∩ row u).Nonempty)
    change M.card + N.card = m + 3
    rw [hsplit, card_erase_of_mem hw, hTcard]
    omega
  have hdegree : M.card = m ∨ M.card = m + 2 := by
    change N.card = 1 ∨ N.card = 3 at hmissing
    rcases hmissing with hN | hN
    · right; omega
    · left; omega
  have hlocal :=
    linear_even_configuration_localMultiplicity_of_internalDegree_eq_or_eq_add_two
      row T w m hw hrowCard hevenV hlinear (by simpa [M] using hdegree)
  rcases hlocal with hM | hM
  · left
    refine ⟨?_, hM.2⟩
    change N.card = 3
    have hMcard : M.card = m := by simpa [M] using hM.1
    omega
  · right
    refine ⟨?_, hM.2⟩
    change N.card = 1
    have hMcard : M.card = m + 2 := by simpa [M] using hM.1
    omega

end

end Erdos85

#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_four_complementDegree
#print axioms
  Erdos85.linear_even_configuration_localMultiplicity_of_internalDegree_eq_or_eq_add_two
#print axioms
  Erdos85.c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_four_localMultiplicity
