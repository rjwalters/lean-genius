import Proofs.Erdos85PureEndpointExteriorEvenConfigurationOddExcessComplementDegree

/-! # Local multiplicities in an `m+3` exterior even configuration -/

open Finset BigOperators

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000

/-- A finite family of positive odd naturals summing to the size of its
indexing set is identically one. -/
theorem odd_sum_eq_card_forces_one
    {α : Type*} [DecidableEq α] (K : Finset α) (f : α → ℕ)
    (hodd : ∀ x ∈ K, Odd (f x)) (hsum : ∑ x ∈ K, f x = K.card) :
    ∀ x ∈ K, f x = 1 := by
  classical
  have hone : ∀ x ∈ K, 1 ≤ f x := by
    intro x hx
    rcases hodd x hx with ⟨a, ha⟩
    omega
  have hall := (Finset.sum_eq_sum_iff_of_le hone).mp
    (show (∑ x ∈ K, 1) = ∑ x ∈ K, f x by simpa [hsum])
  intro x hx
  exact (hall x hx).symm

/-- A finite family of positive odd naturals with total excess two has a
unique entry three, all other entries being one. -/
theorem odd_sum_eq_card_add_two_classify
    {α : Type*} [DecidableEq α] (K : Finset α) (f : α → ℕ)
    (hodd : ∀ x ∈ K, Odd (f x))
    (hsum : ∑ x ∈ K, f x = K.card + 2) :
    ∃! x, x ∈ K ∧ f x = 3 ∧ ∀ y ∈ K, y ≠ x → f y = 1 := by
  classical
  induction K using Finset.induction_on with
  | empty => simp at hsum
  | @insert a K ha ih =>
      have haodd : Odd (f a) := hodd a (mem_insert_self a K)
      have hKodd : ∀ x ∈ K, Odd (f x) := by
        intro x hx
        exact hodd x (mem_insert_of_mem hx)
      have hKlower : K.card ≤ ∑ x ∈ K, f x := by
        have hle : (∑ x ∈ K, 1) ≤ ∑ x ∈ K, f x := by
          apply Finset.sum_le_sum
          intro x hx
          rcases hKodd x hx with ⟨c, hc⟩
          omega
        simpa using hle
      have hsplit : f a + ∑ x ∈ K, f x = K.card + 3 := by
        simpa [ha] using hsum
      rcases haodd with ⟨b, hb⟩
      have hfa : f a = 1 ∨ f a = 3 := by omega
      rcases hfa with hfa | hfa
      · have hKsum : ∑ x ∈ K, f x = K.card + 2 := by omega
        obtain ⟨x, hx, huniq⟩ := ih hKodd hKsum
        refine ⟨x, ⟨mem_insert_of_mem hx.1, hx.2.1, ?_⟩, ?_⟩
        · intro y hy hyx
          rcases mem_insert.mp hy with rfl | hyK
          · exact hfa
          · exact hx.2.2 y hyK hyx
        · intro y hy
          have hyK : y ∈ K := by
            rcases mem_insert.mp hy.1 with rfl | hyK
            · omega
            · exact hyK
          exact huniq y ⟨hyK, hy.2.1, fun z hz hzy =>
            hy.2.2 z (mem_insert_of_mem hz) hzy⟩
      · have hKsum : ∑ x ∈ K, f x = K.card := by omega
        have hKone := odd_sum_eq_card_forces_one K f hKodd hKsum
        refine ⟨a, ⟨mem_insert_self a K, hfa, ?_⟩, ?_⟩
        · intro y hy hya
          exact hKone y ((mem_insert.mp hy).resolve_left hya)
        · intro y hy
          rcases mem_insert.mp hy.1 with rfl | hyK
          · rfl
          · have := hKone y hyK
            omega

/-- Double counting a fixed selected block: its internal meeting degree is
the sum, over its points, of the numbers of other selected blocks through
those points. -/
theorem linear_configuration_internal_meeting_eq_sum_local_partner_degree
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (B : α → Finset β) (T : Finset α) (p : α) (hp : p ∈ T)
    (hlinear : ∀ q ∈ T.erase p, ((B p) ∩ (B q)).card ≤ 1) :
    ((T.erase p).filter fun q => ((B p) ∩ (B q)).Nonempty).card =
      ∑ y ∈ B p, ((T.erase p).filter fun q => y ∈ B q).card := by
  classical
  calc
    ((T.erase p).filter fun q => ((B p) ∩ (B q)).Nonempty).card =
        ∑ q ∈ T.erase p, ((B p) ∩ (B q)).card := by
      rw [card_filter]
      apply sum_congr rfl
      intro q hq
      by_cases hn : ((B p) ∩ (B q)).Nonempty
      · simp only [hn, if_true]
        exact Nat.le_antisymm (card_pos.mpr hn) (hlinear q hq)
      · simp only [hn, if_false]
        exact (card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hn)).symm
    _ = ∑ q ∈ T.erase p, ∑ y ∈ B p, if y ∈ B q then 1 else 0 := by
      apply sum_congr rfl
      intro q _
      rw [← card_filter]
      congr 1
    _ = ∑ y ∈ B p, ∑ q ∈ T.erase p, if y ∈ B q then 1 else 0 := by
      rw [sum_comm]
    _ = ∑ y ∈ B p, ((T.erase p).filter fun q => y ∈ B q).card := by
      apply sum_congr rfl
      intro y _
      rw [card_filter]

/-- Local classification at the first larger odd stratum.  Along any fixed
selected row, either two rows miss it and every point has configuration
multiplicity two, or no row misses it and a unique point has multiplicity
four while every other point has multiplicity two. -/
theorem linear_even_configuration_eq_add_three_localMultiplicity
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (B : α → Finset β) (T : Finset α) (p : α) (m : ℕ)
    (hp : p ∈ T) (hcard : (B p).card = m)
    (hTcard : T.card = m + 3)
    (heven : ∀ y : β, Even ((T.filter fun q => y ∈ B q).card))
    (hlinear : ∀ q ∈ T.erase p, ((B p) ∩ (B q)).card ≤ 1)
    (hmissing : ((T.erase p).filter fun q =>
      ¬ ((B p) ∩ (B q)).Nonempty).card = 0 ∨
      ((T.erase p).filter fun q =>
      ¬ ((B p) ∩ (B q)).Nonempty).card = 2) :
    (((T.erase p).filter fun q =>
        ¬ ((B p) ∩ (B q)).Nonempty).card = 2 ∧
      ∀ y ∈ B p, (T.filter fun q => y ∈ B q).card = 2) ∨
    (((T.erase p).filter fun q =>
        ¬ ((B p) ∩ (B q)).Nonempty).card = 0 ∧
      ∃! y, y ∈ B p ∧ (T.filter fun q => y ∈ B q).card = 4 ∧
        ∀ z ∈ B p, z ≠ y →
          (T.filter fun q => z ∈ B q).card = 2) := by
  classical
  let M := (T.erase p).filter fun q => ((B p) ∩ (B q)).Nonempty
  let N := (T.erase p).filter fun q => ¬ ((B p) ∩ (B q)).Nonempty
  let d : β → ℕ := fun y => ((T.erase p).filter fun q => y ∈ B q).card
  have hpart : T.erase p = M ∪ N := by
    ext q
    simp only [M, N, mem_erase, mem_union, mem_filter]
    tauto
  have hdis : Disjoint M N := by
    rw [disjoint_left]
    intro q hqM hqN
    exact (mem_filter.mp hqN).2 (mem_filter.mp hqM).2
  have hMN : M.card + N.card = m + 2 := by
    have herase : (T.erase p).card = T.card - 1 := card_erase_of_mem hp
    rw [hpart, card_union_of_disjoint hdis] at herase
    omega

/-
/-- Endpoint exterior specialization of the local `m+3` multiplicity
classification. -/
theorem c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_three_localMultiplicity
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
      T.card = m + 3 →
      ∀ w ∈ T,
      ((((T.erase w).filter fun u =>
          ¬ (row w ∩ row u).Nonempty).card = 2 ∧
        ∀ y ∈ row w, (T.filter fun u => y ∈ row u).card = 2) ∨
       (((T.erase w).filter fun u =>
          ¬ (row w ∩ row u).Nonempty).card = 0 ∧
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
      rw [hz]
      exact ⟨0, rfl⟩
  have hlinear : ∀ u ∈ T.erase w, ((row w) ∩ (row u)).card ≤ 1 := by
    intro u hu
    exact hdesign.2.1 w.1 (by simpa [F] using (mem_compl.mp w.2))
      u.1 (by simpa [F] using (mem_compl.mp u.2))
      (fun h => (ne_of_mem_erase hu) (Subtype.ext h).symm)
  have hmissing :=
    c4Free_binarySquare_pureEndpoint_evenConfiguration_eq_add_three_complementDegree
      G hfree hq hqm hmEven hreg hcardV S hempty hCcard hshore htri
      T heven hTcard w hw
  exact linear_even_configuration_eq_add_three_localMultiplicity
    row T w m hw hrowCard hTcard hevenV hlinear (by
      simpa [row, inter_assoc] using hmissing)
-/
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
  rcases hmissing with hN | hN
  · right
    change N.card = 0 at hN
    refine ⟨hN, ?_⟩
    have hsumExcess : ∑ y ∈ B p, d y = (B p).card + 2 := by
      rw [hsum, hcard]
      omega
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
  · left
    change N.card = 2 at hN
    refine ⟨hN, ?_⟩
    have hsumMin : ∑ y ∈ B p, d y = (B p).card := by
      rw [hsum, hcard]
      omega
    have hdOne := odd_sum_eq_card_forces_one (B p) d hdodd hsumMin
    intro y hy
    have hs := hdSucc y hy
    have hdy := hdOne y hy
    omega

end

end Erdos85

#print axioms Erdos85.odd_sum_eq_card_forces_one
#print axioms Erdos85.odd_sum_eq_card_add_two_classify
#print axioms Erdos85.linear_configuration_internal_meeting_eq_sum_local_partner_degree
#print axioms Erdos85.linear_even_configuration_eq_add_three_localMultiplicity
