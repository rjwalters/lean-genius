import Proofs.Erdos85OddKeyEulerian

/-! # The odd exchanged-key support as a graph on labels -/

namespace Erdos85

noncomputable section

def oddExchangedKeyLabelGraph
    {L : Type*} [Fintype L] [DecidableEq L] [LinearOrder L]
    (multiplicity : L × L → ℕ) : SimpleGraph L where
  Adj a b := a ≠ b ∧
    Odd (multiplicity (min a b, max a b))
  symm := ⟨by
    intro a b h
    exact ⟨h.1.symm, by simpa [min_comm, max_comm] using h.2⟩⟩
  loopless := ⟨by simp⟩

noncomputable instance oddExchangedKeyLabelGraph_neighborFintype
    {L : Type*} [Fintype L] [DecidableEq L] [LinearOrder L]
    (multiplicity : L × L → ℕ) (a : L) :
    Fintype ((oddExchangedKeyLabelGraph multiplicity).neighborSet a) :=
  Fintype.ofFinite _

theorem canonicalKey_mem_oddIncidentSupport_iff
    {L : Type*} [Fintype L] [DecidableEq L] [LinearOrder L]
    (multiplicity : L × L → ℕ) (a b : L) :
    (min a b, max a b) ∈ oddExchangedKeyIncidentSupport multiplicity a ↔
      a ≠ b ∧ Odd (multiplicity (min a b, max a b)) := by
  by_cases hab : a = b
  · subst b
    simp [oddExchangedKeyIncidentSupport, oddExchangedKeySupport,
      exchangedMissPairKeys]
  · have hlt : min a b < max a b := min_lt_max.mpr hab
    have hinc : unorderedKeyIncidence (min a b, max a b) a = 1 := by
      unfold unorderedKeyIncidence
      split
      · rfl
      · rename_i h
        exfalso
        apply h
        rcases le_total a b with hle | hle
        · exact Or.inl (min_eq_left hle).symm
        · exact Or.inr (max_eq_left hle).symm
    simp [oddExchangedKeyIncidentSupport, oddExchangedKeySupport,
      exchangedMissPairKeys, hlt, hinc, hab]

/-- The degree of a label in the label-support graph is exactly the number
of odd genuine exchanged keys incident to that label. -/
theorem degree_oddExchangedKeyLabelGraph_eq_incidentSupport_card
    {L : Type*} [Fintype L] [DecidableEq L] [LinearOrder L]
    (multiplicity : L × L → ℕ) (a : L) :
    (oddExchangedKeyLabelGraph multiplicity).degree a =
      (oddExchangedKeyIncidentSupport multiplicity a).card := by
  classical
  let G := oddExchangedKeyLabelGraph multiplicity
  let T := oddExchangedKeyIncidentSupport multiplicity a
  change (G.neighborFinset a).card = T.card
  apply Finset.card_bij (fun b _ => (min a b, max a b))
  · intro b hb
    have hadj : G.Adj a b := by
      simpa [SimpleGraph.mem_neighborFinset] using hb
    exact (canonicalKey_mem_oddIncidentSupport_iff multiplicity a b).2 hadj
  · intro b hb c hc heq
    have hbne : a ≠ b := ((canonicalKey_mem_oddIncidentSupport_iff
      multiplicity a b).1 ((by
        have hadj : G.Adj a b := by
          simpa [SimpleGraph.mem_neighborFinset] using hb
        exact (canonicalKey_mem_oddIncidentSupport_iff multiplicity a b).2 hadj))).1
    have hcne : a ≠ c := ((canonicalKey_mem_oddIncidentSupport_iff
      multiplicity a c).1 ((by
        have hadj : G.Adj a c := by
          simpa [SimpleGraph.mem_neighborFinset] using hc
        exact (canonicalKey_mem_oddIncidentSupport_iff multiplicity a c).2 hadj))).1
    rcases lt_or_gt_of_ne hbne with hab | hba <;>
      rcases lt_or_gt_of_ne hcne with hac | hca
    · simpa [min_eq_left (le_of_lt hab), max_eq_right (le_of_lt hab),
        min_eq_left (le_of_lt hac), max_eq_right (le_of_lt hac)] using
        congrArg Prod.snd heq
    · have : a = c := by
        simpa [min_eq_left (le_of_lt hab), max_eq_right (le_of_lt hab),
          min_eq_right (le_of_lt hca), max_eq_left (le_of_lt hca)] using
          congrArg Prod.fst heq
      exact (hcne this).elim
    · have : b = a := by
        simpa [min_eq_right (le_of_lt hba), max_eq_left (le_of_lt hba),
          min_eq_left (le_of_lt hac), max_eq_right (le_of_lt hac)] using
          congrArg Prod.fst heq
      exact (hbne this.symm).elim
    · simpa [min_eq_right (le_of_lt hba), max_eq_left (le_of_lt hba),
        min_eq_right (le_of_lt hca), max_eq_left (le_of_lt hca)] using
        congrArg Prod.fst heq
  · intro q hq
    have hq' := (Finset.mem_filter.mp hq)
    have hkey := (Finset.mem_filter.mp hq'.1).2
    have hinc := hq'.2
    have hlt : q.1 < q.2 :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hq'.1).1).2
    have ha : a = q.1 ∨ a = q.2 := by
      unfold unorderedKeyIncidence at hinc
      split at hinc
      · assumption
      · omega
    rcases ha with ha | ha
    · refine ⟨q.2, ?_, ?_⟩
      · apply (G.mem_neighborFinset a q.2).mpr
        change a ≠ q.2 ∧ Odd (multiplicity (min a q.2, max a q.2))
        subst a
        simpa [min_eq_left (le_of_lt hlt), max_eq_right (le_of_lt hlt)] using
          ⟨(ne_of_lt hlt), hkey⟩
      · subst a
        simp [min_eq_left (le_of_lt hlt), max_eq_right (le_of_lt hlt)]
    · refine ⟨q.1, ?_, ?_⟩
      · apply (G.mem_neighborFinset a q.1).mpr
        change a ≠ q.1 ∧ Odd (multiplicity (min a q.1, max a q.1))
        subst a
        simpa [min_eq_right (le_of_lt hlt), max_eq_left (le_of_lt hlt)] using
          ⟨(ne_of_gt hlt), hkey⟩
      · subst a
        simp [min_eq_right (le_of_lt hlt), max_eq_left (le_of_lt hlt)]

theorem even_degree_oddExchangedKeyLabelGraph
    {L : Type*} [Fintype L] [DecidableEq L] [LinearOrder L]
    (multiplicity : L × L → ℕ)
    (heven : ∀ l, Even (∑ key ∈ exchangedMissPairKeys L,
      unorderedKeyIncidence key l * multiplicity key)) :
    ∀ l, Even ((oddExchangedKeyLabelGraph multiplicity).degree l) := by
  intro l
  rw [degree_oddExchangedKeyLabelGraph_eq_incidentSupport_card]
  exact even_card_oddExchangedKeyIncidentSupport multiplicity l (heven l)

end

end Erdos85
