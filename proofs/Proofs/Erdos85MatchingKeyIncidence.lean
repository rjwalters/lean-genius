import Proofs.Erdos85MatchingLabelParity
import Proofs.Erdos85OneHighExchangedPairParity

/-! # Endpoint fibers as unordered-key incidence -/

namespace Erdos85

noncomputable section

def nonconstantMatchingKeyIncidence
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [DecidableEq L] [LinearOrder L]
    (mate : X → X) (label : X → L) (l : L) : ℕ :=
  ∑ x ∈ nonconstantMatchingEdgeSources mate label,
    unorderedKeyIncidence (exchangedMissPairKey mate label x) l

/-- Counting a label on crossing endpoints is the same as summing its
incidence over the canonically oriented nonconstant matching edges. -/
theorem card_nonconstantMatchingLabelFiber_eq_keyIncidence
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [DecidableEq L] [LinearOrder L]
    (mate : X → X) (label : X → L) (l : L)
    (hinv : Function.Involutive mate) (hfree : ∀ x, mate x ≠ x) :
    (nonconstantMatchingLabelFiber mate label l).card =
      nonconstantMatchingKeyIncidence mate label l := by
  classical
  let C := nonconstantMatchingLabelFiber mate label l
  let S := nonconstantMatchingEdgeSources mate label
  let T := S.filter fun x =>
    unorderedKeyIncidence (exchangedMissPairKey mate label x) l = 1
  have hCT : C.card = T.card := by
    apply Finset.card_bij (fun z _ => min z (mate z))
    · intro z hz
      have hz' := (Finset.mem_filter.mp hz).2
      have hne : label z ≠ label (mate z) := fun h => hz'.2 (h ▸ hz'.1)
      have hlt : z < mate z ∨ mate z < z := lt_or_gt_of_ne (hfree z).symm
      apply Finset.mem_filter.mpr
      rcases hlt with hlt | hlt
      · have hmin : min z (mate z) = z := min_eq_left (le_of_lt hlt)
        refine ⟨?_, ?_⟩
        · simpa [S, nonconstantMatchingEdgeSources, hmin, hlt, hne]
        · simp only [hmin, exchangedMissPairKey]
          unfold unorderedKeyIncidence
          split
          · rfl
          · rename_i h
            exfalso
            apply h
            rw [← hz'.1]
            rcases le_total (label z) (label (mate z)) with hle | hle
            · exact Or.inl (min_eq_left hle).symm
            · exact Or.inr (max_eq_left hle).symm
      · have hmin : min z (mate z) = mate z := min_eq_right (le_of_lt hlt)
        refine ⟨?_, ?_⟩
        · have hlabel : label (mate z) ≠ label z := hne.symm
          simpa [S, nonconstantMatchingEdgeSources, hmin, hinv z, hlt, hlabel]
        · simp only [hmin, exchangedMissPairKey, hinv z]
          unfold unorderedKeyIncidence
          split
          · rfl
          · rename_i h
            exfalso
            apply h
            rw [← hz'.1]
            rcases le_total (label (mate z)) (label z) with hle | hle
            · exact Or.inr (max_eq_right hle).symm
            · exact Or.inl (min_eq_right hle).symm
    · intro z hz w hw heq
      have hz' := (Finset.mem_filter.mp hz).2
      have hw' := (Finset.mem_filter.mp hw).2
      have hzm : z = min z (mate z) ∨ mate z = min z (mate z) := by
        by_cases h : z ≤ mate z
        · exact Or.inl (min_eq_left h).symm
        · exact Or.inr (min_eq_right (le_of_not_ge h)).symm
      have hwm : w = min w (mate w) ∨ mate w = min w (mate w) := by
        by_cases h : w ≤ mate w
        · exact Or.inl (min_eq_left h).symm
        · exact Or.inr (min_eq_right (le_of_not_ge h)).symm
      rcases hzm with hzm | hzm <;> rcases hwm with hwm | hwm
      · exact hzm.trans (heq.trans hwm.symm)
      · exfalso
        apply hw'.2
        rw [← hz'.1]
        congr
        exact (hzm.trans (heq.trans hwm.symm)).symm
      · exfalso
        apply hz'.2
        rw [← hw'.1]
        congr
        exact hzm.trans (heq.trans hwm.symm)
      · apply hinv.injective
        exact hzm.trans (heq.trans hwm.symm)
    · intro x hx
      have hxS := (Finset.mem_filter.mp hx).1
      have hxI := (Finset.mem_filter.mp hx).2
      have hxl : label x = l ∨ label (mate x) = l := by
        unfold unorderedKeyIncidence at hxI
        split at hxI
        · rename_i h
          rcases le_total (label x) (label (mate x)) with hle | hle
          · simp [exchangedMissPairKey, min_eq_left hle,
              max_eq_right hle] at h
            rcases h with h | h
            · exact Or.inl h.symm
            · exact Or.inr h.symm
          · simp [exchangedMissPairKey, min_eq_right hle,
              max_eq_left hle] at h
            rcases h with h | h
            · exact Or.inr h.symm
            · exact Or.inl h.symm
        · omega
      rcases hxl with hxl | hxml
      · refine ⟨x, ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _, hxl,
            fun hm => (Finset.mem_filter.mp hxS).2.2 (hxl.trans hm.symm)⟩
        · exact min_eq_left (le_of_lt (Finset.mem_filter.mp hxS).2.1)
      · refine ⟨mate x, ?_, ?_⟩
        · apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, hxml, ?_⟩
          rw [hinv x]
          exact fun hm => (Finset.mem_filter.mp hxS).2.2 (hm.trans hxml.symm)
        · rw [hinv x, min_eq_right]
          exact le_of_lt (Finset.mem_filter.mp hxS).2.1
  rw [hCT]
  change (S.filter fun x =>
      unorderedKeyIncidence (exchangedMissPairKey mate label x) l = 1).card =
    ∑ x ∈ S,
    unorderedKeyIncidence (exchangedMissPairKey mate label x) l
  let p : X → Prop := fun x =>
    l = (exchangedMissPairKey mate label x).1 ∨
      l = (exchangedMissPairKey mate label x).2
  calc
    (S.filter fun x =>
        unorderedKeyIncidence (exchangedMissPairKey mate label x) l = 1).card =
        (S.filter p).card := by
          congr 1
          ext x
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hxS, hx⟩
            refine ⟨hxS, ?_⟩
            by_contra hn
            simp [unorderedKeyIncidence, p, hn] at hx
          · rintro ⟨hxS, hx⟩
            exact ⟨hxS, by simp [unorderedKeyIncidence, p, hx]⟩
    _ = ∑ x ∈ S, if p x then 1 else 0 := by
      symm
      exact Finset.sum_boole p S
    _ = ∑ x ∈ S,
        unorderedKeyIncidence (exchangedMissPairKey mate label x) l := by
      apply Finset.sum_congr rfl
      intro x _
      simp [p, unorderedKeyIncidence]

theorem even_nonconstantMatchingKeyIncidence_of_even
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [DecidableEq L] [LinearOrder L]
    (mate : X → X) (label : X → L) (l : L)
    (hinv : Function.Involutive mate) (hfree : ∀ x, mate x ≠ x)
    (heven : Even (nonconstantMatchingLabelFiber mate label l).card) :
    Even (nonconstantMatchingKeyIncidence mate label l) := by
  rwa [card_nonconstantMatchingLabelFiber_eq_keyIncidence
    mate label l hinv hfree] at heven

end

end Erdos85
