import Mathlib

/-! # Enumerating a finite type with prescribed mapped values -/

namespace Erdos85

private theorem exists_list_map_eq_of_multiset_eq_map
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (r : List β) (s : Multiset α)
    (h : (↑r : Multiset β) = s.map f) :
    ∃ l : List α, (↑l : Multiset α) = s ∧ l.map f = r := by
  induction r generalizing s with
  | nil =>
      have hzero : s.map f = 0 := by simpa using h.symm
      have hs : s = 0 := Multiset.map_eq_zero.mp hzero
      exact ⟨[], by simp [hs], by simp⟩
  | cons a r ih =>
      have ha : a ∈ s.map f := by
        rw [← h]
        simp
      obtain ⟨b, hb, hfb⟩ := Multiset.mem_map.mp ha
      have htail : (↑r : Multiset β) = (s.erase b).map f := by
        rw [Multiset.map_erase_of_mem f s hb, ← h, hfb]
        simp
      obtain ⟨l, hl, hmap⟩ := ih (s.erase b) htail
      refine ⟨b :: l, ?_, ?_⟩
      · change b ::ₘ (↑l : Multiset α) = s
        rw [hl]
        exact Multiset.cons_erase hb
      · simp [hfb, hmap]

/-- A multiset equality between prescribed values and all values of a finite
type can be lifted to an enumeration realizing those values pointwise. -/
theorem exists_equiv_fin_of_multiset_eq_map
    {C β : Type*} [Fintype C] [DecidableEq C] [DecidableEq β]
    (f : C → β) (r : List β)
    (h : (↑r : Multiset β) =
      (Finset.univ : Finset C).val.map f) :
    ∃ e : Fin r.length ≃ C, ∀ i, f (e i) = r.get i := by
  obtain ⟨l, hl, hmap⟩ :=
    exists_list_map_eq_of_multiset_eq_map f r
      (Finset.univ : Finset C).val h
  have hlen : r.length = l.length := by
    have hc := congrArg List.length hmap
    simpa using hc.symm
  have hnodup : l.Nodup := by
    change (↑l : Multiset C).Nodup
    rw [hl]
    exact Finset.nodup _
  have hsurj : Function.Surjective l.get := by
    intro c
    have hc : c ∈ l := by
      change c ∈ (↑l : Multiset C)
      rw [hl]
      simp
    obtain ⟨i, hi⟩ := List.get_of_mem hc
    exact ⟨i, hi⟩
  let el : Fin l.length ≃ C := Equiv.ofBijective l.get
    ⟨List.nodup_iff_injective_get.mp hnodup, hsurj⟩
  let e : Fin r.length ≃ C := finCongr hlen |>.trans el
  refine ⟨e, ?_⟩
  intro i
  change f (l.get (finCongr hlen i)) = r.get i
  rw [List.get_eq_getElem, List.get_eq_getElem]
  have hil : i.val < l.length := by omega
  have him : i.val < (l.map f).length := by simpa using hil
  change f (l[i.val]'hil) = r[i.val]'i.isLt
  calc
    f (l[i.val]'hil) = (l.map f)[i.val]'him := (List.getElem_map f).symm
    _ = r[i.val]'i.isLt := by
      have hg := congrArg (fun xs : List β => xs[i.val]?) hmap
      rw [List.getElem?_eq_getElem him,
        List.getElem?_eq_getElem i.isLt] at hg
      exact Option.some.inj hg

end Erdos85
