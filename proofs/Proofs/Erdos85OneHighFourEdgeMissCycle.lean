import Proofs.Erdos85OneHighFourEdgeMissParity

/-! # The all-distinct four-edge exchanged-label pattern -/

namespace Erdos85

noncomputable section

private def keysMeet {L : Type*} (p q : L × L) : Prop :=
  p.1 = q.1 ∨ p.1 = q.2 ∨ p.2 = q.1 ∨ p.2 = q.2

private theorem key_eq_of_meets_at_both_endpoints
    {L : Type*} [LinearOrder L]
    {p q : L × L} (hp : p.1 < p.2) (hq : q.1 < q.2)
    (h1 : p.1 = q.1 ∨ p.1 = q.2)
    (h2 : p.2 = q.1 ∨ p.2 = q.2) : p = q := by
  rcases h1 with h11 | h12 <;> rcases h2 with h21 | h22
  · exact ((ne_of_lt hp) (h11.trans h21.symm)).elim
  · exact Prod.ext h11 h22
  · have hrev : q.2 < q.1 := by simpa [h12, h21] using hp
    exact (lt_asymm hq hrev).elim
  · exact ((ne_of_lt hp) (h12.trans h22.symm)).elim

private theorem second_endpoint_mem_iff_not_first_of_meets_of_ne
    {L : Type*} [LinearOrder L]
    {p q : L × L} (hp : p.1 < p.2) (hq : q.1 < q.2)
    (hpq : p ≠ q) (hmeet : keysMeet p q) :
    (p.2 = q.1 ∨ p.2 = q.2) ↔ ¬(p.1 = q.1 ∨ p.1 = q.2) := by
  constructor
  · intro h2 h1
    exact hpq (key_eq_of_meets_at_both_endpoints hp hq h1 h2)
  · intro hnot
    rcases hmeet with h11 | h12 | h21 | h22
    · exact (hnot (Or.inl h11)).elim
    · exact (hnot (Or.inr h12)).elim
    · exact Or.inl h21
    · exact Or.inr h22

/-- If four genuine, pairwise-distinct keys have even total incidence, then
one of the other three is disjoint from the first.  Hence the simple support
has the opposite-edge feature of a four-cycle. -/
theorem exists_key_disjoint_from_first_of_four_distinct_even
    {L : Type*} [LinearOrder L]
    (p q r s : L × L)
    (hp : p.1 < p.2) (hq : q.1 < q.2)
    (hr : r.1 < r.2) (hs : s.1 < s.2)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (heven : ∀ l, Even
      (unorderedKeyIncidence p l + unorderedKeyIncidence q l +
        unorderedKeyIncidence r l + unorderedKeyIncidence s l)) :
    ¬ keysMeet p q ∨ ¬ keysMeet p r ∨ ¬ keysMeet p s := by
  by_contra hall
  push Not at hall
  have hq2 := second_endpoint_mem_iff_not_first_of_meets_of_ne
    hp hq hpq hall.1
  have hr2 := second_endpoint_mem_iff_not_first_of_meets_of_ne
    hp hr hpr hall.2.1
  have hs2 := second_endpoint_mem_iff_not_first_of_meets_of_ne
    hp hs hps hall.2.2
  have hpne : p.1 ≠ p.2 := ne_of_lt hp
  have hpne' : p.2 ≠ p.1 := hpne.symm
  have he1 := heven p.1
  have he2 := heven p.2
  by_cases hq1 : p.1 = q.1 ∨ p.1 = q.2 <;>
    by_cases hr1 : p.1 = r.1 ∨ p.1 = r.2 <;>
    by_cases hs1 : p.1 = s.1 ∨ p.1 = s.2
  all_goals
    simp [unorderedKeyIncidence, hpne, hpne', hq1, hr1, hs1,
      hq2, hr2, hs2] at he1 he2
  all_goals (simp only [Even] at he1 he2; omega)

end

end Erdos85
