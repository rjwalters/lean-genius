import Proofs.Erdos85OneHighExchangedPairParity

/-! # The three-edge exchanged-label parity pattern

Three genuine unordered label pairs with even total incidence form the
support of a triangle: the keys are distinct and every two share a label.
-/

namespace Erdos85

noncomputable section

private theorem key_eq_of_both_endpoints_mem
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

private theorem first_key_ne_second_of_three_even
    {L : Type*} [LinearOrder L]
    (p q r : L × L) (hr : r.1 < r.2)
    (heven : ∀ l, Even
      (unorderedKeyIncidence p l + unorderedKeyIncidence q l +
        unorderedKeyIncidence r l)) : p ≠ q := by
  intro hpq
  subst q
  have he := heven r.1
  have hrne : r.1 ≠ r.2 := ne_of_lt hr
  by_cases hpr : r.1 = p.1 ∨ r.1 = p.2
  · norm_num [unorderedKeyIncidence, hpr, hrne] at he
  · norm_num [unorderedKeyIncidence, hpr, hrne] at he

private theorem first_key_meets_second_of_three_even
    {L : Type*} [LinearOrder L]
    (p q r : L × L) (hp : p.1 < p.2) (hr : r.1 < r.2)
    (hpr : p ≠ r)
    (heven : ∀ l, Even
      (unorderedKeyIncidence p l + unorderedKeyIncidence q l +
        unorderedKeyIncidence r l)) :
    p.1 = q.1 ∨ p.1 = q.2 ∨ p.2 = q.1 ∨ p.2 = q.2 := by
  by_contra hdisj
  push Not at hdisj
  have hq1 : ¬(p.1 = q.1 ∨ p.1 = q.2) := by
    simp [hdisj.1, hdisj.2.1]
  have hq2 : ¬(p.2 = q.1 ∨ p.2 = q.2) := by
    simp [hdisj.2.2.1, hdisj.2.2.2]
  have hpne : p.1 ≠ p.2 := ne_of_lt hp
  have hr1 : p.1 = r.1 ∨ p.1 = r.2 := by
    by_contra hn
    have he := heven p.1
    norm_num [unorderedKeyIncidence, hpne, hq1, hn] at he
  have hr2 : p.2 = r.1 ∨ p.2 = r.2 := by
    by_contra hn
    have he := heven p.2
    have hpne' : p.2 ≠ p.1 := (ne_of_lt hp).symm
    norm_num [unorderedKeyIncidence, hpne', hq2, hn] at he
  exact hpr (key_eq_of_both_endpoints_mem hp hr hr1 hr2)

/-- Three genuine keys with even total incidence are distinct and pairwise
intersect.  This is the label-multigraph triangle classification in the form
needed by the one-high matching analysis. -/
theorem three_unorderedKeys_even_incidence_triangle_support
    {L : Type*} [LinearOrder L]
    (p q r : L × L) (hp : p.1 < p.2) (hq : q.1 < q.2)
    (hr : r.1 < r.2)
    (heven : ∀ l, Even
      (unorderedKeyIncidence p l + unorderedKeyIncidence q l +
        unorderedKeyIncidence r l)) :
    p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      (p.1 = q.1 ∨ p.1 = q.2 ∨ p.2 = q.1 ∨ p.2 = q.2) ∧
      (p.1 = r.1 ∨ p.1 = r.2 ∨ p.2 = r.1 ∨ p.2 = r.2) ∧
      (q.1 = r.1 ∨ q.1 = r.2 ∨ q.2 = r.1 ∨ q.2 = r.2) := by
  have hpq := first_key_ne_second_of_three_even p q r hr heven
  have hpr := first_key_ne_second_of_three_even p r q hq (by
    intro l
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using heven l)
  have hqr := first_key_ne_second_of_three_even q r p hp (by
    intro l
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using heven l)
  refine ⟨hpq, hpr, hqr, ?_, ?_, ?_⟩
  · exact first_key_meets_second_of_three_even p q r hp hr hpr heven
  · exact first_key_meets_second_of_three_even p r q hp hq hpq (by
      intro l
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using heven l)
  · exact first_key_meets_second_of_three_even q r p hq hp (Ne.symm hpq) (by
      intro l
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using heven l)

end

end Erdos85
