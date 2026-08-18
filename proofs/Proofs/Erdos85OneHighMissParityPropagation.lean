import Proofs.Erdos85OneHighV2OrbitInvariants

/-! # Propagation of odd one-high miss entries

Every raw miss-table row has even total.  Consequently an odd entry cannot
occur alone in its row.  Symmetry then extends every odd directed entry to a
non-backtracking next odd entry in another row.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- An odd summand in an even finite sum is accompanied by a different odd
summand. -/
theorem exists_other_odd_of_even_sum_of_odd_mem
    {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → Nat) {b : ι}
    (hb : b ∈ S) (hodd : Odd (f b))
    (hsum : Even (∑ x ∈ S, f x)) :
    ∃ c ∈ S, c ≠ b ∧ Odd (f c) := by
  let O := S.filter fun x => Odd (f x)
  have hbO : b ∈ O := Finset.mem_filter.mpr ⟨hb, hodd⟩
  have hcardEven : Even O.card := by
    simpa [O] using
      (Finset.even_sum_iff_even_card_odd f).mp hsum
  have hcardPos : 0 < O.card := Finset.card_pos.mpr ⟨b, hbO⟩
  have hcardTwo : 1 < O.card := by
    rcases hcardEven with ⟨k, hk⟩
    omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcardTwo
  by_cases hxb : x = b
  · exact ⟨y, (Finset.mem_filter.mp hy).1, fun hyb =>
      hxy (hxb.trans hyb.symm), (Finset.mem_filter.mp hy).2⟩
  · exact ⟨x, (Finset.mem_filter.mp hx).1, hxb,
      (Finset.mem_filter.mp hx).2⟩

/-- Every odd far-miss entry in a raw presentation has a distinct odd mate
in the same row. -/
theorem OneHighRawV2Presentation.exists_other_odd_miss_in_row
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (s u : {z : V // z ∈ G.neighborSet v})
    (hu : u ∈ ((Finset.univ.erase s).erase (p.mate s)))
    (hodd : Odd (highBranchMissCount G v s u)) :
    ∃ w ∈ ((Finset.univ.erase s).erase (p.mate s)),
      w ≠ u ∧ Odd (highBranchMissCount G v s w) := by
  have hsumEq := p.sum_far_missCount G hfree hv s
  have hsumEven : Even
      (∑ w ∈ ((Finset.univ.erase s).erase (p.mate s)),
        highBranchMissCount G v s w) := by
    rw [hsumEq]
    exact even_two_mul _
  exact exists_other_odd_of_even_sum_of_odd_mem _ _ hu hodd hsumEven

/-- Symmetry plus even row sums propagates an odd miss edge through its
far endpoint without immediately backtracking. -/
theorem OneHighRawV2Presentation.exists_odd_miss_extension
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (s u : {z : V // z ∈ G.neighborSet v})
    (hu : u ∈ ((Finset.univ.erase s).erase (p.mate s)))
    (hodd : Odd (highBranchMissCount G v s u)) :
    ∃ w ∈ ((Finset.univ.erase u).erase (p.mate u)),
      w ≠ s ∧ Odd (highBranchMissCount G v u w) := by
  have hus : u ≠ s := (Finset.mem_erase.mp
    (Finset.mem_erase.mp hu).2).1
  have hums : u ≠ p.mate s := (Finset.mem_erase.mp hu).1
  have hsmu : s ≠ p.mate u := by
    intro h
    apply hums
    have hm : p.mate s = u := by
      rw [h, p.mate_involutive u]
    exact hm.symm
  have hsFar : s ∈ ((Finset.univ.erase u).erase (p.mate u)) := by
    simp [hus.symm, hsmu]
  have hodd' : Odd (highBranchMissCount G v u s) := by
    rw [← OneHighRawV2Presentation.missCount_comm G hfree v p s u]
    exact hodd
  exact p.exists_other_odd_miss_in_row G hfree hv u s hsFar hodd'

end

end Erdos85
