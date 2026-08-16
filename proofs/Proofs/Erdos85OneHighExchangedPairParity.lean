import Proofs.Erdos85OneHighExchangedMissCounting

/-! # Parity rigidity for two exchanged miss pairs -/

namespace Erdos85

noncomputable section

/-- Incidence of a label in one unordered off-diagonal key. -/
def unorderedKeyIncidence
    {L : Type*} [DecidableEq L] (key : L × L) (l : L) : Nat :=
  if l = key.1 ∨ l = key.2 then 1 else 0

theorem unorderedKeyIncidence_le_one
    {L : Type*} [DecidableEq L] (key : L × L) (l : L) :
    unorderedKeyIncidence key l ≤ 1 := by
  unfold unorderedKeyIncidence
  split <;> omega

/-- Two genuine ordered representatives of unordered pairs whose combined
incidence is even at every label must be the same pair.  Equivalently, an
even two-edge label multigraph consists of two parallel edges. -/
theorem eq_of_two_unorderedKeys_even_incidence
    {L : Type*} [LinearOrder L]
    (p q : L × L) (hp : p.1 < p.2) (hq : q.1 < q.2)
    (heven : ∀ l, Even
      (unorderedKeyIncidence p l + unorderedKeyIncidence q l)) :
    p = q := by
  have hp1q : p.1 = q.1 ∨ p.1 = q.2 := by
    by_contra hn
    have he := heven p.1
    have hnp : ¬(p.1 = q.1 ∨ p.1 = q.2) := hn
    simp [unorderedKeyIncidence, hnp] at he
  have hp2q : p.2 = q.1 ∨ p.2 = q.2 := by
    by_contra hn
    have he := heven p.2
    have hnp : ¬(p.2 = q.1 ∨ p.2 = q.2) := hn
    simp [unorderedKeyIncidence, hnp] at he
  rcases hp1q with h11 | h12 <;> rcases hp2q with h21 | h22
  · have : p.1 = p.2 := h11.trans h21.symm
    exact ((ne_of_lt hp) this).elim
  · exact Prod.ext h11 h22
  · have hrev : q.2 < q.1 := by
      rw [← h12, ← h21]
      exact hp
    exact (lt_asymm hq hrev).elim
  · have : p.1 = p.2 := h12.trans h22.symm
    exact ((ne_of_lt hp) this).elim

/-- Specialization to the canonical keys attached to two nonconstant
matching edges. -/
theorem exchangedMissPairKey_eq_of_even_two_edge_incidence
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [LinearOrder L]
    {mate : X → X} {label : X → L} {x y : X}
    (hx : x ∈ nonconstantMatchingEdgeSources mate label)
    (hy : y ∈ nonconstantMatchingEdgeSources mate label)
    (heven : ∀ l, Even
      (unorderedKeyIncidence (exchangedMissPairKey mate label x) l +
       unorderedKeyIncidence (exchangedMissPairKey mate label y) l)) :
    exchangedMissPairKey mate label x =
      exchangedMissPairKey mate label y := by
  exact eq_of_two_unorderedKeys_even_incidence _ _
    (exchangedMissPairKey_lt_of_mem hx)
    (exchangedMissPairKey_lt_of_mem hy) heven

end

end Erdos85
