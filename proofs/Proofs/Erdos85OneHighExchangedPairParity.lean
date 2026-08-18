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

/-- Frequency of a label among four matching-edge endpoints. -/
def fourEndpointLabelMultiplicity
    {L : Type*} [DecidableEq L] (a b c d l : L) : Nat :=
  (if l = a then 1 else 0) + (if l = b then 1 else 0) +
    (if l = c then 1 else 0) + (if l = d then 1 else 0)

theorem unorderedKeyIncidence_min_max
    {L : Type*} [LinearOrder L] {a b : L} (hab : a ≠ b) (l : L) :
    unorderedKeyIncidence (min a b, max a b) l =
      (if l = a then 1 else 0) + (if l = b then 1 else 0) := by
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · rw [min_eq_left (le_of_lt hablt), max_eq_right (le_of_lt hablt)]
    by_cases hla : l = a <;> by_cases hlb : l = b <;>
      simp [unorderedKeyIncidence, hla, hlb, hab, hab.symm]
  · rw [min_eq_right (le_of_lt hbalt), max_eq_left (le_of_lt hbalt)]
    by_cases hla : l = a <;> by_cases hlb : l = b <;>
      simp [unorderedKeyIncidence, hla, hlb, hab, hab.symm]

/-- Four-label form used by a two-edge graph branch: if both edges are
nonconstant and every label occurs evenly among their four endpoints, the
two canonical unordered label pairs coincide. -/
theorem minMax_pair_eq_of_fourEndpointMultiplicity_even
    {L : Type*} [LinearOrder L]
    (a b c d : L) (hab : a ≠ b) (hcd : c ≠ d)
    (heven : ∀ l, Even (fourEndpointLabelMultiplicity a b c d l)) :
    (min a b, max a b) = (min c d, max c d) := by
  apply eq_of_two_unorderedKeys_even_incidence
  · exact min_lt_max.mpr hab
  · exact min_lt_max.mpr hcd
  · intro l
    rw [unorderedKeyIncidence_min_max hab,
      unorderedKeyIncidence_min_max hcd]
    simpa [fourEndpointLabelMultiplicity, add_assoc] using heven l

/-- Endpoint-label specialization for two concrete nonconstant matching
edges. -/
theorem exchangedMissPairKey_eq_of_fourEndpointMultiplicity_even
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [LinearOrder L]
    {mate : X → X} {label : X → L} {x y : X}
    (hx : x ∈ nonconstantMatchingEdgeSources mate label)
    (hy : y ∈ nonconstantMatchingEdgeSources mate label)
    (heven : ∀ l, Even (fourEndpointLabelMultiplicity
      (label x) (label (mate x)) (label y) (label (mate y)) l)) :
    exchangedMissPairKey mate label x =
      exchangedMissPairKey mate label y := by
  exact minMax_pair_eq_of_fourEndpointMultiplicity_even _ _ _ _
    (Finset.mem_filter.mp hx).2.2 (Finset.mem_filter.mp hy).2.2 heven

end

end Erdos85
