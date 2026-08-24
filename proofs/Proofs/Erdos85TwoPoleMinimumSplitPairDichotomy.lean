import Proofs.Erdos85TwoPoleMinimumEndpointDetector
import Proofs.Erdos85PoleOwnerFlipChannelDecomposition

/-!
# Split-pair channel of a minimum two-pole endpoint

This formalizes `(73rnz_bu)--(73rnz_bv)`.  A line met by the support at one
point contributes either a leaf endpoint or one ordinary split pair.  These
are complementary F₂ channels.
-/

namespace Erdos85

/-- The ordinary-side representatives of involution pairs split by a shore. -/
def ordinarySplitPairRepresentatives
    {V : Type*} [DecidableEq V]
    (mate : V → V) (ordinary shore : Finset V) : Finset V :=
  ordinary.filter fun v => v ∈ shore ∧ mate v ∉ shore

/-- **One-unit split-pair dichotomy (`73rnz_bu`).** -/
theorem ordinarySplitPairRepresentatives_eq_of_singleton_line
    {V : Type*} [DecidableEq V]
    (mate : V → V) (line leaves ordinary shore : Finset V) (p : V)
    (hpartition : line = leaves ∪ ordinary)
    (hdisjoint : Disjoint leaves ordinary)
    (hshore : shore ∩ line = {p})
    (hclosed : ∀ v ∈ ordinary, mate v ∈ ordinary)
    (hfree : ∀ v ∈ ordinary, mate v ≠ v) :
    ordinarySplitPairRepresentatives mate ordinary shore =
      if p ∈ ordinary then {p} else ∅ := by
  classical
  have hpBoth : p ∈ shore ∩ line := by
    rw [hshore]
    exact Finset.mem_singleton_self p
  have hpShore : p ∈ shore := (Finset.mem_inter.mp hpBoth).1
  have hpLine : p ∈ line := (Finset.mem_inter.mp hpBoth).2
  have hpCases : p ∈ leaves ∨ p ∈ ordinary := by
    rw [hpartition] at hpLine
    exact Finset.mem_union.mp hpLine
  split_ifs with hpOrd
  · ext v
    simp only [ordinarySplitPairRepresentatives, Finset.mem_filter,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hvOrd, hvShore, hmateOut⟩
      have hvLine : v ∈ line := by
        rw [hpartition]
        exact Finset.mem_union_right _ hvOrd
      have hvp : v = p := by
        have : v ∈ shore ∩ line := Finset.mem_inter.mpr ⟨hvShore, hvLine⟩
        rw [hshore] at this
        exact Finset.mem_singleton.mp this
      exact hvp
    · intro hvp
      subst v
      refine ⟨hpOrd, hpShore, ?_⟩
      intro hmateShore
      have hmateOrd := hclosed p hpOrd
      have hmateLine : mate p ∈ line := by
        rw [hpartition]
        exact Finset.mem_union_right _ hmateOrd
      have hmateEq : mate p = p := by
        have : mate p ∈ shore ∩ line :=
          Finset.mem_inter.mpr ⟨hmateShore, hmateLine⟩
        rw [hshore] at this
        exact Finset.mem_singleton.mp this
      exact hfree p hpOrd hmateEq
  · have hpLeaf : p ∈ leaves := hpCases.resolve_right hpOrd
    ext v
    simp only [ordinarySplitPairRepresentatives, Finset.mem_filter]
    constructor
    · rintro ⟨hvOrd, hvShore, hmateOut⟩
      have hvLine : v ∈ line := by
        rw [hpartition]
        exact Finset.mem_union_right _ hvOrd
      have hvp : v = p := by
        have : v ∈ shore ∩ line := Finset.mem_inter.mpr ⟨hvShore, hvLine⟩
        rw [hshore] at this
        exact Finset.mem_singleton.mp this
      subst v
      exact (Finset.disjoint_left.mp hdisjoint hpLeaf hvOrd).elim
    · intro hv
      simp at hv

/-- The split-pair bit is exactly the ordinary-endpoint indicator. -/
theorem ordinarySplitPair_card_cast_eq_indicator
    {V : Type*} [DecidableEq V]
    (mate : V → V) (line leaves ordinary shore : Finset V) (p : V)
    (hpartition : line = leaves ∪ ordinary)
    (hdisjoint : Disjoint leaves ordinary)
    (hshore : shore ∩ line = {p})
    (hclosed : ∀ v ∈ ordinary, mate v ∈ ordinary)
    (hfree : ∀ v ∈ ordinary, mate v ≠ v) :
    ((ordinarySplitPairRepresentatives mate ordinary shore).card : ZMod 2) =
      if p ∈ ordinary then 1 else 0 := by
  rw [ordinarySplitPairRepresentatives_eq_of_singleton_line mate line leaves
    ordinary shore p hpartition hdisjoint hshore hclosed hfree]
  split_ifs <;> simp

/-- **Complementary endpoint channels (`73rnz_bv`).**  A leaf detector bit
and the ordinary split-pair bit sum to one. -/
theorem endpointDetector_add_ordinarySplitPair_eq_one
    {V : Type*} [DecidableEq V]
    (mate : V → V) (line leaves ordinary shore : Finset V) (p : V)
    (hpartition : line = leaves ∪ ordinary)
    (hdisjoint : Disjoint leaves ordinary)
    (hshore : shore ∩ line = {p})
    (hclosed : ∀ v ∈ ordinary, mate v ∈ ordinary)
    (hfree : ∀ v ∈ ordinary, mate v ≠ v)
    (k : ZMod 2) (hk : k = if p ∈ leaves then 1 else 0) :
    k + (ordinarySplitPairRepresentatives mate ordinary shore).card = 1 := by
  rw [hk, ordinarySplitPair_card_cast_eq_indicator mate line leaves ordinary
    shore p hpartition hdisjoint hshore hclosed hfree]
  have hpBoth : p ∈ shore ∩ line := by
    rw [hshore]
    exact Finset.mem_singleton_self p
  have hpLine : p ∈ line := (Finset.mem_inter.mp hpBoth).2
  rw [hpartition] at hpLine
  rcases Finset.mem_union.mp hpLine with hpLeaf | hpOrd
  · have hpNotOrd : p ∉ ordinary :=
      fun hpO => Finset.disjoint_left.mp hdisjoint hpLeaf hpO
    simp [hpLeaf, hpNotOrd]
  · have hpNotLeaf : p ∉ leaves :=
      fun hpL => Finset.disjoint_left.mp hdisjoint hpL hpOrd
    simp [hpOrd, hpNotLeaf]

end Erdos85

#print axioms Erdos85.ordinarySplitPairRepresentatives_eq_of_singleton_line
#print axioms Erdos85.ordinarySplitPair_card_cast_eq_indicator
#print axioms Erdos85.endpointDetector_add_ordinarySplitPair_eq_one
