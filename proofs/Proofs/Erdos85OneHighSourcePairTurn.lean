import Proofs.Erdos85OneHighCanonicalMate

/-! # Local source-pair classification at a label-cycle turn -/

namespace Erdos85

noncomputable section

/-- Quotient the canonical eight root labels by their four standard mate
pairs `01, 23, 45, 67`. -/
def oneHighRootPair (x : Fin 8) : Fin 4 :=
  ⟨x.val / 2, by omega⟩

/-- With four colors, three distinct endpoint colors and the two far-source
constraints leave an exact trichotomy at a turn. -/
theorem fourColor_far_turn_trichotomy
    (a b c s t : Fin 4)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hsa : s ≠ a) (hsb : s ≠ b)
    (htb : t ≠ b) (htc : t ≠ c) :
    s = t ∨ s = c ∨ t = a := by
  by_contra h
  simp only [not_or] at h
  have ha : a.val < 4 := a.isLt
  have hb : b.val < 4 := b.isLt
  have hc : c.val < 4 := c.isLt
  have hs : s.val < 4 := s.isLt
  have ht : t.val < 4 := t.isLt
  have hab' : a.val ≠ b.val := fun e => hab (Fin.ext e)
  have hbc' : b.val ≠ c.val := fun e => hbc (Fin.ext e)
  have hac' : a.val ≠ c.val := fun e => hac (Fin.ext e)
  have hsa' : s.val ≠ a.val := fun e => hsa (Fin.ext e)
  have hsb' : s.val ≠ b.val := fun e => hsb (Fin.ext e)
  have htb' : t.val ≠ b.val := fun e => htb (Fin.ext e)
  have htc' : t.val ≠ c.val := fun e => htc (Fin.ext e)
  have hst' : s.val ≠ t.val := fun e => h.1 (Fin.ext e)
  have hsc' : s.val ≠ c.val := fun e => h.2.1 (Fin.ext e)
  have hta' : t.val ≠ a.val := fun e => h.2.2 (Fin.ext e)
  omega

/-- Canonical eight-root form.  For consecutive cycle edges `(a,b)` and
`(b,c)`, if the three label mate-pairs are distinct and each edge source is
far from its two endpoints, then the adjacent source mate-pairs coincide,
or one source lies in the opposite edge's outer endpoint pair. -/
theorem oneHigh_sourcePair_turn_trichotomy
    (a b c s t : Fin 8)
    (hab : oneHighRootPair a ≠ oneHighRootPair b)
    (hbc : oneHighRootPair b ≠ oneHighRootPair c)
    (hac : oneHighRootPair a ≠ oneHighRootPair c)
    (hsa : oneHighRootPair s ≠ oneHighRootPair a)
    (hsb : oneHighRootPair s ≠ oneHighRootPair b)
    (htb : oneHighRootPair t ≠ oneHighRootPair b)
    (htc : oneHighRootPair t ≠ oneHighRootPair c) :
    oneHighRootPair s = oneHighRootPair t ∨
      oneHighRootPair s = oneHighRootPair c ∨
      oneHighRootPair t = oneHighRootPair a := by
  exact fourColor_far_turn_trichotomy _ _ _ _ _
    hab hbc hac hsa hsb htb htc

/-- If neither edge is sourced from the other edge's outer endpoint pair,
both sources are forced into the unique fourth mate-pair. -/
theorem oneHigh_sourcePairs_eq_of_not_endpointPairs
    (a b c s t : Fin 8)
    (hab : oneHighRootPair a ≠ oneHighRootPair b)
    (hbc : oneHighRootPair b ≠ oneHighRootPair c)
    (hac : oneHighRootPair a ≠ oneHighRootPair c)
    (hsa : oneHighRootPair s ≠ oneHighRootPair a)
    (hsb : oneHighRootPair s ≠ oneHighRootPair b)
    (htb : oneHighRootPair t ≠ oneHighRootPair b)
    (htc : oneHighRootPair t ≠ oneHighRootPair c)
    (hsc : oneHighRootPair s ≠ oneHighRootPair c)
    (hta : oneHighRootPair t ≠ oneHighRootPair a) :
    oneHighRootPair s = oneHighRootPair t := by
  rcases oneHigh_sourcePair_turn_trichotomy a b c s t
    hab hbc hac hsa hsb htb htc with h | h | h
  · exact h
  · exact (hsc h).elim
  · exact (hta h).elim

end

end Erdos85
