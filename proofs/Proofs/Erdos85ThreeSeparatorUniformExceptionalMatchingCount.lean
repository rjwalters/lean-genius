import Proofs.Erdos85ThreeSeparatorExceptionalImageLocation

/-! # Uniform exceptional matching count -/

open Finset

namespace Erdos85

/-- Subtraction-safe arithmetic core of B18.  If `q-a+h` K-points are
common-neighbor targets and the remaining K-points fit inside defect degree
`q-1`, then all `a` eligible X-neighbors contribute: `h=a`. -/
theorem uniform_exceptional_count_forces_h_eq_a
    {q a h dK : ℕ} (hq : 1 ≤ q) (ha : a ≤ q) (hh : h ≤ a)
    (hpartition : dK + (q - a + h) = 2 * q - 1)
    (hdK : dK ≤ q - 1) :
    h = a ∧ dK = q - 1 := by
  omega

/-- Finset form of the B18 count: a partition of `K\{c}` into targets and
K-contained defect neighbors forces q targets and full defect degree. -/
theorem uniform_exceptional_target_partition_saturates
    {V : Type*} [DecidableEq V]
    (K Q N : Finset V) (c : V) (q a h : ℕ)
    (hq : 1 ≤ q) (ha : a ≤ q) (hh : h ≤ a)
    (hKcard : K.card = 2 * q) (hcK : c ∈ K)
    (hpartition : K.erase c = Q ∪ N) (hdisj : Disjoint Q N)
    (hQcard : Q.card = q - a + h) (hNle : N.card ≤ q - 1) :
    h = a ∧ N.card = q - 1 ∧ Q.card = q := by
  have hEraseCard : (K.erase c).card = 2 * q - 1 := by
    rw [Finset.card_erase_of_mem hcK, hKcard]
  have hcount : N.card + (q - a + h) = 2 * q - 1 := by
    have hu := Finset.card_union_of_disjoint hdisj
    rw [← hpartition, hEraseCard, hQcard] at hu
    omega
  obtain ⟨hha, hN⟩ :=
    uniform_exceptional_count_forces_h_eq_a hq ha hh hcount hNle
  refine ⟨hha, hN, ?_⟩
  rw [hQcard, hha]
  omega

/-- The all-a B18 matching image has at least `q-(3a+4)` points in Y. -/
theorem uniform_exceptionalImage_largeShore_lower
    {V : Type*} [DecidableEq V]
    (Q K Y S : Finset V) (q a : ℕ)
    (hQK : Q ⊆ K) (hQcard : Q.card = q)
    (hKcover : K ⊆ Y ∪ S)
    (hSmall : (K ∩ S).card ≤ 3 * a + 4) :
    q - (3 * a + 4) ≤ (Q ∩ Y).card := by
  have houtside : Q \ Y ⊆ K ∩ S := by
    intro z hz
    have hzQ := (Finset.mem_sdiff.mp hz).1
    have hzNotY := (Finset.mem_sdiff.mp hz).2
    have hzK := hQK hzQ
    refine Finset.mem_inter.mpr ⟨hzK, ?_⟩
    rcases Finset.mem_union.mp (hKcover hzK) with hzY | hzS
    · exact False.elim (hzNotY hzY)
    · exact hzS
  have houtsideCard : (Q \ Y).card ≤ 3 * a + 4 :=
    (Finset.card_le_card houtside).trans hSmall
  have hsplit := Finset.card_sdiff_add_card_inter Q Y
  rw [hQcard] at hsplit
  omega

#print axioms uniform_exceptional_count_forces_h_eq_a
#print axioms uniform_exceptional_target_partition_saturates
#print axioms uniform_exceptionalImage_largeShore_lower

end Erdos85
