import Proofs.Erdos85CanonicalExceptionalSignedSupport

/-!
# Population identities for the canonical exceptional support

The support size and signed mass recover the full- and empty-line
populations.  These identities are the exact bridge from the arithmetic
normal-form parameters to the canonical occupancy families.
-/

open SimpleGraph

namespace Erdos85

/-- At positive degree, support cardinality is the sum of the disjoint full
and empty populations. -/
theorem exceptionalSignedSupport_card_eq_full_add_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {q : ℕ} (hq : 0 < q) :
    (exceptionalSignedSupport G S q).card =
      (fullLineCenters G S q).card + (emptyLineCenters G S).card := by
  rw [exceptionalSignedSupport_eq_full_union_empty,
    Finset.card_union_of_disjoint
      (fullLineCenters_disjoint_emptyLineCenters G S hq)]

/-- The coordinate sum of the sparse occupancy sign is full population
minus empty population. -/
theorem sum_exceptionalOccupancySign_eq_full_sub_empty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {q : ℕ} (hq : 0 < q) :
    ∑ x : V, exceptionalOccupancySign G S q x =
      ((fullLineCenters G S q).card : ℤ) -
        (emptyLineCenters G S).card := by
  have hdisj := fullLineCenters_disjoint_emptyLineCenters G S hq
  have hpoint (x : V) :
      exceptionalOccupancySign G S q x =
        (if x ∈ fullLineCenters G S q then (1 : ℤ) else 0) -
          (if x ∈ emptyLineCenters G S then (1 : ℤ) else 0) := by
    have hnotBoth : ¬(x ∈ fullLineCenters G S q ∧
        x ∈ emptyLineCenters G S) := by
      intro h
      exact Finset.disjoint_left.mp hdisj h.1 h.2
    by_cases hxFull : x ∈ fullLineCenters G S q
    · have hxNotEmpty : x ∉ emptyLineCenters G S := fun he =>
        hnotBoth ⟨hxFull, he⟩
      have hoccFull := (mem_fullLineCenters G S q x).mp hxFull
      simp [exceptionalOccupancySign, hxFull, hxNotEmpty, hoccFull]
    · by_cases hxEmpty : x ∈ emptyLineCenters G S
      · have hoccEmpty := (mem_emptyLineCenters G S x).mp hxEmpty
        have hoccNotFull : ¬(G.neighborFinset x ∩ S).card = q := fun h =>
          hxFull ((mem_fullLineCenters G S q x).mpr h)
        have hzeroNotQ : ¬ 0 = q := by omega
        simp [exceptionalOccupancySign, hxFull, hxEmpty,
          hoccEmpty, hzeroNotQ]
      · have hoccNotFull : ¬(G.neighborFinset x ∩ S).card = q := fun h =>
          hxFull ((mem_fullLineCenters G S q x).mpr h)
        have hoccNotEmpty : ¬(G.neighborFinset x ∩ S).card = 0 := fun h =>
          hxEmpty ((mem_emptyLineCenters G S x).mpr h)
        simp [exceptionalOccupancySign, hxFull, hxEmpty,
          hoccNotFull, hoccNotEmpty]
  simp_rw [hpoint, Finset.sum_sub_distrib]
  have hFsum :
      (∑ x : V, if x ∈ fullLineCenters G S q then (1 : ℤ) else 0) =
        (fullLineCenters G S q).card := by
    have hnat := Finset.card_eq_sum_ite
      (s := fullLineCenters G S q) (t := Finset.univ)
      (Finset.subset_univ _)
    exact_mod_cast hnat.symm
  have hEsum :
      (∑ x : V, if x ∈ emptyLineCenters G S then (1 : ℤ) else 0) =
        (emptyLineCenters G S).card := by
    have hnat := Finset.card_eq_sum_ite
      (s := emptyLineCenters G S) (t := Finset.univ)
      (Finset.subset_univ _)
    exact_mod_cast hnat.symm
  rw [hFsum, hEsum]

/-- A support-size and signed-mass specification translates exactly into
the two canonical population equations used by the normal form. -/
theorem exceptionalSignedSupport_population_profile
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) {q c : ℕ} (hq : 0 < q) {d : ℤ}
    (hcard : (exceptionalSignedSupport G S q).card = c)
    (hmass : ∑ x : V, exceptionalOccupancySign G S q x = d) :
    (fullLineCenters G S q).card + (emptyLineCenters G S).card = c ∧
      ((fullLineCenters G S q).card : ℤ) -
        (emptyLineCenters G S).card = d := by
  constructor
  · rw [← hcard, exceptionalSignedSupport_card_eq_full_add_empty G S hq]
  · rw [← hmass, sum_exceptionalOccupancySign_eq_full_sub_empty G S hq]

end Erdos85

#print axioms Erdos85.exceptionalSignedSupport_card_eq_full_add_empty
#print axioms Erdos85.sum_exceptionalOccupancySign_eq_full_sub_empty
#print axioms Erdos85.exceptionalSignedSupport_population_profile
