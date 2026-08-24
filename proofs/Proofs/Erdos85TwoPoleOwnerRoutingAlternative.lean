import Proofs.Erdos85F2WalkWeightPotential

/-!
# Two-pole owner routing through a paired cut

After decomposing an Eulerian cut into two-ended segments, the segment
pairing is a fixed-point-free involution on the cut occurrences.  This file
records the exact owner-resolved alternative used in the Baer coupling
audit: two distinguished pole occurrences either pair with one another, or
they launch two distinct ordinary exits.  In the additive branch, the price
of each launched exit is the sum of its endpoint potentials.
-/

namespace Erdos85

/-- Remove the two marked pole occurrences from a finite occurrence set. -/
def twoPoleOrdinaryOccurrences
    {O : Type*} [DecidableEq O] (S : Finset O) (pole0 pole1 : O) : Finset O :=
  (S.erase pole0).erase pole1

/-- The two owner labels select the mates of the corresponding pole
occurrences.  This is the canonical owner-retaining exit map once a segment
pairing has been fixed. -/
def twoPoleOwnerExit {O : Type*} (mate : O → O) (pole : Bool → O) : Bool → O :=
  fun owner => mate (pole owner)

/-- **Two-pole owner-routing alternative.**  For a fixed-point-free
involution on a finite set, two distinct marked occurrences either pair
directly (the cross-owner through), or their owner-indexed mates are two
distinct occurrences outside the marked pair.

This is the occurrence-level form of the routing assertion following
`(73rnz_cjibkp)`: owner labels are retained by indexing the two exits with
`Bool`; no arbitrary relabeling is needed. -/
theorem twoPoleOwnerExit_crossOwner_or_injective_ordinary
    {O : Type*} [DecidableEq O]
    (mate : O → O) (S : Finset O) (pole : Bool → O)
    (hpole : ∀ owner, pole owner ∈ S)
    (hpoles : Function.Injective pole)
    (hclosed : ∀ o ∈ S, mate o ∈ S)
    (hinvol : ∀ o ∈ S, mate (mate o) = o)
    (hfree : ∀ o ∈ S, mate o ≠ o) :
    mate (pole false) = pole true ∨
      (Function.Injective (twoPoleOwnerExit mate pole) ∧
        ∀ owner, twoPoleOwnerExit mate pole owner ∈
          twoPoleOrdinaryOccurrences S (pole false) (pole true)) := by
  by_cases hthrough : mate (pole false) = pole true
  · exact Or.inl hthrough
  · right
    have hpole_ne : pole false ≠ pole true := by
      intro h
      exact Bool.false_ne_true (hpoles h)
    have hreverse : mate (pole true) ≠ pole false := by
      intro h
      have hm := congrArg mate h
      rw [hinvol (pole true) (hpole true)] at hm
      exact hthrough hm.symm
    constructor
    · intro i j hij
      cases i <;> cases j
      · rfl
      · exfalso
        have hm := congrArg mate hij
        simp only [twoPoleOwnerExit] at hm
        rw [hinvol (pole false) (hpole false),
          hinvol (pole true) (hpole true)] at hm
        exact hpole_ne hm
      · exfalso
        have hm := congrArg mate hij
        simp only [twoPoleOwnerExit] at hm
        rw [hinvol (pole true) (hpole true),
          hinvol (pole false) (hpole false)] at hm
        exact hpole_ne hm.symm
      · rfl
    · intro owner
      have hmem : mate (pole owner) ∈ S := hclosed _ (hpole owner)
      simp only [twoPoleOwnerExit, twoPoleOrdinaryOccurrences,
        Finset.mem_erase]
      constructor
      · cases owner
        · exact hthrough
        · exact hfree (pole true) (hpole true)
      · constructor
        · cases owner
          · exact hfree (pole false) (hpole false)
          · exact hreverse
        · exact hmem

/-- In the additive-price branch, the two owner-retaining exits carry the
corresponding endpoint-potential prices.  Kept as a separate consumer so a
future geometric construction of the segment involution can use the routing
alternative without committing to a particular price. -/
theorem twoPoleOwnerExit_price_eq_endpointPotentialSum
    {O : Type*} [DecidableEq O]
    (mate : O → O) (S : Finset O) (pole : Bool → O)
    (k : O → O → ZMod 2) (lam : O → ZMod 2)
    (hpole : ∀ owner, pole owner ∈ S)
    (hpotential : ∀ o ∈ S, k o (mate o) = lam o + lam (mate o)) :
    ∀ owner, k (pole owner) (twoPoleOwnerExit mate pole owner) =
      lam (pole owner) + lam (twoPoleOwnerExit mate pole owner) := by
  intro owner
  exact hpotential _ (hpole owner)

end Erdos85

#print axioms Erdos85.twoPoleOwnerExit_crossOwner_or_injective_ordinary
#print axioms Erdos85.twoPoleOwnerExit_price_eq_endpointPotentialSum
