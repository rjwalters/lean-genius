import Proofs.Erdos85LocalGramPacking

/-!
# Scale-one finite point covers for reverse local-packing intervals

This is the direct consumer needed by the q=9 B.3 collision-star matching
certificate.  Once the collision data constructs a finite set of points
meeting every contracted residual block, no explicit weight function or
rational arithmetic remains at the call site.
-/

namespace Erdos85

variable {V : Type*} [Fintype V]

/-- A strict finite point cover of all candidates left after the forced and
impossible reverse-interval contractions gives a rank deficit at that row. -/
theorem reverseIntervalRankDeficit_of_pointCoverFinset
    {P : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (H W : V → V → Prop) (d : V → ℕ) (u : V)
    (B : V → Finset P) (C : Finset P)
    (hshared : ∀ x y, x ≠ y → ¬ Disjoint (B x) (B y) → W x y)
    (hcover : ∀ x, H u x →
      x ∉ reverseForcedLocalGramNeighborFinset H W d u →
      x ∉ reverseImpossibleLocalGramNeighborFinset H W d u →
      (∀ f ∈ reverseForcedLocalGramNeighborFinset H W d u,
        f ≠ x → ¬ W f x) →
      ¬ Disjoint C (B x))
    (htotal :
      (reverseForcedLocalGramNeighborFinset H W d u).card + C.card < d u) :
    HasReverseIntervalRankDeficitAt H W d u := by
  classical
  let weight : P → ℕ := fun p => if p ∈ C then 1 else 0
  apply reverseIntervalRankDeficit_of_scaledPointCover
      H W d u B weight 1 (by decide) hshared
  · intro x hxH hxF hxI hxcompat
    rcases Finset.not_disjoint_iff.mp
        (hcover x hxH hxF hxI hxcompat) with ⟨p, hpC, hpB⟩
    calc
      1 = weight p := by simp [weight, hpC]
      _ ≤ ∑ q ∈ B x, weight q := by
        exact Finset.single_le_sum
          (fun q _hq => Nat.zero_le (weight q)) hpB
  · simpa [weight] using htotal

/-- Direct graph-facing consumer for a strict scale-one contracted point
cover.  This is the final interface a collision-star certificate needs. -/
theorem false_of_localGramPackingPointCoverFinset
    {P : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]
    (A H W : V → V → Prop) [DecidableRel A]
    (d : V → ℕ) (u : V) (B : V → Finset P) (C : Finset P)
    (hsymm : Std.Symm A)
    (hdegree : ∀ v, (relationNeighborFinset A v).card = d v)
    (hsupport : ∀ v w, A v w → H v w)
    (hgram : ∀ x y w, W x y → A x w → A y w → False)
    (hshared : ∀ x y, x ≠ y → ¬ Disjoint (B x) (B y) → W x y)
    (hcover : ∀ x, H u x →
      x ∉ reverseForcedLocalGramNeighborFinset H W d u →
      x ∉ reverseImpossibleLocalGramNeighborFinset H W d u →
      (∀ f ∈ reverseForcedLocalGramNeighborFinset H W d u,
        f ≠ x → ¬ W f x) →
      ¬ Disjoint C (B x))
    (htotal :
      (reverseForcedLocalGramNeighborFinset H W d u).card + C.card < d u) :
    False := by
  apply false_of_localGramPackingReverseIntervalRankDeficit
      A H W d hsymm hdegree hsupport hgram
  exact ⟨u, reverseIntervalRankDeficit_of_pointCoverFinset
    H W d u B C hshared hcover htotal⟩

#print axioms reverseIntervalRankDeficit_of_pointCoverFinset
#print axioms false_of_localGramPackingPointCoverFinset

end Erdos85
