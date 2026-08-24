import Proofs.Erdos85EulerianShoreSegmentPairing

/-!
# Endpoint prices of routed shore segments

In the additive branch of the global relay price gauge, restrict the edge
price and vertex potential to an induced shore.  Every internal owner route
then telescopes to the sum of the potentials at its paired cut crossings.
This is the gauge-invariant price carried by the segment construction.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Restrict a binary edge price to an induced vertex shore. -/
def shoreRestrictedF2EdgePrice
    {V : Type*} (k : V → V → ZMod 2) (U : Set V) :
    {u : V // u ∈ U} → {u : V // u ∈ U} → ZMod 2 :=
  fun u v => k u.1 v.1

/-- A global edge-potential equation restricts to the induced shore, so the
price of every shore-internal walk is determined by its two endpoints. -/
theorem f2WalkWeight_shoreRestricted_eq_endpointPotentialSum
    {V : Type*} {H : SimpleGraph V} (k : V → V → ZMod 2)
    (lam : V → ZMod 2)
    (hpotential : ∀ {u v}, H.Adj u v → k u v = lam u + lam v)
    (U : Set V) {u v : {x : V // x ∈ U}}
    (p : (H.induce U).Walk u v) :
    f2WalkWeight (shoreRestrictedF2EdgePrice k U) p =
      lam u.1 + lam v.1 := by
  apply f2WalkWeight_eq_endpointPotentialSum
    (shoreRestrictedF2EdgePrice k U) (fun x => lam x.1)
  intro a b hab
  exact hpotential hab

/-- Every segment of a paired shore cut has its canonical endpoint price in
the additive branch. -/
theorem pairedShoreSegment_price_eq_endpointPotentialSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (U : Finset V)
    (mate : (Σ _ : {u : V // u ∈ U}, V) →
      (Σ _ : {u : V // u ∈ U}, V))
    (segment : ∀ o, o ∈ shoreGraphCutOccurrences H U →
      (H.induce (↑U : Set V)).Walk o.1 (mate o).1)
    (k : V → V → ZMod 2) (lam : V → ZMod 2)
    (hpotential : ∀ {u v}, H.Adj u v → k u v = lam u + lam v) :
    ∀ o (ho : o ∈ shoreGraphCutOccurrences H U),
      f2WalkWeight (shoreRestrictedF2EdgePrice k (↑U : Set V))
          (segment o ho) =
        lam o.1.1 + lam (mate o).1.1 := by
  intro o ho
  exact f2WalkWeight_shoreRestricted_eq_endpointPotentialSum
    k lam hpotential (↑U : Set V) (segment o ho)

/-- Owner-indexed form: the segment launched by a marked pole has price the
sum of the pole potential and its retained-owner exit potential. -/
theorem twoPoleOwner_shoreSegment_price_eq_endpointPotentialSum
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (U : Finset V)
    (mate : (Σ _ : {u : V // u ∈ U}, V) →
      (Σ _ : {u : V // u ∈ U}, V))
    (segment : ∀ o, o ∈ shoreGraphCutOccurrences H U →
      (H.induce (↑U : Set V)).Walk o.1 (mate o).1)
    (pole : Bool → (Σ _ : {u : V // u ∈ U}, V))
    (hpole : ∀ owner, pole owner ∈ shoreGraphCutOccurrences H U)
    (k : V → V → ZMod 2) (lam : V → ZMod 2)
    (hpotential : ∀ {u v}, H.Adj u v → k u v = lam u + lam v) :
    ∀ owner,
      f2WalkWeight (shoreRestrictedF2EdgePrice k (↑U : Set V))
          (segment (pole owner) (hpole owner)) =
        lam (pole owner).1.1 +
          lam (twoPoleOwnerExit mate pole owner).1.1 := by
  intro owner
  exact pairedShoreSegment_price_eq_endpointPotentialSum
    H U mate segment k lam hpotential (pole owner) (hpole owner)

end

end Erdos85

#print axioms Erdos85.f2WalkWeight_shoreRestricted_eq_endpointPotentialSum
#print axioms Erdos85.pairedShoreSegment_price_eq_endpointPotentialSum
#print axioms Erdos85.twoPoleOwner_shoreSegment_price_eq_endpointPotentialSum
