import Proofs.Erdos85F2SegmentBoundaryCharacter

/-!
# Binary boundaries of routed walks

An owner route is assembled from two-ended witness segments.  Over `F₂`,
the internal witness labels cancel and the segment boundary telescopes to
the two endpoint labels.  This is the graph-facing bridge from a constructed
route to the pole-source vector in the residual-character quotient.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem zmod2_add_self_walk (z : ZMod 2) : z + z = 0 := by
  calc
    z + z = (2 : ZMod 2) * z := by ring
    _ = 0 := by
      have h2 : (2 : ZMod 2) = 0 := CharP.cast_eq_zero (ZMod 2) 2
      rw [h2, zero_mul]

private theorem f2EndpointSwitch_chain_walk
    {V : Type*} [DecidableEq V] (a b c : V) :
    f2EndpointSwitch a b + f2EndpointSwitch b c =
      f2EndpointSwitch a c := by
  ext x
  simp only [f2EndpointSwitch, Pi.add_apply]
  let A := (Pi.single a (1 : ZMod 2) : V → ZMod 2) x
  let B := (Pi.single b (1 : ZMod 2) : V → ZMod 2) x
  let C := (Pi.single c (1 : ZMod 2) : V → ZMod 2) x
  change (A + B) + (B + C) = A + C
  calc
    (A + B) + (B + C) = A + (B + B) + C := by abel
    _ = A + C := by rw [zmod2_add_self_walk B]; simp

/-- Sum of the endpoint switches of the consecutive edges of a walk. -/
def f2WalkEdgeBoundary
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V} :
    G.Walk u v → (V → ZMod 2)
  | .nil => 0
  | .cons (u := a) (v := b) hab p =>
      f2EndpointSwitch a b + f2WalkEdgeBoundary p

/-- **Walk boundary telescoping.**  Every internal vertex of a routed walk
occurs twice, so its binary edge boundary is supported exactly on the two
endpoints. -/
theorem f2WalkEdgeBoundary_eq_endpointSwitch
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) :
    f2WalkEdgeBoundary p = f2EndpointSwitch u v := by
  induction p with
  | nil =>
      ext x
      simp only [f2WalkEdgeBoundary, Pi.zero_apply, f2EndpointSwitch,
        Pi.add_apply]
      symm
      apply zmod2_add_self_walk
  | @cons u w v huw p ih =>
      simp only [f2WalkEdgeBoundary]
      rw [ih, f2EndpointSwitch_chain_walk u w v]

/-- Boundary of a finite family of routed walks. -/
def f2WalkFamilyBoundary
    {I V : Type*} [Fintype I] [DecidableEq V]
    {G : SimpleGraph V} (start finish : I → V)
    (route : ∀ i, G.Walk (start i) (finish i)) : V → ZMod 2 :=
  ∑ i, f2WalkEdgeBoundary (route i)

/-- A routed family has the same boundary as the sum of its source/sink
endpoint switches; all intermediate witness occurrences disappear. -/
theorem f2WalkFamilyBoundary_eq_sum_endpointSwitch
    {I V : Type*} [Fintype I] [DecidableEq V]
    {G : SimpleGraph V} (start finish : I → V)
    (route : ∀ i, G.Walk (start i) (finish i)) :
    f2WalkFamilyBoundary start finish route =
      ∑ i, f2EndpointSwitch (start i) (finish i) := by
  apply Finset.sum_congr rfl
  intro i _
  exact f2WalkEdgeBoundary_eq_endpointSwitch (route i)

/-- If the endpoint census of an owner-route family is the two-pole source,
then its full internal segment boundary is that same source. -/
theorem f2WalkFamilyBoundary_eq_poleSwitch
    {I V : Type*} [Fintype I] [DecidableEq V]
    {G : SimpleGraph V} (start finish : I → V)
    (route : ∀ i, G.Walk (start i) (finish i)) (pole₁ pole₂ : V)
    (hsource : (∑ i, f2EndpointSwitch (start i) (finish i)) =
      f2EndpointSwitch pole₁ pole₂) :
    f2WalkFamilyBoundary start finish route =
      f2EndpointSwitch pole₁ pole₂ := by
  rw [f2WalkFamilyBoundary_eq_sum_endpointSwitch, hsource]

end

end Erdos85

#print axioms Erdos85.f2WalkEdgeBoundary_eq_endpointSwitch
#print axioms Erdos85.f2WalkFamilyBoundary_eq_sum_endpointSwitch
#print axioms Erdos85.f2WalkFamilyBoundary_eq_poleSwitch
