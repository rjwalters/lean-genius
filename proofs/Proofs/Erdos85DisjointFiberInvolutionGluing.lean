import Proofs.Erdos85EvenFinsetInvolutionPairing

/-!
# Gluing involutions on disjoint fibers

The canonical Baer completion pairs two disjoint parts of each witness star
separately: the non-broken endpoints use the canonical partial involution
`iota`, while the broken endpoints use an owner-adapted completion.  This
file gives the exact abstract gluing operation and proves that no mixed pair
is introduced.
-/

namespace Erdos85

noncomputable section

/-- Use `left` on `S` and `right` away from `S`. -/
def glueDisjointFiberMate
    {V : Type*} [DecidableEq V] (S : Finset V)
    (left right : V → V) (v : V) : V :=
  if v ∈ S then left v else right v

/-- Two involutions preserving disjoint fibers glue to an involution on
their union.  The output also records the stronger no-mixing laws: points
of each input fiber remain in that same fiber. -/
theorem glueDisjointFiberMate_spec
    {V : Type*} [DecidableEq V] (S T : Finset V)
    (hdisjoint : Disjoint S T) (left right : V → V)
    (hleftClosed : ∀ v, v ∈ S → left v ∈ S)
    (hleftInvol : ∀ v, v ∈ S → left (left v) = v)
    (hleftFixed : ∀ v, v ∈ S → left v ≠ v)
    (hrightClosed : ∀ v, v ∈ T → right v ∈ T)
    (hrightInvol : ∀ v, v ∈ T → right (right v) = v)
    (hrightFixed : ∀ v, v ∈ T → right v ≠ v) :
    let mate := glueDisjointFiberMate S left right
    (∀ v, v ∈ S → mate v = left v) ∧
    (∀ v, v ∈ T → mate v = right v) ∧
    (∀ v, v ∈ S → mate v ∈ S) ∧
    (∀ v, v ∈ T → mate v ∈ T) ∧
    (∀ v, v ∈ S ∪ T → mate (mate v) = v) ∧
    (∀ v, v ∈ S ∪ T → mate v ≠ v) := by
  dsimp only
  have hnotS : ∀ v, v ∈ T → v ∉ S := by
    intro v hvT hvS
    exact Finset.disjoint_left.mp hdisjoint hvS hvT
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    simp [glueDisjointFiberMate, hv]
  · intro v hv
    simp [glueDisjointFiberMate, hnotS v hv]
  · intro v hv
    simpa [glueDisjointFiberMate, hv] using hleftClosed v hv
  · intro v hv
    simpa [glueDisjointFiberMate, hnotS v hv] using hrightClosed v hv
  · intro v hv
    rcases Finset.mem_union.mp hv with hvS | hvT
    · have hmS := hleftClosed v hvS
      simp [glueDisjointFiberMate, hvS, hmS, hleftInvol v hvS]
    · have hvNS := hnotS v hvT
      have hmT := hrightClosed v hvT
      have hmNS := hnotS (right v) hmT
      simp [glueDisjointFiberMate, hvNS, hmNS, hrightInvol v hvT]
  · intro v hv
    rcases Finset.mem_union.mp hv with hvS | hvT
    · simpa [glueDisjointFiberMate, hvS] using hleftFixed v hvS
    · simpa [glueDisjointFiberMate, hnotS v hvT] using hrightFixed v hvT

/-- Convenient existence form: if an involution is already fixed on `S`
and the disjoint residual fiber `T` has even cardinality, it extends to a
fixed-point-free involution of `S ∪ T` without changing any `S`-pair. -/
theorem exists_gluedMate_of_involution_of_even_disjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (S T : Finset V) (hdisjoint : Disjoint S T)
    (left : V → V)
    (hleftClosed : ∀ v, v ∈ S → left v ∈ S)
    (hleftInvol : ∀ v, v ∈ S → left (left v) = v)
    (hleftFixed : ∀ v, v ∈ S → left v ≠ v)
    (hevenT : Even T.card) :
    ∃ mate : V → V,
      (∀ v, v ∈ S → mate v = left v) ∧
      (∀ v, v ∈ S → mate v ∈ S) ∧
      (∀ v, v ∈ T → mate v ∈ T) ∧
      (∀ v, v ∈ S ∪ T → mate (mate v) = v) ∧
      (∀ v, v ∈ S ∪ T → mate v ≠ v) := by
  obtain ⟨right, hrightClosed, hrightInvol, hrightFixed, _⟩ :=
    exists_mate_of_even_finset T hevenT
  let mate := glueDisjointFiberMate S left right
  have hspec := glueDisjointFiberMate_spec S T hdisjoint left right
    hleftClosed hleftInvol hleftFixed
    hrightClosed hrightInvol hrightFixed
  exact ⟨mate, hspec.1, hspec.2.2.1, hspec.2.2.2.1,
    hspec.2.2.2.2.1, hspec.2.2.2.2.2⟩

end

end Erdos85

#print axioms Erdos85.glueDisjointFiberMate_spec
#print axioms Erdos85.exists_gluedMate_of_involution_of_even_disjoint
