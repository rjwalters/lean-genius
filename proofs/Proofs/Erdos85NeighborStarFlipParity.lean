import Proofs.Erdos85LabeledInvolutionBoundaryParity

/-!
# Flip parity in a paired neighbor star

A fixed-point-free mate involution partitions a witness's neighbor star into
pairs.  For a vertex shore `B`, represent every crossing pair by its unique
endpoint in `B`.  The parity of these representatives is exactly the parity
of `N_A(y) ∩ B`.  This is the local activity/flip identity
`(73rnz_cjibkh)`, and is the fiberwise input to `(73rnz_cjibkzi)`.
-/

open SimpleGraph

namespace Erdos85

/-- The `B`-side representatives of mate pairs crossing `B` in the neighbor
star at `y`.  Each crossing pair occurs exactly once. -/
def neighborStarFlipRepresentatives
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (mate : V → V → V) (y : V) (B : Finset V) : Finset V :=
  (A.neighborFinset y).filter fun v => v ∈ B ∧ mate y v ∉ B

/-- Even form of the paired-star flip identity. -/
theorem even_neighborStarFlipRepresentatives_iff_even_neighborSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (mate : V → V → V)
    (hclosed : ∀ y v, A.Adj y v → A.Adj y (mate y v))
    (hinvol : ∀ y v, A.Adj y v → mate y (mate y v) = v)
    (hfixed : ∀ y v, A.Adj y v → mate y v ≠ v)
    (y : V) (B : Finset V) :
    Even (neighborStarFlipRepresentatives A mate y B).card ↔
      Even (A.neighborFinset y ∩ B).card := by
  have h := even_labeledOccurrenceBlock_iff_even_boundaryRepresentatives
    (mate y) (A.neighborFinset y) id B
    (by
      intro v hv
      rw [SimpleGraph.mem_neighborFinset] at hv ⊢
      exact hclosed y v hv)
    (by
      intro v hv
      rw [SimpleGraph.mem_neighborFinset] at hv
      exact hinvol y v hv)
    (by
      intro v hv
      rw [SimpleGraph.mem_neighborFinset] at hv
      exact hfixed y v hv)
  have hinter : (A.neighborFinset y).filter (fun v => v ∈ B) =
      A.neighborFinset y ∩ B := by
    ext v
    simp
  rw [← hinter]
  simpa [neighborStarFlipRepresentatives, labeledOccurrenceBlock,
    labeledPairBoundaryRepresentatives, and_comm] using h.symm

/-- **Local activity equals flip parity (`73rnz_cjibkh`).**  The number of
mate pairs at `y` crossing `B`, counted once from their `B` endpoint, is odd
exactly when the number of `A`-neighbors of `y` in `B` is odd. -/
theorem odd_neighborStarFlipRepresentatives_iff_odd_neighborSupport
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (mate : V → V → V)
    (hclosed : ∀ y v, A.Adj y v → A.Adj y (mate y v))
    (hinvol : ∀ y v, A.Adj y v → mate y (mate y v) = v)
    (hfixed : ∀ y v, A.Adj y v → mate y v ≠ v)
    (y : V) (B : Finset V) :
    Odd (neighborStarFlipRepresentatives A mate y B).card ↔
      Odd (A.neighborFinset y ∩ B).card := by
  rw [← Nat.not_even_iff_odd, ← Nat.not_even_iff_odd, not_iff_not]
  exact even_neighborStarFlipRepresentatives_iff_even_neighborSupport
    A mate hclosed hinvol hfixed y B

end Erdos85

#print axioms Erdos85.even_neighborStarFlipRepresentatives_iff_even_neighborSupport
#print axioms Erdos85.odd_neighborStarFlipRepresentatives_iff_odd_neighborSupport
