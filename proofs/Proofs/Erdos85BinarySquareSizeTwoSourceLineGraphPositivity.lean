import Proofs.Erdos85BinarySquareSizeTwoSourceLineGraph

/-! # Positivity of source-restricted size-two owner line graphs -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Every source block of a normalized size-two owner color retains the
line-graph lower spectral bound: its adjacency matrix shifted by `2I` is
positive semidefinite.  This is the principal-submatrix constraint missing
from abstract commuting regular-block models. -/
theorem binarySquare_regular_sizeTwoPart_restrictedOwner_adjMatrix_add_two_posSemidef
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (source owner : (secondOrderDefectGraph G).ConnectedComponent)
    (howner : owner.supp.ncard = q * 2) :
    ((restrictedComponentOwnerGraph G source owner).adjMatrix ℤ +
      (2 : ℤ) • 1).PosSemidef := by
  have hglobal :=
    binarySquare_regular_componentOwnerGraph_adjMatrix_add_posSemidef
      G hfree hq hreg hcard owner howner
  have hprincipal := hglobal.submatrix (fun x : source.supp => x.1)
  have heq :
      ((componentOwnerGraph G (secondOrderDefectGraph G) owner).adjMatrix ℤ +
          (2 : ℤ) • 1).submatrix (fun x : source.supp => x.1)
            (fun x : source.supp => x.1) =
        (restrictedComponentOwnerGraph G source owner).adjMatrix ℤ +
          (2 : ℤ) • 1 := by
    ext x y
    change
      (if (componentOwnerGraph G (secondOrderDefectGraph G) owner).Adj x.1 y.1
          then (1 : ℤ) else 0) + 2 * (if x.1 = y.1 then 1 else 0) =
        (if (componentOwnerGraph G (secondOrderDefectGraph G) owner).Adj x.1 y.1
          then (1 : ℤ) else 0) + 2 * (if x = y then 1 else 0)
    by_cases hxy : x = y
    · subst y
      simp
    · have hval : x.1 ≠ y.1 := fun h => hxy (Subtype.ext h)
      simp [hxy, hval]
  rw [← heq]
  exact hprincipal

end

end Erdos85
