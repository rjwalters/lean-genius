import Proofs.Erdos85MuNegOneOneFourOwnerCnf
import Proofs.Erdos85EightEightLowOwnerCnfBridge

/-!
# Typed owner model for the μ=-1 `(1,4)` owner-grid CNFs — layer 1

Node: outline F.3 (μ=-1 lane; graph→valuation bridge, increment 1 of
the plan posted in squad msgs 13942/13943).

The checked `(−1,1,4)` certificates are stated over the raw generator
tables (`muNegOneOwners`, `muNegOneTwelve`, …) on `Nat` codes `0..15`.
This layer types those tables over a fixed sixteen-vertex model: the
model graph realised by `muNegOneGAdj`, the two cyclic `ZMod 8` shore
embeddings, the `Fin 80` owner index with its unordered-pair table and
injectivity, and the basic census facts (twelve-set length, adjacency
of within-shore triangle owners).  Everything here is decidable and
carries no graph hypotheses; the graph-facing embedding layers consume
these facts when transporting sol-3's exterior geometry into
`MuNegOneOneFourOwnerConstraintSemantics`.
-/

open SimpleGraph

namespace Erdos85

/-- The owner list has the fixed length 80 in every sector mode. -/
theorem muNegOneOwners_length (uTri vTri : Bool) :
    (muNegOneOwners uTri vTri).length = 80 := by
  revert uTri vTri
  decide

/-- The owner pair at a typed index. -/
def muNegOneOwnerAt (uTri vTri : Bool) (e : Fin 80) : Nat × Nat :=
  (muNegOneOwners uTri vTri)[e.val]!

/-- Both endpoints of every generated owner are internal codes. -/
theorem muNegOneOwnerAt_lt_sixteen (uTri vTri : Bool) (e : Fin 80) :
    (muNegOneOwnerAt uTri vTri e).1 < 16 ∧
      (muNegOneOwnerAt uTri vTri e).2 < 16 := by
  revert uTri vTri e
  decide

/-- First endpoint of a generated owner in the fixed sixteen-vertex
model. -/
def muNegOneOwnerFirst (uTri vTri : Bool) (e : Fin 80) : Fin 16 :=
  ⟨(muNegOneOwnerAt uTri vTri e).1, (muNegOneOwnerAt_lt_sixteen uTri vTri e).1⟩

/-- Second endpoint of a generated owner in the fixed sixteen-vertex
model. -/
def muNegOneOwnerSecond (uTri vTri : Bool) (e : Fin 80) : Fin 16 :=
  ⟨(muNegOneOwnerAt uTri vTri e).2, (muNegOneOwnerAt_lt_sixteen uTri vTri e).2⟩

/-- The unordered internal pair represented by a typed owner index. -/
def muNegOneOwnerSym2 (uTri vTri : Bool) (e : Fin 80) : Sym2 (Fin 16) :=
  s(muNegOneOwnerFirst uTri vTri e, muNegOneOwnerSecond uTri vTri e)

/-- The generated owner list has no duplicate unordered pairs (each
sector mode separately). -/
theorem muNegOneOwnerSym2_injective (uTri vTri : Bool) :
    Function.Injective (muNegOneOwnerSym2 uTri vTri) := by
  revert uTri vTri
  decide

/-- Canonical equivalence between typed owner indices and the range of
the unordered-pair table. -/
noncomputable def muNegOneOwnerRangeEquiv (uTri vTri : Bool) :
    Fin 80 ≃ Set.range (muNegOneOwnerSym2 uTri vTri) :=
  Equiv.ofInjective _ (muNegOneOwnerSym2_injective uTri vTri)

/-- The fixed sixteen-vertex model graph realised by the generator's
`G`-adjacency table: two disjoint octagons. -/
def muNegOneModelGraph : SimpleGraph (Fin 16) where
  Adj x y := muNegOneGAdj x.val y.val = true
  symm := ⟨by
    intro x y h
    have hall : ∀ x y : Fin 16,
        muNegOneGAdj x.val y.val = true → muNegOneGAdj y.val x.val = true := by
      decide
    exact hall x y h⟩
  loopless := ⟨by
    intro x h
    have hall : ∀ x : Fin 16, ¬ muNegOneGAdj x.val x.val = true := by decide
    exact hall x h⟩

instance : DecidableRel muNegOneModelGraph.Adj := fun _ _ =>
  inferInstanceAs (Decidable (_ = true))

/-- First-shore embedding of cyclic coordinates into the model. -/
def muNegOneLeftFin16 (i : ZMod 8) : Fin 16 :=
  Fin.castAdd 8 ((ZMod.finEquiv 8).symm i)

/-- Second-shore embedding of cyclic coordinates into the model. -/
def muNegOneRightFin16 (i : ZMod 8) : Fin 16 :=
  Fin.natAdd 8 ((ZMod.finEquiv 8).symm i)

/-- Within the first shore the model graph is the standard octagon. -/
theorem muNegOneModelGraph_left (i j : ZMod 8) :
    muNegOneModelGraph.Adj (muNegOneLeftFin16 i) (muNegOneLeftFin16 j) ↔
      j - i = 1 ∨ j - i = 7 := by
  revert i j
  decide

/-- Within the second shore the model graph is the standard octagon. -/
theorem muNegOneModelGraph_right (i j : ZMod 8) :
    muNegOneModelGraph.Adj (muNegOneRightFin16 i) (muNegOneRightFin16 j) ↔
      j - i = 1 ∨ j - i = 7 := by
  revert i j
  decide

/-- The model graph has no cross-shore edges. -/
theorem muNegOneModelGraph_cross (i j : ZMod 8) :
    ¬ muNegOneModelGraph.Adj (muNegOneLeftFin16 i) (muNegOneRightFin16 j) := by
  revert i j
  decide

/-- Every owner's twelve-set has exactly twelve elements. -/
theorem muNegOneTwelve_length (uTri vTri : Bool) (e : Fin 80) :
    (muNegOneTwelve (muNegOneOwnerAt uTri vTri e)).length = 12 := by
  revert uTri vTri e
  decide

/-- An owner pair is `G`-adjacent exactly when it is a within-shore pair
of a triangle-mode shore. -/
theorem muNegOneOwnerAt_adjacent_iff (uTri vTri : Bool) (e : Fin 80) :
    muNegOneAdjacentPair (muNegOneOwnerAt uTri vTri e) = true ↔
      ((e.val < 8 ∧ uTri = true) ∨
        (8 ≤ e.val ∧ e.val < 16 ∧ vTri = true)) := by
  revert uTri vTri e
  decide

/-- Cross owners are the cells `(i, 8+j)` in row-major order after the
sixteen within-shore owners. -/
theorem muNegOneOwnerAt_cross (uTri vTri : Bool) (e : Fin 80)
    (he : 16 ≤ e.val) :
    muNegOneOwnerAt uTri vTri e =
      ((e.val - 16) / 8, 8 + (e.val - 16) % 8) := by
  revert uTri vTri e
  decide

/-- Within-shore owners of the first shore in explicit coordinates. -/
theorem muNegOneOwnerAt_left (uTri vTri : Bool) (e : Fin 80)
    (he : e.val < 8) :
    muNegOneOwnerAt uTri vTri e =
      (min e.val ((e.val + if uTri then 1 else 3) % 8),
        max e.val ((e.val + if uTri then 1 else 3) % 8)) := by
  revert uTri vTri e
  decide

/-- Within-shore owners of the second shore in explicit coordinates. -/
theorem muNegOneOwnerAt_right (uTri vTri : Bool) (e : Fin 80)
    (he : 8 ≤ e.val) (he' : e.val < 16) :
    muNegOneOwnerAt uTri vTri e =
      (min (e.val) (8 + ((e.val - 8 + if vTri then 1 else 3) % 8)),
        max (e.val) (8 + ((e.val - 8 + if vTri then 1 else 3) % 8))) := by
  revert uTri vTri e
  decide

end Erdos85

#print axioms Erdos85.muNegOneOwnerSym2_injective
#print axioms Erdos85.muNegOneTwelve_length
