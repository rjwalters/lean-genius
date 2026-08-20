import Proofs.Erdos85MuNegFiveOneTwoCrossOnlyOwnerServiceBridge
import Proofs.Erdos85MuNegFiveZeroThreeGraphRealization
import Proofs.Erdos85MuNegFiveOneTwoShoreGeometry

/-!
# Graph realization of the corrected cross-only h512 owner universe

The corrected h512 certificate numbers the 64 cross pairs directly.  The
older h503 graph development numbers the same pairs inside its 72-element
table, interleaved with eight fixed same-shore pairs.  This file gives the
checked embedding between those tables and reuses the established graph
owner predicates through it.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Insert the four first-shore fixed h503 owners that precede the cross
table.  In rows `0..3` one new fixed owner has appeared; rows `4..7` retain
the accumulated offset four. -/
def muNegFiveOneTwoCrossOnlyToZeroThree (e : Fin 64) : Fin 72 :=
  ⟨e.val + min (e.val / 8 + 1) 4, by omega⟩

theorem muNegFiveOneTwoCrossOnlyToZeroThree_val (e : Fin 64) :
    (muNegFiveOneTwoCrossOnlyToZeroThree e).val =
      e.val + min (e.val / 8 + 1) 4 := rfl

theorem muNegFiveOneTwoCrossOnlyToZeroThree_injective :
    Function.Injective muNegFiveOneTwoCrossOnlyToZeroThree := by
  intro e f h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simp only [muNegFiveOneTwoCrossOnlyToZeroThree_val] at hval
  revert e f
  native_decide

/-- The embedded old-table entry names exactly the corrected cross-only
entry, including its orientation. -/
theorem muNegFiveOneTwoCrossOnly_ownerAt_embed (e : Fin 64) :
    muNegFiveZeroThreeOwnerAt (muNegFiveOneTwoCrossOnlyToZeroThree e) =
      muNegFiveOneTwoCrossOnlyOwnerAt e := by
  revert e
  native_decide

theorem muNegFiveOneTwoCrossOnly_ownerAt_bounds (e : Fin 64) :
    (muNegFiveOneTwoCrossOnlyOwnerAt e).1 < 8 ∧
      8 ≤ (muNegFiveOneTwoCrossOnlyOwnerAt e).2 ∧
      (muNegFiveOneTwoCrossOnlyOwnerAt e).2 < 16 := by
  revert e
  native_decide

theorem muNegFiveOneTwoCrossOnly_ownerAt_injective :
    Function.Injective (fun e : Fin 64 ↦
      muNegFiveOneTwoCrossOnlyOwnerAt e) := by
  intro e f h
  revert e f
  native_decide

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  [Fintype (secondOrderDefectGraph G).ConnectedComponent]
  [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
  (c : (secondOrderDefectGraph G).ConnectedComponent)

/-- Corrected h512 owners are the old graph owners at embedded cross
indices. -/
def MuNegFiveOneTwoCrossOnlyOwnerVertex
    (u v : ZMod 8 → c.supp) (e : Fin 64) (z : V) : Prop :=
  MuNegFiveZeroThreeOwnerVertex G c u v
    (muNegFiveOneTwoCrossOnlyToZeroThree e) z

def muNegFiveOneTwoCrossOnlyGraphActive
    (u v : ZMod 8 → c.supp) (e : Fin 64) : Prop :=
  ∃ z : V, MuNegFiveOneTwoCrossOnlyOwnerVertex G c u v e z

def muNegFiveOneTwoCrossOnlyGraphHit
    (u v : ZMod 8 → c.supp) (e f : Fin 64) : Prop :=
  ∃ z w : V,
    MuNegFiveOneTwoCrossOnlyOwnerVertex G c u v e z ∧
    MuNegFiveOneTwoCrossOnlyOwnerVertex G c u v f w ∧ G.Adj z w

instance (u v : ZMod 8 → c.supp) :
    DecidablePred (muNegFiveOneTwoCrossOnlyGraphActive G c u v) := by
  intro e
  exact Classical.propDecidable _

instance (u v : ZMod 8 → c.supp) :
    DecidableRel (muNegFiveOneTwoCrossOnlyGraphHit G c u v) := by
  intro e f
  exact Classical.propDecidable _

theorem muNegFiveOneTwoCrossOnlyGraphActive_eq_old
    (u v : ZMod 8 → c.supp) (e : Fin 64) :
    muNegFiveOneTwoCrossOnlyGraphActive G c u v e ↔
      muNegFiveZeroThreeGraphActive G c u v
        (muNegFiveOneTwoCrossOnlyToZeroThree e) := Iff.rfl

theorem muNegFiveOneTwoCrossOnlyGraphHit_eq_old
    (u v : ZMod 8 → c.supp) (e f : Fin 64) :
    muNegFiveOneTwoCrossOnlyGraphHit G c u v e f ↔
      muNegFiveZeroThreeGraphHit G c u v
        (muNegFiveOneTwoCrossOnlyToZeroThree e)
        (muNegFiveOneTwoCrossOnlyToZeroThree f) := Iff.rfl

theorem muNegFiveOneTwoCrossOnlyGraphHit_symm
    (u v : ZMod 8 → c.supp) (e f : Fin 64) :
    muNegFiveOneTwoCrossOnlyGraphHit G c u v e f →
      muNegFiveOneTwoCrossOnlyGraphHit G c u v f e := by
  rintro ⟨z, w, he, hf, hzw⟩
  exact ⟨w, z, hf, he, hzw.symm⟩

theorem muNegFiveOneTwoCrossOnlyGraphHit_ends
    (u v : ZMod 8 → c.supp) (e f : Fin 64) :
    muNegFiveOneTwoCrossOnlyGraphHit G c u v e f →
      muNegFiveOneTwoCrossOnlyGraphActive G c u v e ∧
        muNegFiveOneTwoCrossOnlyGraphActive G c u v f := by
  rintro ⟨z, w, he, hf, _⟩
  exact ⟨⟨z, he⟩, ⟨w, hf⟩⟩

end

end Erdos85

#print axioms Erdos85.muNegFiveOneTwoCrossOnly_ownerAt_embed
#print axioms Erdos85.muNegFiveOneTwoCrossOnlyToZeroThree_injective
#print axioms Erdos85.muNegFiveOneTwoCrossOnlyGraphHit_symm
