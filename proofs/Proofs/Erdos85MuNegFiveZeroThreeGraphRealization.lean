import Proofs.Erdos85MuNegFiveZeroThreeOwnerServiceBridge
import Proofs.Erdos85SizeTwoMuNegFiveAlignedShoreSwitch
import Proofs.Erdos85SizeTwoOwnerVertexDictionary

/-!
# Graph realization of the h503 owner relations

The 72 finite candidates consist of eight fixed antipodal within-shore pairs
and all 64 cross pairs.  This file maps their Nat codes to the two cyclic
shore embeddings and realizes activity/hits by exterior owner vertices.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]
  [DecidableRel (antipodalGraph G).Adj]
  [DecidableRel (triangleFreeEdgeGraph G).Adj]
  [Fintype (secondOrderDefectGraph G).ConnectedComponent]
  [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
  (c : (secondOrderDefectGraph G).ConnectedComponent)

/-- Interpret codes `0..7` on the first shore and `8..15` on the second. -/
def muNegFiveZeroThreeCodeVertex
    (u v : ZMod 8 → c.supp) (x : Nat) : V :=
  if x < 8 then (u (x : ZMod 8)).1
  else (v (x - 8 : ZMod 8)).1

def muNegFiveZeroThreeOwnerEndpoints
    (u v : ZMod 8 → c.supp) (e : Nat) : V × V :=
  let p := muNegFiveZeroThreeOwnerAt e
  (muNegFiveZeroThreeCodeVertex G c u v p.1,
    muNegFiveZeroThreeCodeVertex G c u v p.2)

def MuNegFiveZeroThreeOwnerVertex
    (u v : ZMod 8 → c.supp) (e : Nat) (z : V) : Prop :=
  z ∉ c.supp ∧
    G.Adj (muNegFiveZeroThreeOwnerEndpoints G c u v e).1 z ∧
    G.Adj (muNegFiveZeroThreeOwnerEndpoints G c u v e).2 z

def muNegFiveZeroThreeGraphActive
    (u v : ZMod 8 → c.supp) (e : Fin 72) : Prop :=
  ∃ z : V, MuNegFiveZeroThreeOwnerVertex G c u v e z

def muNegFiveZeroThreeGraphHit
    (u v : ZMod 8 → c.supp) (e f : Fin 72) : Prop :=
  ∃ z w : V,
    MuNegFiveZeroThreeOwnerVertex G c u v e z ∧
    MuNegFiveZeroThreeOwnerVertex G c u v f w ∧ G.Adj z w

instance (u v : ZMod 8 → c.supp) :
    DecidablePred (muNegFiveZeroThreeGraphActive G c u v) := by
  intro e
  exact Classical.propDecidable _

instance (u v : ZMod 8 → c.supp) :
    DecidableRel (muNegFiveZeroThreeGraphHit G c u v) := by
  intro e f
  exact Classical.propDecidable _

theorem muNegFiveZeroThreeGraphHit_symm
    (u v : ZMod 8 → c.supp) (e f : Fin 72) :
    muNegFiveZeroThreeGraphHit G c u v e f →
      muNegFiveZeroThreeGraphHit G c u v f e := by
  rintro ⟨z, w, he, hf, hzw⟩
  exact ⟨w, z, hf, he, hzw.symm⟩

theorem muNegFiveZeroThreeGraphHit_ends
    (u v : ZMod 8 → c.supp) (e f : Fin 72) :
    muNegFiveZeroThreeGraphHit G c u v e f →
      muNegFiveZeroThreeGraphActive G c u v e ∧
        muNegFiveZeroThreeGraphActive G c u v f := by
  rintro ⟨z, w, he, hf, _⟩
  exact ⟨⟨z, he⟩, ⟨w, hf⟩⟩

theorem muNegFiveZeroThreeGraphHit_witness
    (u v : ZMod 8 → c.supp) {e f : Fin 72}
    (h : muNegFiveZeroThreeGraphHit G c u v e f) :
    ∃ z w : V, z ∉ c.supp ∧ w ∉ c.supp ∧
      G.Adj (muNegFiveZeroThreeOwnerEndpoints G c u v e).1 z ∧
      G.Adj (muNegFiveZeroThreeOwnerEndpoints G c u v e).2 z ∧
      G.Adj (muNegFiveZeroThreeOwnerEndpoints G c u v f).1 w ∧
      G.Adj (muNegFiveZeroThreeOwnerEndpoints G c u v f).2 w ∧
      G.Adj z w := by
  obtain ⟨z, w, he, hf, hzw⟩ := h
  exact ⟨z, w, he.1, hf.1, he.2.1, he.2.2,
    hf.2.1, hf.2.2, hzw⟩

end

end Erdos85

#print axioms Erdos85.muNegFiveZeroThreeGraphHit_symm
#print axioms Erdos85.muNegFiveZeroThreeGraphHit_ends
