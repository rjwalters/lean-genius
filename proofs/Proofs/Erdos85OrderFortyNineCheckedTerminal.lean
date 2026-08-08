import Proofs.Erdos85OrderFortyNineAlignedBooleanBridge
import Proofs.Erdos85DimacsSatBridge

/-!
# Checked finite terminals for the classified order-49 branches

These theorems isolate the only remaining certificate-specific input: an
LRAT proof accepted against the CNF generated in Lean for each representative.
-/

namespace Erdos85

open Std Sat
open Std.Tactic.BVDecide

theorem false_of_orderFortyNine_t2_of_lratChecks
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (hcount : orderFortyNineHighIncidenceCount G 3 = 2)
    (hchecks : ∀ rep ∈ orderFortyNineH9T2Systems,
      ∃ proof : Array LRAT.IntAction,
        LRAT.check proof
          (orderFortyNineGeneratedSatCnf
            (orderFortyNineH9ProfileMasks rep))) : False := by
  obtain ⟨rep, hrep, edges, hc⟩ :=
    orderFortyNine_exists_booleanTerminal_t2
      G hfree hmin hcard hHigh hcount
  obtain ⟨proof, hcheck⟩ := hchecks rep hrep
  exact false_of_orderFortyNine_generated_lrat hc
    (orderFortyNineH9ProfileMasks_high_zero rep) proof hcheck

theorem false_of_orderFortyNine_t3_of_lratChecks
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (hcount : orderFortyNineHighIncidenceCount G 3 = 3)
    (hchecks : ∀ rep ∈ orderFortyNineH9T3Systems,
      ∃ proof : Array LRAT.IntAction,
        LRAT.check proof
          (orderFortyNineGeneratedSatCnf
            (orderFortyNineH9ProfileMasks rep))) : False := by
  obtain ⟨rep, hrep, edges, hc⟩ :=
    orderFortyNine_exists_booleanTerminal_t3
      G hfree hmin hcard hHigh hcount
  obtain ⟨proof, hcheck⟩ := hchecks rep hrep
  exact false_of_orderFortyNine_generated_lrat hc
    (orderFortyNineH9ProfileMasks_high_zero rep) proof hcheck

theorem false_of_orderFortyNine_t4_of_lratChecks
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    (hmin : ∀ x : V, 7 ≤ G.degree x)
    (hcard : Fintype.card V = 49)
    (hHigh : (orderFortyNineHighVertices G).card = 9)
    (hcount : orderFortyNineHighIncidenceCount G 3 = 4)
    (hchecks : ∀ rep ∈ orderFortyNineH9T4Systems,
      ∃ proof : Array LRAT.IntAction,
        LRAT.check proof
          (orderFortyNineGeneratedSatCnf
            (orderFortyNineH9ProfileMasks rep))) : False := by
  obtain ⟨rep, hrep, edges, hc⟩ :=
    orderFortyNine_exists_booleanTerminal_t4
      G hfree hmin hcard hHigh hcount
  obtain ⟨proof, hcheck⟩ := hchecks rep hrep
  exact false_of_orderFortyNine_generated_lrat hc
    (orderFortyNineH9ProfileMasks_high_zero rep) proof hcheck

end Erdos85
