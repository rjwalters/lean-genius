import Proofs.Erdos85BoundaryQuotientExcess

/-!
# Parity transfer from a minimum defect component

The quotient identities do not by themselves make the minimum-size class
closed.  This file records the exact parity information available along an
edge from a minimum component to a longer component: the reverse quotient
entry is one, the forward entry is the length ratio, and (because the
minimum length is odd) the target length is odd exactly when that ratio is
odd.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Along a positive quotient edge from a minimum defect component to a
strictly longer one, oddness of the longer cycle is equivalent to oddness
of the forward quotient entry (the covering multiplicity). -/
theorem secondOrder_minimumComponent_target_order_odd_iff_ratio_odd
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hcmin : ∀ l : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard ≤ l.supp.ncard)
    (hlt : c.supp.ncard < e.supp.ncard)
    (hpos : 0 < componentQuotientMatrix G
      (secondOrderDefectGraph G) c e) :
    Odd e.supp.ncard ↔
      Odd (componentQuotientMatrix G (secondOrderDefectGraph G) c e) := by
  have hentries := secondOrder_componentQuotientMatrix_entries_of_size_lt
    G hfree hd heven hmin hcard c e hlt hpos
  have hcodd := secondOrder_minimumComponent_order_odd
    G hfree hd heven hmin hcard c hcmin
  rw [← hentries.2.2]
  rw [Nat.odd_mul]
  simp only [hcodd, true_and]

/-- Expanded form of the minimum-to-longer edge structure.  This is a
convenient interface for arguments that must rule out even covering
multiplicities by additional geometric information. -/
theorem secondOrder_minimumComponent_longer_edge_structure
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hcmin : ∀ l : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard ≤ l.supp.ncard)
    (hlt : c.supp.ncard < e.supp.ncard)
    (hpos : 0 < componentQuotientMatrix G
      (secondOrderDefectGraph G) c e) :
    componentQuotientMatrix G (secondOrderDefectGraph G) e c = 1 ∧
      c.supp.ncard ∣ e.supp.ncard ∧
      c.supp.ncard *
        componentQuotientMatrix G (secondOrderDefectGraph G) c e =
          e.supp.ncard ∧
      (Odd e.supp.ncard ↔
        Odd (componentQuotientMatrix G (secondOrderDefectGraph G) c e)) := by
  have hentries := secondOrder_componentQuotientMatrix_entries_of_size_lt
    G hfree hd heven hmin hcard c e hlt hpos
  exact ⟨hentries.1, hentries.2.1, hentries.2.2,
    secondOrder_minimumComponent_target_order_odd_iff_ratio_odd
      G hfree hd heven hmin hcard c e hcmin hlt hpos⟩

end

end Erdos85
