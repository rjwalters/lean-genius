import Proofs.Erdos85CycleCoverGraph

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

/-- A positive edge from a minimum defect cycle to a longer cycle is an
actual globally oriented cyclic cover.  Its degree is the forward quotient
entry, and parity of that degree is exactly parity of the target cycle. -/
theorem exists_minimumComponent_longer_cycleCover
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d r n : ℕ} [NeZero r] [NeZero n]
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (hr : 3 ≤ r) (hn : 3 ≤ n)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hcmin : ∀ l : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard ≤ l.supp.ncard)
    (hlt : c.supp.ncard < e.supp.ncard)
    (hpos : 0 < componentQuotientMatrix G
      (secondOrderDefectGraph G) c e)
    (u : ZMod r → V) (v : ZMod n → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (huRange : Set.range u = c.supp) (hvRange : Set.range v = e.supp)
    (huD : ∀ x, (secondOrderDefectGraph G).neighborFinset (u x) =
      {u (x - 1), u (x + 1)})
    (hvD : ∀ y, (secondOrderDefectGraph G).neighborFinset (v y) =
      {v (y - 1), v (y + 1)}) :
    ∃ f : ZMod n → ZMod r,
      (∀ x y, G.Adj (u x) (v y) ↔ x = f y) ∧
      ((∀ y, f (y + 1) = f y + 1) ∨
        (∀ y, f (y + 1) = f y - 1)) ∧
      c.supp.ncard *
          componentQuotientMatrix G (secondOrderDefectGraph G) c e =
        e.supp.ncard ∧
      (Odd e.supp.ncard ↔
        Odd (componentQuotientMatrix G (secondOrderDefectGraph G) c e)) := by
  have hs := secondOrder_minimumComponent_longer_edge_structure
    G hfree hd heven hmin hcard c e hcmin hlt hpos
  obtain ⟨f, hf, horient⟩ :=
    exists_cycleCoverMap_of_componentQuotient_eq_one
      G hfree hd heven hmin hcard hr hn c e u v huinj hvinj
        huRange hvRange huD hvD hs.1
  exact ⟨f, hf, horient, hs.2.2.1, hs.2.2.2⟩

end

end Erdos85
