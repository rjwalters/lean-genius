import Proofs.Erdos85SizeTwoEigenlineCyclicRoutingCoincidence

/-!
# Edge-reversal coherence of cyclic routing permutations

Undirected adjacency couples the routing permutations attached to different
source cells.  An edge routed from `(x,t)` through relative row `r` reverses
from its target through relative row `-r` and relative column `t-r`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Routing-graph reversal.**  Every routing witness has a canonically
shifted reverse witness in the routing graph of its target cell. -/
theorem sizeTwoCyclicRoutingRel_reverse
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (r : SizeTwoAdmissibleTargetRow q t.1)
    (c : SizeTwoAdmissibleTargetColumn q)
    (hroute : sizeTwoCyclicRoutingRel q a C x t r c) :
    ∃ (s : sizeTwoAllowedDifference q a)
      (r' : SizeTwoAdmissibleTargetRow q s.1)
      (c' : SizeTwoAdmissibleTargetColumn q),
      s.1 = c.1 - r.1 ∧ r'.1 = -r.1 ∧ c'.1 = t.1 - r.1 ∧
      sizeTwoCyclicRoutingRel q a C (x + r.1) s r' c' := by
  obtain ⟨s, hcol, hadj⟩ := hroute
  have hrev := C.adj_symm hadj
  have hr_adm : s.1 ≠ -r.1 ∧ s.1 ≠ (-r.1) - 1 := by
    constructor
    · intro hs
      apply c.2.1
      rw [hcol, hs]
      abel
    · intro hs
      apply c.2.2
      rw [hcol, hs]
      abel
  have hc_adm : (-r.1) + t.1 ≠ 0 ∧ (-r.1) + t.1 ≠ -1 := by
    constructor
    · intro hc
      apply r.2.1
      calc
        t.1 = r.1 + ((-r.1) + t.1) := by abel
        _ = r.1 + 0 := by rw [hc]
        _ = r.1 := by simp
    · intro hc
      apply r.2.2
      calc
        t.1 = r.1 + ((-r.1) + t.1) := by abel
        _ = r.1 + (-1) := by rw [hc]
        _ = r.1 - 1 := by simp [sub_eq_add_neg]
  let r' : SizeTwoAdmissibleTargetRow q s.1 := ⟨-r.1, hr_adm⟩
  let c' : SizeTwoAdmissibleTargetColumn q := ⟨(-r.1) + t.1, hc_adm⟩
  refine ⟨s, r', c', ?_, rfl, ?_, ?_⟩
  · rw [hcol]
    abel
  · change (-r.1) + t.1 = t.1 - r.1
    abel
  · refine ⟨t, ?_, ?_⟩
    · change (-r.1) + t.1 = (-r.1) + t.1
      rfl
    · simpa [r', add_assoc] using hrev

/-- Equality form of edge-reversal coherence for the explicit routing
equivalences. -/
theorem sizeTwoCyclicRoutingEquiv_reverse
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (y : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = y).card =
        if u.1.2 = y ∨ u.1.2 = y - 1 then 0 else 1)
    (hcol_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = z).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1)
    (routes : SizeTwoCyclicRoutingConstraints q a C)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (r : SizeTwoAdmissibleTargetRow q t.1) :
    let c := sizeTwoCyclicRoutingEquiv
      q a C hrow_hit hcol_hit routes x t r
    ∃ (s : sizeTwoAllowedDifference q a)
      (r' : SizeTwoAdmissibleTargetRow q s.1)
      (c' : SizeTwoAdmissibleTargetColumn q),
      s.1 = c.1 - r.1 ∧ r'.1 = -r.1 ∧ c'.1 = t.1 - r.1 ∧
      sizeTwoCyclicRoutingEquiv q a C hrow_hit hcol_hit routes
        (x + r.1) s r' = c' := by
  dsimp only
  let c := sizeTwoCyclicRoutingEquiv
    q a C hrow_hit hcol_hit routes x t r
  have hroute : sizeTwoCyclicRoutingRel q a C x t r c :=
    (sizeTwoCyclicRoutingRel_iff_routingEquiv
      q a C hrow_hit hcol_hit routes x t r c).2 rfl
  obtain ⟨s, r', c', hs, hr, hc, hrev⟩ :=
    sizeTwoCyclicRoutingRel_reverse
      q a C x t r c hroute
  exact ⟨s, r', c', hs, hr, hc,
    (sizeTwoCyclicRoutingRel_iff_routingEquiv
      q a C hrow_hit hcol_hit routes (x + r.1) s r' c').1 hrev⟩

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicRoutingRel_reverse
#print axioms Erdos85.sizeTwoCyclicRoutingEquiv_reverse
