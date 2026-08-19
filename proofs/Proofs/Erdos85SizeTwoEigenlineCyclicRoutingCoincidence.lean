import Proofs.Erdos85SizeTwoEigenlineCyclicRoutingGraph

/-!
# C4 bounds shifted coincidences of routing permutations

For source cells at bases `x` and `x+d` in the same difference orbit, an
absolute target row has relative coordinates `r` and `r-d`; an absolute
target column similarly has coordinates `c` and `c-d`.  Thus common neighbors
are shifted coincidences of the two pointwise routing permutations.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Relative rows admissible for both source cells at base separation `d`. -/
def SizeTwoCommonAdmissibleTargetRow (q : ℕ) (t d : ZMod q) :=
  {r : ZMod q //
    (t ≠ r ∧ t ≠ r - 1) ∧
    (t ≠ r - d ∧ t ≠ (r - d) - 1)}

noncomputable instance (q : ℕ) [NeZero q] (t d : ZMod q) :
    Fintype (SizeTwoCommonAdmissibleTargetRow q t d) :=
  Subtype.fintype _

/-- The routing graphs for sources at `x` and `x+d` coincide after shifting
both target coordinates by `d`. -/
def sizeTwoCyclicRoutingCoincidence
    (q : ℕ) (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a))
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) (d : ZMod q)
    (r : SizeTwoCommonAdmissibleTargetRow q t.1 d) : Prop :=
  ∃ (c₁ c₂ : SizeTwoAdmissibleTargetColumn q),
    sizeTwoCyclicRoutingRel q a C x t
      ⟨r.1, r.2.1⟩ c₁ ∧
    sizeTwoCyclicRoutingRel q a C (x + d) t
      ⟨r.1 - d, r.2.2⟩ c₂ ∧
    c₂.1 = c₁.1 - d

noncomputable instance (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) (d : ZMod q) :
    DecidablePred (sizeTwoCyclicRoutingCoincidence q a C x t d) :=
  Classical.decPred _

/-- A shifted routing coincidence produces an actual common target cell. -/
theorem sizeTwoCyclicRoutingCoincidence_exists_commonTarget
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a))
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) (d : ZMod q)
    (r : SizeTwoCommonAdmissibleTargetRow q t.1 d)
    (hcoin : sizeTwoCyclicRoutingCoincidence q a C x t d r) :
    ∃ s : sizeTwoAllowedDifference q a,
      C.Adj (sizeTwoCyclicCellAt q a x t)
        (sizeTwoCyclicCellAt q a (x + r.1) s) ∧
      C.Adj (sizeTwoCyclicCellAt q a (x + d) t)
        (sizeTwoCyclicCellAt q a (x + r.1) s) := by
  obtain ⟨c₁, c₂, hc₁, hc₂, hshift⟩ := hcoin
  obtain ⟨s₁, hcol₁, hs₁⟩ := hc₁
  obtain ⟨s₂, hcol₂, hs₂⟩ := hc₂
  have hss : s₂ = s₁ := by
    apply Subtype.ext
    have hval : s₂.1 = s₁.1 := by
      rw [hcol₁, hcol₂] at hshift
      have h := congrArg (fun z : ZMod q => z + d - r.1) hshift
      simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using h
    exact hval
  subst s₂
  refine ⟨s₁, hs₁, ?_⟩
  have hbase : x + d + (r.1 - d) = x + r.1 := by abel
  simpa [hbase] using hs₂

/-- **Permutation coincidence bound from C4-freeness.**  Two distinct
translated source cells can have at most one shifted coincidence row. -/
theorem sizeTwoCyclicRoutingCoincidence_card_le_one
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a))
    [DecidableRel C.Adj]
    (hfree : ¬ containsC4 (sizeTwoCyclicExteriorCell q a) C)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) (d : ZMod q)
    (hd : d ≠ 0) :
    ((Finset.univ : Finset (SizeTwoCommonAdmissibleTargetRow q t.1 d)).filter
      fun r => sizeTwoCyclicRoutingCoincidence q a C x t d r).card ≤ 1 := by
  letI : DecidableEq (SizeTwoCommonAdmissibleTargetRow q t.1 d) :=
    Classical.decEq _
  rw [Finset.card_le_one]
  intro r hr r' hr'
  rw [Finset.mem_filter] at hr hr'
  obtain ⟨s, hs₁, hs₂⟩ :=
    sizeTwoCyclicRoutingCoincidence_exists_commonTarget
      q a C x t d r hr.2
  obtain ⟨s', hs₁', hs₂'⟩ :=
    sizeTwoCyclicRoutingCoincidence_exists_commonTarget
      q a C x t d r' hr'.2
  by_contra hrr
  apply hfree
  have hsource : sizeTwoCyclicCellAt q a x t ≠
      sizeTwoCyclicCellAt q a (x + d) t := by
    intro heq
    apply hd
    have hx := sizeTwoCyclicCellAt_injective q a t heq
    apply add_left_cancel (a := x)
    simpa using hx
  have htarget : sizeTwoCyclicCellAt q a (x + r.1) s ≠
      sizeTwoCyclicCellAt q a (x + r'.1) s' := by
    intro heq
    apply hrr
    apply Subtype.ext
    have hbase := congrArg
      (fun u => (sizeTwoCyclicExteriorCellEquiv q a u).1) heq
    simpa [sizeTwoCyclicCellAt] using add_left_cancel hbase
  exact containsC4_of_two_common hsource htarget
    (C.adj_symm hs₁) (C.adj_symm hs₂)
    (C.adj_symm hs₁') (C.adj_symm hs₂')

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicRoutingCoincidence_exists_commonTarget
#print axioms Erdos85.sizeTwoCyclicRoutingCoincidence_card_le_one
