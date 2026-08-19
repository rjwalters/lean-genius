import Proofs.Erdos85SizeTwoEigenlineCyclicDisplacementRouting

/-!
# Permutation structure of cyclic grid routing

Node: `SIZE-TWO-EIGENLINE(q)`, beneath `GAP A-REG-NONBIP`.

For a fixed exterior source cell, the row- and column-hit laws say that its
neighbors form a perfect matching between the admissible target rows and
admissible target columns.  This file packages that matching as an explicit
equivalence, retaining information discarded by displacement marginals.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

def SizeTwoAdmissibleTargetRow (q : ℕ) (t : ZMod q) :=
  {r : ZMod q // t ≠ r ∧ t ≠ r - 1}

def SizeTwoAdmissibleTargetColumn (q : ℕ) :=
  {c : ZMod q // c ≠ 0 ∧ c ≠ -1}

def sizeTwoCyclicRowRoute
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a))
    (routes : SizeTwoCyclicRoutingConstraints q a C)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (r : SizeTwoAdmissibleTargetRow q t.1) :
    sizeTwoAllowedDifference q a :=
  Classical.choose (routes.row x t r.1 r.2)

theorem sizeTwoCyclicRowRoute_spec
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a))
    (routes : SizeTwoCyclicRoutingConstraints q a C)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (r : SizeTwoAdmissibleTargetRow q t.1) :
    C.Adj (sizeTwoCyclicCellAt q a x t)
      (sizeTwoCyclicCellAt q a (x + r.1)
        (sizeTwoCyclicRowRoute q a C routes x t r)) :=
  (Classical.choose_spec (routes.row x t r.1 r.2)).1

theorem sizeTwoCyclicRowRoute_targetColumn_admissible
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hcol_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = z).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1)
    (routes : SizeTwoCyclicRoutingConstraints q a C)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (r : SizeTwoAdmissibleTargetRow q t.1) :
    let s := sizeTwoCyclicRowRoute q a C routes x t r
    r.1 + s.1 ≠ 0 ∧ r.1 + s.1 ≠ -1 := by
  let s := sizeTwoCyclicRowRoute q a C routes x t r
  have hadj := sizeTwoCyclicRowRoute_spec q a C routes x t r
  constructor
  · intro hc
    have hcount := hcol_hit (sizeTwoCyclicCellAt q a x t) x
    have hbad :
        (sizeTwoCyclicCellAt q a x t).1.1 = x ∨
          (sizeTwoCyclicCellAt q a x t).1.1 = x + 1 := Or.inl (by
            simp [sizeTwoCyclicCellAt_fst])
    rw [if_pos hbad] at hcount
    have hmem : sizeTwoCyclicCellAt q a (x + r.1) s ∈
        (C.neighborFinset (sizeTwoCyclicCellAt q a x t)).filter
          (fun v => v.1.2 = x) := by
      apply Finset.mem_filter.mpr
      refine ⟨by simpa using hadj, ?_⟩
      rw [sizeTwoCyclicCellAt_snd]
      simpa [add_assoc, hc]
    have hpos : 0 < ((C.neighborFinset
        (sizeTwoCyclicCellAt q a x t)).filter
          fun v => v.1.2 = x).card := Finset.card_pos.mpr ⟨_, hmem⟩
    omega
  · intro hc
    have hcount := hcol_hit (sizeTwoCyclicCellAt q a x t) (x - 1)
    have hbad :
        (sizeTwoCyclicCellAt q a x t).1.1 = x - 1 ∨
          (sizeTwoCyclicCellAt q a x t).1.1 = (x - 1) + 1 := Or.inr (by
            simp [sizeTwoCyclicCellAt_fst])
    rw [if_pos hbad] at hcount
    have hmem : sizeTwoCyclicCellAt q a (x + r.1) s ∈
        (C.neighborFinset (sizeTwoCyclicCellAt q a x t)).filter
          (fun v => v.1.2 = x - 1) := by
      apply Finset.mem_filter.mpr
      refine ⟨by simpa using hadj, ?_⟩
      rw [sizeTwoCyclicCellAt_snd]
      calc
        x + r.1 + s.1 = x + (r.1 + s.1) := by simp [add_assoc]
        _ = x + (-1) := by rw [hc]
        _ = x - 1 := by simp [sub_eq_add_neg]
    have hpos : 0 < ((C.neighborFinset
        (sizeTwoCyclicCellAt q a x t)).filter
          fun v => v.1.2 = x - 1).card := Finset.card_pos.mpr ⟨_, hmem⟩
    omega

def sizeTwoCyclicRowRouteTargetColumn
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hcol_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = z).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1)
    (routes : SizeTwoCyclicRoutingConstraints q a C)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (r : SizeTwoAdmissibleTargetRow q t.1) :
    SizeTwoAdmissibleTargetColumn q :=
  ⟨r.1 + (sizeTwoCyclicRowRoute q a C routes x t r).1,
    sizeTwoCyclicRowRoute_targetColumn_admissible
      q a C hcol_hit routes x t r⟩

theorem sizeTwoCyclicRowRoute_spec_as_column
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hcol_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = z).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1)
    (routes : SizeTwoCyclicRoutingConstraints q a C)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (r : SizeTwoAdmissibleTargetRow q t.1) :
    let s := sizeTwoCyclicRowRoute q a C routes x t r
    let c := sizeTwoCyclicRowRouteTargetColumn
      q a C hcol_hit routes x t r
    C.Adj (sizeTwoCyclicCellAt q a x t)
      (sizeTwoCyclicCellAt q a ((x + c.1) - s.1) s) := by
  dsimp only
  have hadj := sizeTwoCyclicRowRoute_spec q a C routes x t r
  convert hadj using 2
  simp [sizeTwoCyclicRowRouteTargetColumn, sub_eq_add_neg, add_assoc]

theorem sizeTwoCyclicRowRouteTargetColumn_injective
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hcol_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = z).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1)
    (routes : SizeTwoCyclicRoutingConstraints q a C)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) :
    Function.Injective
      (sizeTwoCyclicRowRouteTargetColumn q a C hcol_hit routes x t) := by
  intro r₁ r₂ hc
  let s₁ := sizeTwoCyclicRowRoute q a C routes x t r₁
  let s₂ := sizeTwoCyclicRowRoute q a C routes x t r₂
  let c₁ := sizeTwoCyclicRowRouteTargetColumn
    q a C hcol_hit routes x t r₁
  let c₂ := sizeTwoCyclicRowRouteTargetColumn
    q a C hcol_hit routes x t r₂
  have hcval : c₁.1 = c₂.1 := congrArg Subtype.val hc
  have hu := routes.column x t c₁.1 c₁.2
  have ha₁ : C.Adj (sizeTwoCyclicCellAt q a x t)
      (sizeTwoCyclicCellAt q a ((x + c₁.1) - s₁.1) s₁) :=
    sizeTwoCyclicRowRoute_spec_as_column
      q a C hcol_hit routes x t r₁
  have ha₂ : C.Adj (sizeTwoCyclicCellAt q a x t)
      (sizeTwoCyclicCellAt q a ((x + c₁.1) - s₂.1) s₂) := by
    rw [hcval]
    exact sizeTwoCyclicRowRoute_spec_as_column
      q a C hcol_hit routes x t r₂
  have hs : s₁ = s₂ := hu.unique ha₁ ha₂
  apply Subtype.ext
  have hsum : r₁.1 + s₁.1 = r₂.1 + s₂.1 := by
    simpa [c₁, c₂, sizeTwoCyclicRowRouteTargetColumn] using hcval
  rw [hs] at hsum
  exact add_right_cancel hsum

def sizeTwoCyclicColumnRoute
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a))
    (routes : SizeTwoCyclicRoutingConstraints q a C)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (c : SizeTwoAdmissibleTargetColumn q) :
    sizeTwoAllowedDifference q a :=
  Classical.choose (routes.column x t c.1 c.2)

theorem sizeTwoCyclicColumnRoute_spec
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a))
    (routes : SizeTwoCyclicRoutingConstraints q a C)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (c : SizeTwoAdmissibleTargetColumn q) :
    C.Adj (sizeTwoCyclicCellAt q a x t)
      (sizeTwoCyclicCellAt q a
        ((x + c.1) - (sizeTwoCyclicColumnRoute q a C routes x t c).1)
        (sizeTwoCyclicColumnRoute q a C routes x t c)) :=
  (Classical.choose_spec (routes.column x t c.1 c.2)).1

theorem sizeTwoCyclicColumnRoute_sourceRow_admissible
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (y : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = y).card =
        if u.1.2 = y ∨ u.1.2 = y - 1 then 0 else 1)
    (routes : SizeTwoCyclicRoutingConstraints q a C)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (c : SizeTwoAdmissibleTargetColumn q) :
    let s := sizeTwoCyclicColumnRoute q a C routes x t c
    t.1 ≠ c.1 - s.1 ∧ t.1 ≠ (c.1 - s.1) - 1 := by
  let s := sizeTwoCyclicColumnRoute q a C routes x t c
  have hadj := sizeTwoCyclicColumnRoute_spec q a C routes x t c
  constructor
  · intro hr
    have hcount := hrow_hit (sizeTwoCyclicCellAt q a x t) (x + t.1)
    have hbad :
        (sizeTwoCyclicCellAt q a x t).1.2 = x + t.1 ∨
          (sizeTwoCyclicCellAt q a x t).1.2 = (x + t.1) - 1 := Or.inl (by
            simp [sizeTwoCyclicCellAt_snd])
    rw [if_pos hbad] at hcount
    have hmem : sizeTwoCyclicCellAt q a ((x + c.1) - s.1) s ∈
        (C.neighborFinset (sizeTwoCyclicCellAt q a x t)).filter
          (fun v => v.1.1 = x + t.1) := by
      apply Finset.mem_filter.mpr
      refine ⟨by simpa using hadj, ?_⟩
      rw [sizeTwoCyclicCellAt_fst]
      calc
        x + c.1 - s.1 = x + (c.1 - s.1) := by
          simp [sub_eq_add_neg, add_assoc]
        _ = x + t.1 := by rw [← hr]
    have hpos : 0 < ((C.neighborFinset
        (sizeTwoCyclicCellAt q a x t)).filter
          fun v => v.1.1 = x + t.1).card := Finset.card_pos.mpr ⟨_, hmem⟩
    omega
  · intro hr
    have hcount := hrow_hit (sizeTwoCyclicCellAt q a x t) (x + t.1 + 1)
    have hbad :
        (sizeTwoCyclicCellAt q a x t).1.2 = x + t.1 + 1 ∨
          (sizeTwoCyclicCellAt q a x t).1.2 = (x + t.1 + 1) - 1 := Or.inr (by
            simp [sizeTwoCyclicCellAt_snd, sub_eq_add_neg, add_assoc])
    rw [if_pos hbad] at hcount
    have hrow : c.1 - s.1 = t.1 + 1 := by
      have := congrArg (fun z : ZMod q => z + 1) hr
      simpa [sub_eq_add_neg, add_assoc] using this.symm
    have hmem : sizeTwoCyclicCellAt q a ((x + c.1) - s.1) s ∈
        (C.neighborFinset (sizeTwoCyclicCellAt q a x t)).filter
          (fun v => v.1.1 = x + t.1 + 1) := by
      apply Finset.mem_filter.mpr
      refine ⟨by simpa using hadj, ?_⟩
      rw [sizeTwoCyclicCellAt_fst]
      calc
        x + c.1 - s.1 = x + (c.1 - s.1) := by
          simp [sub_eq_add_neg, add_assoc]
        _ = x + t.1 + 1 := by rw [hrow, add_assoc]
    have hpos : 0 < ((C.neighborFinset
        (sizeTwoCyclicCellAt q a x t)).filter
          fun v => v.1.1 = x + t.1 + 1).card := Finset.card_pos.mpr ⟨_, hmem⟩
    omega

def sizeTwoCyclicColumnRouteSourceRow
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (y : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = y).card =
        if u.1.2 = y ∨ u.1.2 = y - 1 then 0 else 1)
    (routes : SizeTwoCyclicRoutingConstraints q a C)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (c : SizeTwoAdmissibleTargetColumn q) :
    SizeTwoAdmissibleTargetRow q t.1 :=
  ⟨c.1 - (sizeTwoCyclicColumnRoute q a C routes x t c).1,
    sizeTwoCyclicColumnRoute_sourceRow_admissible
      q a C hrow_hit routes x t c⟩

theorem sizeTwoCyclicRowRouteTargetColumn_surjective
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (y : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = y).card =
        if u.1.2 = y ∨ u.1.2 = y - 1 then 0 else 1)
    (hcol_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = z).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1)
    (routes : SizeTwoCyclicRoutingConstraints q a C)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) :
    Function.Surjective
      (sizeTwoCyclicRowRouteTargetColumn q a C hcol_hit routes x t) := by
  intro c
  let s := sizeTwoCyclicColumnRoute q a C routes x t c
  let r := sizeTwoCyclicColumnRouteSourceRow
    q a C hrow_hit routes x t c
  refine ⟨r, ?_⟩
  have hcol := sizeTwoCyclicColumnRoute_spec q a C routes x t c
  have hrow : C.Adj (sizeTwoCyclicCellAt q a x t)
      (sizeTwoCyclicCellAt q a (x + r.1) s) := by
    convert hcol using 2
    simp [r, sizeTwoCyclicColumnRouteSourceRow,
      sub_eq_add_neg, add_assoc]
  have hu := routes.row x t r.1 r.2
  have hs : sizeTwoCyclicRowRoute q a C routes x t r = s :=
    hu.unique (sizeTwoCyclicRowRoute_spec q a C routes x t r) hrow
  apply Subtype.ext
  change r.1 + (sizeTwoCyclicRowRoute q a C routes x t r).1 = c.1
  rw [hs]
  simp [r, sizeTwoCyclicColumnRouteSourceRow, s]

def sizeTwoCyclicRoutingEquiv
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (y : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = y).card =
        if u.1.2 = y ∨ u.1.2 = y - 1 then 0 else 1)
    (hcol_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = z).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1)
    (routes : SizeTwoCyclicRoutingConstraints q a C)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) :
    SizeTwoAdmissibleTargetRow q t.1 ≃ SizeTwoAdmissibleTargetColumn q :=
  Equiv.ofBijective
    (sizeTwoCyclicRowRouteTargetColumn q a C hcol_hit routes x t)
    ⟨sizeTwoCyclicRowRouteTargetColumn_injective
        q a C hcol_hit routes x t,
      sizeTwoCyclicRowRouteTargetColumn_surjective
        q a C hrow_hit hcol_hit routes x t⟩

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicRowRoute_targetColumn_admissible
#print axioms Erdos85.sizeTwoCyclicRowRouteTargetColumn_injective
#print axioms Erdos85.sizeTwoCyclicColumnRoute_sourceRow_admissible
#print axioms Erdos85.sizeTwoCyclicRowRouteTargetColumn_surjective
#print axioms Erdos85.sizeTwoCyclicRoutingEquiv
