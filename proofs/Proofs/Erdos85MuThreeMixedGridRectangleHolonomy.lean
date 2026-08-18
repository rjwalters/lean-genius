import Proofs.Erdos85MuThreeMixedGridForeignFiberEquiv

/-!
# C4-free rectangle holonomy

The foreign-fiber equivalences around an `H`-allowed coordinate rectangle
compose to a permutation of one occupied column.  C4-freeness says that this
holonomy has no fixed point: a fixed point would trace four exterior edges
around the rectangle.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem mixedGridForeignFiberEquiv_adj
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (x : X) (y : Y) (hxy : ¬ H x y)
    (u : mixedGridOccupiedColumn K y) :
    C.Adj u.1 (mixedGridForeignFiberEquiv H K C code x y hxy u).1 := by
  rw [mixedGridForeignFiberEquiv_apply]
  exact mixedGridRowRoute_adj H K C code u.1 x (by simpa [u.2] using hxy)

theorem mixedGridForeignFiberEquiv_symm_adj
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (x : X) (y : Y) (hxy : ¬ H x y)
    (v : mixedGridOccupiedRow K x) :
    C.Adj ((mixedGridForeignFiberEquiv H K C code x y hxy).symm v).1 v.1 := by
  have h := mixedGridForeignFiberEquiv_adj H K C code x y hxy
    ((mixedGridForeignFiberEquiv H K C code x y hxy).symm v)
  simpa using h

/-- The four foreign-fiber transports around an allowed rectangle. -/
noncomputable def mixedGridRectangleHolonomy
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (x₁ x₂ : X) (y₁ y₂ : Y)
    (h11 : ¬ H x₁ y₁) (h12 : ¬ H x₁ y₂)
    (h22 : ¬ H x₂ y₂) (h21 : ¬ H x₂ y₁) :
    mixedGridOccupiedColumn K y₁ ≃ mixedGridOccupiedColumn K y₁ :=
  (mixedGridForeignFiberEquiv H K C code x₁ y₁ h11).trans
    ((mixedGridForeignFiberEquiv H K C code x₁ y₂ h12).symm.trans
      ((mixedGridForeignFiberEquiv H K C code x₂ y₂ h22).trans
        (mixedGridForeignFiberEquiv H K C code x₂ y₁ h21).symm))

/-- **Rectangle compatibility law.** A nondegenerate allowed rectangle has
fixed-point-free foreign-fiber holonomy. -/
theorem mixedGridRectangleHolonomy_ne
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (x₁ x₂ : X) (y₁ y₂ : Y) (hx : x₁ ≠ x₂) (hy : y₁ ≠ y₂)
    (h11 : ¬ H x₁ y₁) (h12 : ¬ H x₁ y₂)
    (h22 : ¬ H x₂ y₂) (h21 : ¬ H x₂ y₁)
    (u : mixedGridOccupiedColumn K y₁) :
    mixedGridRectangleHolonomy H K C code x₁ x₂ y₁ y₂
      h11 h12 h22 h21 u ≠ u := by
  let e11 := mixedGridForeignFiberEquiv H K C code x₁ y₁ h11
  let e12 := mixedGridForeignFiberEquiv H K C code x₁ y₂ h12
  let e22 := mixedGridForeignFiberEquiv H K C code x₂ y₂ h22
  let e21 := mixedGridForeignFiberEquiv H K C code x₂ y₁ h21
  let a := e11 u
  let u' := e12.symm a
  let b := e22 u'
  let u'' := e21.symm b
  intro hfix
  have hu'' : u'' = u := by
    simpa [mixedGridRectangleHolonomy, e11, e12, e22, e21,
      a, u', b, u''] using hfix
  have huu' : u.1 ≠ u'.1 := by
    intro heq
    apply hy
    calc
      y₁ = u.1.1.2 := u.2.symm
      _ = u'.1.1.2 := congrArg (fun z : muThreeMixedCell K => z.1.2) heq
      _ = y₂ := u'.2
  have hab : a.1 ≠ b.1 := by
    intro heq
    apply hx
    calc
      x₁ = a.1.1.1 := a.2.symm
      _ = b.1.1.1 := congrArg (fun z : muThreeMixedCell K => z.1.1) heq
      _ = x₂ := b.2
  have hua : C.Adj u.1 a.1 :=
    mixedGridForeignFiberEquiv_adj H K C code x₁ y₁ h11 u
  have hu'a : C.Adj u'.1 a.1 :=
    mixedGridForeignFiberEquiv_symm_adj H K C code x₁ y₂ h12 a
  have hu'b : C.Adj u'.1 b.1 :=
    mixedGridForeignFiberEquiv_adj H K C code x₂ y₂ h22 u'
  have hu''b : C.Adj u''.1 b.1 :=
    mixedGridForeignFiberEquiv_symm_adj H K C code x₂ y₁ h21 b
  have hub : C.Adj u.1 b.1 := by simpa [hu''] using hu''b
  have ha : a.1 ∈ C.neighborFinset u.1 ∩ C.neighborFinset u'.1 := by
    exact Finset.mem_inter.mpr ⟨(C.mem_neighborFinset _ _).mpr hua,
      (C.mem_neighborFinset _ _).mpr hu'a⟩
  have hb : b.1 ∈ C.neighborFinset u.1 ∩ C.neighborFinset u'.1 := by
    exact Finset.mem_inter.mpr ⟨(C.mem_neighborFinset _ _).mpr hub,
      (C.mem_neighborFinset _ _).mpr hu'b⟩
  have hle := code.common_neighbor_card_le_one H K C u.1 u'.1 huu'
  exact hab (Finset.card_le_one.mp hle a.1 ha b.1 hb)

end

end Erdos85

#print axioms Erdos85.mixedGridRectangleHolonomy_ne
