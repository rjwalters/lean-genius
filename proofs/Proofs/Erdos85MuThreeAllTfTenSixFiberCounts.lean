import Proofs.Erdos85MuThreeAllTfTenSixFiberMargin

/-!
# Fiber counts for the `C10 + C6` margin terminal

Two cells of each component color in every row and column imply the total
and strip counts `16/6/6` consumed by the certificate-free contradiction.
-/

namespace Erdos85

def tenSixColorRowFiber (color : Fin 8 → Fin 8 → Fin 3)
    (c : Fin 3) (x : Fin 8) : Finset (Fin 8) :=
  Finset.univ.filter fun y => ¬ tenSixHole x y ∧ color x y = c

def tenSixColorColumnFiber (color : Fin 8 → Fin 8 → Fin 3)
    (c : Fin 3) (y : Fin 8) : Finset (Fin 8) :=
  Finset.univ.filter fun x => ¬ tenSixHole x y ∧ color x y = c

theorem tenSixColorFiber_rowFiber_card
    (color : Fin 8 → Fin 8 → Fin 3) (c : Fin 3) (x : Fin 8) :
    ((tenSixColorFiber color c).filter fun p => p.1 = x).card =
      (tenSixColorRowFiber color c x).card := by
  apply Finset.card_bij (fun p _ => p.2)
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpF := Finset.mem_filter.mp hp'.1
    apply Finset.mem_filter.mpr
    simpa [hp'.2] using hpF.2
  · intro p hp q hq heq
    apply Prod.ext
    · exact (Finset.mem_filter.mp hp).2.trans
        (Finset.mem_filter.mp hq).2.symm
    · exact heq
  · intro y hy
    refine ⟨(x, y), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
        (Finset.mem_filter.mp hy).2⟩
    · rfl

theorem tenSixColorFiber_columnFiber_card
    (color : Fin 8 → Fin 8 → Fin 3) (c : Fin 3) (y : Fin 8) :
    ((tenSixColorFiber color c).filter fun p => p.2 = y).card =
      (tenSixColorColumnFiber color c y).card := by
  apply Finset.card_bij (fun p _ => p.1)
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpF := Finset.mem_filter.mp hp'.1
    apply Finset.mem_filter.mpr
    simpa [hp'.2] using hpF.2
  · intro p hp q hq heq
    apply Prod.ext
    · exact heq
    · exact (Finset.mem_filter.mp hp).2.trans
        (Finset.mem_filter.mp hq).2.symm
  · intro x hx
    refine ⟨(x, y), ?_, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_univ _⟩,
        (Finset.mem_filter.mp hx).2⟩
    · rfl

theorem tenSixColorFiber_card_eq_sixteen_of_rowTwo
    (color : Fin 8 → Fin 8 → Fin 3) (c : Fin 3)
    (hrowTwo : ∀ x : Fin 8, (tenSixColorRowFiber color c x).card = 2) :
    (tenSixColorFiber color c).card = 16 := by
  let F := tenSixColorFiber color c
  have hmaps : ∀ p ∈ F, p.1 ∈ (Finset.univ : Finset (Fin 8)) := by
    intro p _
    exact Finset.mem_univ _
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ x ∈ (Finset.univ : Finset (Fin 8)),
      (F.filter fun p => p.1 = x).card = 2 := by
    intro x _
    rw [show (F.filter fun p => p.1 = x).card =
      (tenSixColorRowFiber color c x).card by
        exact tenSixColorFiber_rowFiber_card color c x]
    exact hrowTwo x
  calc
    (∑ x ∈ (Finset.univ : Finset (Fin 8)),
      (F.filter fun p => p.1 = x).card) =
        ∑ x ∈ (Finset.univ : Finset (Fin 8)), 2 := by
          apply Finset.sum_congr rfl hfib
    _ = 16 := by decide

theorem tenSixSmallRowStrip_card_eq_six_of_rowTwo
    (color : Fin 8 → Fin 8 → Fin 3) (c : Fin 3)
    (hrowTwo : ∀ x : Fin 8, (tenSixColorRowFiber color c x).card = 2) :
    (tenSixSmallRowStrip color c).card = 6 := by
  let S := tenSixSmallRowStrip color c
  let A := (Finset.univ : Finset (Fin 8)).filter fun x => 5 ≤ x.val
  have hmaps : ∀ p ∈ S, p.1 ∈ A := by
    intro p hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
  rw [show S.card = ∑ x ∈ A, (S.filter fun p => p.1 = x).card by
    exact Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ x ∈ A, (S.filter fun p => p.1 = x).card = 2 := by
    intro x hx
    have heq : S.filter (fun p => p.1 = x) =
        (tenSixColorFiber color c).filter fun p => p.1 = x := by
      ext p
      constructor
      · intro hp
        have hp' := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hp'.1).1, hp'.2⟩
      · intro hp
        have hp' := Finset.mem_filter.mp hp
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_filter.mpr ⟨hp'.1, ?_⟩, hp'.2⟩
        simpa [hp'.2] using (Finset.mem_filter.mp hx).2
    rw [heq, tenSixColorFiber_rowFiber_card]
    exact hrowTwo x
  calc
    (∑ x ∈ A, (S.filter fun p => p.1 = x).card) =
        ∑ x ∈ A, 2 := by apply Finset.sum_congr rfl hfib
    _ = 6 := by decide

theorem tenSixSmallColumnStrip_card_eq_six_of_columnTwo
    (color : Fin 8 → Fin 8 → Fin 3) (c : Fin 3)
    (hcolumnTwo : ∀ y : Fin 8,
      (tenSixColorColumnFiber color c y).card = 2) :
    (tenSixSmallColumnStrip color c).card = 6 := by
  let S := tenSixSmallColumnStrip color c
  let A := (Finset.univ : Finset (Fin 8)).filter fun y => 5 ≤ y.val
  have hmaps : ∀ p ∈ S, p.2 ∈ A := by
    intro p hp
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hp).2⟩
  rw [show S.card = ∑ y ∈ A, (S.filter fun p => p.2 = y).card by
    exact Finset.card_eq_sum_card_fiberwise hmaps]
  have hfib : ∀ y ∈ A, (S.filter fun p => p.2 = y).card = 2 := by
    intro y hy
    have heq : S.filter (fun p => p.2 = y) =
        (tenSixColorFiber color c).filter fun p => p.2 = y := by
      ext p
      constructor
      · intro hp
        have hp' := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr
          ⟨(Finset.mem_filter.mp hp'.1).1, hp'.2⟩
      · intro hp
        have hp' := Finset.mem_filter.mp hp
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_filter.mpr ⟨hp'.1, ?_⟩, hp'.2⟩
        simpa [hp'.2] using (Finset.mem_filter.mp hy).2
    rw [heq, tenSixColorFiber_columnFiber_card]
    exact hcolumnTwo y
  calc
    (∑ y ∈ A, (S.filter fun p => p.2 = y).card) =
        ∑ y ∈ A, 2 := by apply Finset.sum_congr rfl hfib
    _ = 6 := by decide

/-- Final abstract all-TF `C10+C6`, `[2,2,2,2]` contradiction: only the
column margins and exact two-per-row/two-per-column color fibers remain. -/
theorem false_of_tenSix_columnMargins_of_twoFibers
    (color : Fin 8 → Fin 8 → Fin 3)
    (hmargin : ∀ c : Fin 3, ∀ h y : Fin 8,
      tenSixHole h y → tenSixColumnMargin color c h y)
    (hrowTwo : ∀ c : Fin 3, ∀ x : Fin 8,
      (tenSixColorRowFiber color c x).card = 2)
    (hcolumnTwo : ∀ c : Fin 3, ∀ y : Fin 8,
      (tenSixColorColumnFiber color c y).card = 2) : False := by
  apply false_of_tenSix_columnMargins_of_fiberStripCounts color hmargin
  · intro c
    exact tenSixColorFiber_card_eq_sixteen_of_rowTwo color c (hrowTwo c)
  · intro c
    exact tenSixSmallRowStrip_card_eq_six_of_rowTwo color c (hrowTwo c)
  · intro c
    exact tenSixSmallColumnStrip_card_eq_six_of_columnTwo color c (hcolumnTwo c)

end Erdos85

#print axioms Erdos85.false_of_tenSix_columnMargins_of_twoFibers
