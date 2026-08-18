import Proofs.Erdos85MuThreeMixedGridForeignRectangleMonodromyTypeCocycle
import Proofs.Erdos85MuThreeMixedGridForeignRectangleMonodromyParityPigeonhole

/-!
# Allowed cycle-type patterns on an even monodromy triangle

Each even derangement of six points has type `(4,2)` or `(3,3)`.  The type
cocycle excludes exactly two `(3,3)` members.  Thus precisely five labelled
patterns remain: all `(4,2)`, one `(3,3)` in any of the three positions, or
all `(3,3)`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The five allowed labelled type patterns for a cocycle pair `σ`, `τ` and
its product `τ * σ`. -/
def sixElementCocycleTypePattern {α : Type*} [Fintype α] [DecidableEq α]
    (σ τ : Equiv.Perm α) : Prop :=
  (σ.cycleType = {2, 4} ∧ τ.cycleType = {2, 4} ∧
    (τ * σ).cycleType = {2, 4}) ∨
  (σ.cycleType = {3, 3} ∧ τ.cycleType = {2, 4} ∧
    (τ * σ).cycleType = {2, 4}) ∨
  (σ.cycleType = {2, 4} ∧ τ.cycleType = {3, 3} ∧
    (τ * σ).cycleType = {2, 4}) ∨
  (σ.cycleType = {2, 4} ∧ τ.cycleType = {2, 4} ∧
    (τ * σ).cycleType = {3, 3}) ∨
  (σ.cycleType = {3, 3} ∧ τ.cycleType = {3, 3} ∧
    (τ * σ).cycleType = {3, 3})

/-- The exhaustive five-pattern list for two even derangements and their
fixed-point-free product on a six-element type. -/
theorem sixElement_even_derangement_cocycle_cycleType_patterns
    {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α = 6)
    (σ τ : Equiv.Perm α)
    (hσfree : ∀ x, σ x ≠ x)
    (hτfree : ∀ x, τ x ≠ x)
    (hprodFree : ∀ x, (τ * σ) x ≠ x)
    (hσeven : σ.sign = 1) (hτeven : τ.sign = 1)
    (hprodeven : (τ * σ).sign = 1) :
    sixElementCocycleTypePattern σ τ := by
  unfold sixElementCocycleTypePattern
  have hσclass := even_fixedPointFree_cycleType_eq_fourTwo_or_threeThree
    hcard σ hσfree hσeven
  have hτclass := even_fixedPointFree_cycleType_eq_fourTwo_or_threeThree
    hcard τ hτfree hτeven
  have hprodclass := even_fixedPointFree_cycleType_eq_fourTwo_or_threeThree
    hcard (τ * σ) hprodFree hprodeven
  have hclose := sixElement_threeThree_cocycle_pairwise_closure
    hcard σ τ hσfree hτfree hprodFree
  rcases hσclass with hσ42 | hσ33 <;>
    rcases hτclass with hτ42 | hτ33 <;>
    rcases hprodclass with hp42 | hp33
  · exact Or.inl ⟨hσ42, hτ42, hp42⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hσ42, hτ42, hp33⟩)))
  · exact Or.inr (Or.inr (Or.inl ⟨hσ42, hτ33, hp42⟩))
  · have hbad : ({2, 4} : Multiset ℕ) = {3, 3} :=
      hσ42.symm.trans (hclose.2.1 ⟨hτ33, hp33⟩)
    have := congrArg (Multiset.count 2) hbad
    norm_num at this
  · exact Or.inr (Or.inl ⟨hσ33, hτ42, hp42⟩)
  · have hbad : ({2, 4} : Multiset ℕ) = {3, 3} :=
      hτ42.symm.trans (hclose.2.2 ⟨hσ33, hp33⟩)
    have := congrArg (Multiset.count 2) hbad
    norm_num at this
  · have hbad : ({2, 4} : Multiset ℕ) = {3, 3} :=
      hp42.symm.trans (hclose.1 ⟨hσ33, hτ33⟩)
    have := congrArg (Multiset.count 2) hbad
    norm_num at this
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hσ33, hτ33, hp33⟩)))

/-- **Unavoidable five-pattern rectangle triangle.**  If the two-regular
`H`-factor is C4-free, some overlap-one column pair has three distinct common
eligible rows whose monodromy cocycle realizes one of the five allowed type
patterns. -/
theorem MuThreeMixedGridCode.exists_even_monodromy_triangle_typePattern_of_c4Free
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (hc4 : ¬ containsC4 (X ⊕ Y) (relationBipartiteGraph H)) :
    ∃ b b' : Y, b ≠ b' ∧
      ∃ a a' a'' : commonForeignRows H b b',
        a ≠ a' ∧ a ≠ a'' ∧ a' ≠ a'' ∧
        sixElementCocycleTypePattern
          (code.foreignRectangleMonodromyEquiv H K C a.1 a'.1 b b'
            a.2.1 a.2.2 a'.2.1 a'.2.2)
          (code.foreignRectangleMonodromyEquiv H K C a'.1 a''.1 b b'
            a'.2.1 a'.2.2 a''.2.1 a''.2.2) := by
  obtain ⟨b, b', hbb', a, a', a'', haa', haa'', ha'a'',
      heven01, heven02, heven12⟩ :=
    code.exists_columns_three_commonRows_pairwise_even_of_c4Free H K C hc4
  let σ : Equiv.Perm {u : muThreeMixedCell K // u.1.2 = b} :=
    code.foreignRectangleMonodromyEquiv H K C a.1 a'.1 b b'
      a.2.1 a.2.2 a'.2.1 a'.2.2
  let τ : Equiv.Perm {u : muThreeMixedCell K // u.1.2 = b} :=
    code.foreignRectangleMonodromyEquiv H K C a'.1 a''.1 b b'
      a'.2.1 a'.2.2 a''.2.1 a''.2.2
  let υ : Equiv.Perm {u : muThreeMixedCell K // u.1.2 = b} :=
    code.foreignRectangleMonodromyEquiv H K C a.1 a''.1 b b'
      a.2.1 a.2.2 a''.2.1 a''.2.2
  have hmul : τ * σ = υ := by
    apply Equiv.ext
    intro u
    exact Equiv.congr_fun
      (code.foreignRectangleMonodromyEquiv_trans H K C
        a.1 a'.1 a''.1 b b' a.2.1 a.2.2 a'.2.1 a'.2.2 a''.2.1 a''.2.2) u
  have hσfree : ∀ x, σ x ≠ x :=
    code.foreignRectangleMonodromyEquiv_ne H K C
      (fun h => haa' (Subtype.ext h)) hbb'
      a.2.1 a.2.2 a'.2.1 a'.2.2
  have hτfree : ∀ x, τ x ≠ x :=
    code.foreignRectangleMonodromyEquiv_ne H K C
      (fun h => ha'a'' (Subtype.ext h)) hbb'
      a'.2.1 a'.2.2 a''.2.1 a''.2.2
  have hυfree : ∀ x, υ x ≠ x :=
    code.foreignRectangleMonodromyEquiv_ne H K C
      (fun h => haa'' (Subtype.ext h)) hbb'
      a.2.1 a.2.2 a''.2.1 a''.2.2
  have hpattern := sixElement_even_derangement_cocycle_cycleType_patterns
    (code.card_occupiedColumnFiber_eq_six H K C b) σ τ hσfree hτfree
    (by simpa [hmul] using hυfree) heven01 heven12 (by simpa [hmul] using heven02)
  exact ⟨b, b', hbb', a, a', a'', haa', haa'', ha'a'', by
    simpa [σ, τ] using hpattern⟩

end


end Erdos85

#print axioms Erdos85.sixElement_even_derangement_cocycle_cycleType_patterns
#print axioms
  Erdos85.MuThreeMixedGridCode.exists_even_monodromy_triangle_typePattern_of_c4Free
