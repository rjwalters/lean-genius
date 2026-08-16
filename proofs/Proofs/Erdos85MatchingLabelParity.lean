import Proofs.Erdos85OneHighExchangedMissCounting

/-! # Label parity under a free matching involution -/

namespace Erdos85

noncomputable section

def matchingLabelFiber
    {X L : Type*} [Fintype X] [DecidableEq X] [DecidableEq L]
    (label : X → L) (l : L) : Finset X :=
  Finset.univ.filter fun x => label x = l

def nonconstantMatchingLabelFiber
    {X L : Type*} [Fintype X] [DecidableEq X] [DecidableEq L]
    (mate : X → X) (label : X → L) (l : L) : Finset X :=
  Finset.univ.filter fun x => label x = l ∧ label (mate x) ≠ l

def constantMatchingLabelFiber
    {X L : Type*} [Fintype X] [DecidableEq X] [DecidableEq L]
    (mate : X → X) (label : X → L) (l : L) : Finset X :=
  Finset.univ.filter fun x => label x = l ∧ label (mate x) = l

theorem even_card_fintype_of_freeInvolution
    {X : Type*} [Fintype X] (mate : X → X)
    (hinv : Function.Involutive mate) (hfree : ∀ x, mate x ≠ x) :
    Even (Fintype.card X) := by
  classical
  have hsum : (∑ _x ∈ (Finset.univ : Finset X), (1 : ZMod 2)) = 0 := by
    apply Finset.sum_ninvolution mate
    · intro x
      decide
    · intro x _
      exact hfree x
    · intro x
      exact Finset.mem_univ _
    · intro x
      exact hinv x
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hsum
  rwa [ZMod.natCast_eq_zero_iff_even] at hsum

theorem even_card_constantMatchingLabelFiber
    {X L : Type*} [Fintype X] [DecidableEq X] [DecidableEq L]
    (mate : X → X) (label : X → L) (l : L)
    (hinv : Function.Involutive mate) (hfree : ∀ x, mate x ≠ x) :
    Even (constantMatchingLabelFiber mate label l).card := by
  let P := constantMatchingLabelFiber mate label l
  let mateP : {x // x ∈ P} → {x // x ∈ P} := fun x =>
    ⟨mate x.1, by
      have hx := (Finset.mem_filter.mp x.2).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, hx.2, ?_⟩
      rw [hinv x.1]
      exact hx.1⟩
  have hinvP : Function.Involutive mateP := by
    intro x
    apply Subtype.ext
    exact hinv x.1
  have hfreeP : ∀ x, mateP x ≠ x := by
    intro x h
    exact hfree x.1 (congrArg Subtype.val h)
  have heven := even_card_fintype_of_freeInvolution mateP hinvP hfreeP
  simpa [P] using heven

/-- Removing constant-label mate orbits preserves label-fiber parity. -/
theorem even_nonconstantMatchingLabelFiber_of_even
    {X L : Type*} [Fintype X] [DecidableEq X] [DecidableEq L]
    (mate : X → X) (label : X → L) (l : L)
    (hinv : Function.Involutive mate) (hfree : ∀ x, mate x ≠ x)
    (heven : Even (matchingLabelFiber label l).card) :
    Even (nonconstantMatchingLabelFiber mate label l).card := by
  let A := matchingLabelFiber label l
  let C := nonconstantMatchingLabelFiber mate label l
  let P := constantMatchingLabelFiber mate label l
  change Even C.card
  have hdisj : Disjoint C P := by
    apply Finset.disjoint_left.mpr
    intro x hxC hxP
    have hc := (Finset.mem_filter.mp hxC).2.2
    have hp := (Finset.mem_filter.mp hxP).2.2
    exact hc hp
  have hunion : C ∪ P = A := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, C, P, A, matchingLabelFiber,
      nonconstantMatchingLabelFiber, constantMatchingLabelFiber]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact h.1
    · intro hx
      by_cases hm : label (mate x) = l
      · exact Or.inr ⟨hx, hm⟩
      · exact Or.inl ⟨hx, hm⟩
  have hcard : C.card + P.card = A.card := by
    rw [← Finset.card_union_of_disjoint hdisj, hunion]
  have hpEven := even_card_constantMatchingLabelFiber
    mate label l hinv hfree
  change Even A.card at heven
  change Even P.card at hpEven
  rcases heven with ⟨a, ha⟩
  rcases hpEven with ⟨p, hp⟩
  have hpa : p ≤ a := by omega
  refine ⟨a - p, ?_⟩
  omega

end

end Erdos85
