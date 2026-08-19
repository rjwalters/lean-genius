import Proofs.Erdos85SizeTwoMuNegFiveEightEightAllTriangleCases

/-! # Shore switching from the `mu=-5` to the `mu=3` C8+C8 branch -/

open Finset

namespace Erdos85

noncomputable section

/-- For a `{±1}`-valued row, its signed sum is determined by the row size
and the number of entries having the same sign as the base point. -/
theorem signed_sum_eq_two_same_sub_card
    {X : Type*} [DecidableEq X]
    (F : Finset X) (s : X → ℤ) (x : X)
    (hx : s x = -1 ∨ s x = 1)
    (hF : ∀ y ∈ F, s y = -1 ∨ s y = 1) :
    ∑ y ∈ F, s y =
      (2 * ((F.filter fun y ↦ s y = s x).card : ℤ) - (F.card : ℤ)) * s x := by
  classical
  let P : X → Prop := fun y ↦ s y = s x
  have hsame : ∑ y ∈ F.filter P, s y =
      ((F.filter P).card : ℤ) * s x := by
    calc
      ∑ y ∈ F.filter P, s y = ∑ _y ∈ F.filter P, s x := by
        apply Finset.sum_congr rfl
        intro y hy
        exact (Finset.mem_filter.mp hy).2
      _ = ((F.filter P).card : ℤ) * s x := by simp
  have hopp : ∑ y ∈ F.filter (fun y ↦ ¬ P y), s y =
      -((F.filter (fun y ↦ ¬ P y)).card : ℤ) * s x := by
    calc
      ∑ y ∈ F.filter (fun y ↦ ¬ P y), s y =
          ∑ _y ∈ F.filter (fun y ↦ ¬ P y), -s x := by
        apply Finset.sum_congr rfl
        intro y hy
        have hyF := (Finset.mem_filter.mp hy).1
        have hyne := (Finset.mem_filter.mp hy).2
        rcases hx with hx | hx <;> rcases hF y hyF with hsy | hsy
        all_goals simp only [P] at hyne
        all_goals omega
      _ = -((F.filter (fun y ↦ ¬ P y)).card : ℤ) * s x := by simp
  have hcard := Finset.card_filter_add_card_filter_not (s := F) P
  rw [← Finset.sum_filter_add_sum_filter_not F P, hsame]
  change _ + (∑ y ∈ F.filter (fun y ↦ ¬ P y), s y) = _
  rw [hopp]
  rw [show F.filter (fun y ↦ s y = s x) = F.filter P by rfl]
  ring_nf
  have hcardZ : ((F.filter P).card : ℤ) +
      ((F.filter (fun y ↦ ¬ P y)).card : ℤ) = (F.card : ℤ) := by
    exact_mod_cast hcard
  rw [← hcardZ]
  ring

/-- Negating a signed vector on one shore subtracts the cross-block
coefficient from the diagonal-block coefficient. -/
theorem bipartition_signSwitch_eigen_sub
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : SimpleGraph X) [DecidableRel D.Adj]
    (A B : Finset X) (hAB : Disjoint A B)
    (hcover : ∀ x, D.neighborFinset x ⊆ A ∪ B)
    (s : X → ℤ) (p q : ℤ)
    (hAA : ∀ x ∈ A,
      ∑ y ∈ (D.neighborFinset x).filter (· ∈ A), s y = p * s x)
    (hABsum : ∀ x ∈ A,
      ∑ y ∈ (D.neighborFinset x).filter (· ∈ B), s y = q * s x)
    (hBB : ∀ x ∈ B,
      ∑ y ∈ (D.neighborFinset x).filter (· ∈ B), s y = p * s x)
    (hBAsum : ∀ x ∈ B,
      ∑ y ∈ (D.neighborFinset x).filter (· ∈ A), s y = q * s x) :
    let t : X → ℤ := fun x ↦ if x ∈ B then -s x else s x
    ∀ x ∈ A ∪ B, ∑ y ∈ D.neighborFinset x, t y = (p - q) * t x := by
  classical
  dsimp only
  intro x hx
  have hsplit : D.neighborFinset x =
      (D.neighborFinset x).filter (· ∈ A) ∪
        (D.neighborFinset x).filter (· ∈ B) := by
    ext y
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hy
      have hyAB := hcover x hy
      rcases Finset.mem_union.mp hyAB with hyA | hyB
      · exact Or.inl ⟨hy, hyA⟩
      · exact Or.inr ⟨hy, hyB⟩
    · rintro (⟨hy, _⟩ | ⟨hy, _⟩) <;> exact hy
  have hfilters : Disjoint
      ((D.neighborFinset x).filter (· ∈ A))
      ((D.neighborFinset x).filter (· ∈ B)) := by
    rw [Finset.disjoint_left]
    intro y hyA hyB
    exact (Finset.disjoint_left.mp hAB)
      (Finset.mem_filter.mp hyA).2 (Finset.mem_filter.mp hyB).2
  rcases Finset.mem_union.mp hx with hxA | hxB
  · have hxnotB : x ∉ B := by
      intro hxB
      exact Finset.disjoint_left.mp hAB hxA hxB
    rw [hsplit, Finset.sum_union hfilters]
    have hsumA : ∑ y ∈ (D.neighborFinset x).filter (· ∈ A),
        (if y ∈ B then -s y else s y) =
        ∑ y ∈ (D.neighborFinset x).filter (· ∈ A), s y := by
      apply Finset.sum_congr rfl
      intro y hy
      have hyA := (Finset.mem_filter.mp hy).2
      have hynotB : y ∉ B := by
        intro hyB
        exact Finset.disjoint_left.mp hAB hyA hyB
      simp [hynotB]
    have hsumB : ∑ y ∈ (D.neighborFinset x).filter (· ∈ B),
        (if y ∈ B then -s y else s y) =
        -∑ y ∈ (D.neighborFinset x).filter (· ∈ B), s y := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro y hy
      simp [(Finset.mem_filter.mp hy).2]
    rw [hsumA, hsumB, hAA x hxA, hABsum x hxA]
    simp [hxnotB]
    ring

  · rw [hsplit, Finset.sum_union hfilters]
    have hsumA : ∑ y ∈ (D.neighborFinset x).filter (· ∈ A),
        (if y ∈ B then -s y else s y) =
        ∑ y ∈ (D.neighborFinset x).filter (· ∈ A), s y := by
      apply Finset.sum_congr rfl
      intro y hy
      have hyA := (Finset.mem_filter.mp hy).2
      have hynotB : y ∉ B := by
        intro hyB
        exact Finset.disjoint_left.mp hAB hyA hyB
      simp [hynotB]
    have hsumB : ∑ y ∈ (D.neighborFinset x).filter (· ∈ B),
        (if y ∈ B then -s y else s y) =
        -∑ y ∈ (D.neighborFinset x).filter (· ∈ B), s y := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro y hy
      simp [(Finset.mem_filter.mp hy).2]
    rw [hsumA, hsumB, hBAsum x hxB, hBB x hxB]
    simp [hxB]
    ring

/-- The `mu=-5`, `(k,r)=(1,4)` specialization: block sums `(-1,-4)`
switch to eigenvalue three. -/
theorem bipartition_signSwitch_eigen_three
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : SimpleGraph X) [DecidableRel D.Adj]
    (A B : Finset X) (hAB : Disjoint A B)
    (hcover : ∀ x, D.neighborFinset x ⊆ A ∪ B)
    (s : X → ℤ)
    (hAA : ∀ x ∈ A,
      ∑ y ∈ (D.neighborFinset x).filter (· ∈ A), s y = -s x)
    (hABsum : ∀ x ∈ A,
      ∑ y ∈ (D.neighborFinset x).filter (· ∈ B), s y = -4 * s x)
    (hBB : ∀ x ∈ B,
      ∑ y ∈ (D.neighborFinset x).filter (· ∈ B), s y = -s x)
    (hBAsum : ∀ x ∈ B,
      ∑ y ∈ (D.neighborFinset x).filter (· ∈ A), s y = -4 * s x) :
    let t : X → ℤ := fun x ↦ if x ∈ B then -s x else s x
    ∀ x ∈ A ∪ B, ∑ y ∈ D.neighborFinset x, t y = 3 * t x := by
  simpa using
    bipartition_signSwitch_eigen_sub D A B hAB hcover s (-1) (-4)
      (by simpa using hAA) (by simpa using hABsum)
      (by simpa using hBB) (by simpa using hBAsum)

/-- Cardinality-level form of the `(k,r)=(1,4)` switch.  Each diagonal
block row has size three with one same-sign entry, while each cross-block
row has size four with no same-sign entry. -/
theorem bipartition_signSwitch_eigen_three_of_card
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : SimpleGraph X) [DecidableRel D.Adj]
    (A B : Finset X) (hAB : Disjoint A B)
    (hcover : ∀ x, D.neighborFinset x ⊆ A ∪ B)
    (s : X → ℤ)
    (hsign : ∀ x ∈ A ∪ B, s x = -1 ∨ s x = 1)
    (hAAcard : ∀ x ∈ A,
      ((D.neighborFinset x).filter (· ∈ A)).card = 3)
    (hAAsame : ∀ x ∈ A,
      (((D.neighborFinset x).filter (· ∈ A)).filter
        (fun y ↦ s y = s x)).card = 1)
    (hABcard : ∀ x ∈ A,
      ((D.neighborFinset x).filter (· ∈ B)).card = 4)
    (hABsame : ∀ x ∈ A,
      (((D.neighborFinset x).filter (· ∈ B)).filter
        (fun y ↦ s y = s x)).card = 0)
    (hBBcard : ∀ x ∈ B,
      ((D.neighborFinset x).filter (· ∈ B)).card = 3)
    (hBBsame : ∀ x ∈ B,
      (((D.neighborFinset x).filter (· ∈ B)).filter
        (fun y ↦ s y = s x)).card = 1)
    (hBAcard : ∀ x ∈ B,
      ((D.neighborFinset x).filter (· ∈ A)).card = 4)
    (hBAsame : ∀ x ∈ B,
      (((D.neighborFinset x).filter (· ∈ A)).filter
        (fun y ↦ s y = s x)).card = 0) :
    let t : X → ℤ := fun x ↦ if x ∈ B then -s x else s x
    ∀ x ∈ A ∪ B, ∑ y ∈ D.neighborFinset x, t y = 3 * t x := by
  apply bipartition_signSwitch_eigen_three D A B hAB hcover s
  · intro x hx
    rw [signed_sum_eq_two_same_sub_card _ s x
      (hsign x (Finset.mem_union_left B hx))]
    · rw [hAAcard x hx, hAAsame x hx]
      norm_num
    · intro y hy
      exact hsign y (Finset.mem_union_left B (Finset.mem_filter.mp hy).2)

  · intro x hx
    rw [signed_sum_eq_two_same_sub_card _ s x
      (hsign x (Finset.mem_union_left B hx))]
    · rw [hABcard x hx, hABsame x hx]
      norm_num
    · intro y hy
      exact hsign y (Finset.mem_union_right A (Finset.mem_filter.mp hy).2)
  · intro x hx
    rw [signed_sum_eq_two_same_sub_card _ s x
      (hsign x (Finset.mem_union_right A hx))]
    · rw [hBBcard x hx, hBBsame x hx]
      norm_num
    · intro y hy
      exact hsign y (Finset.mem_union_right A (Finset.mem_filter.mp hy).2)
  · intro x hx
    rw [signed_sum_eq_two_same_sub_card _ s x
      (hsign x (Finset.mem_union_right A hx))]
    · rw [hBAcard x hx, hBAsame x hx]
      norm_num
    · intro y hy
      exact hsign y (Finset.mem_union_left B (Finset.mem_filter.mp hy).2)

/-- Matrix form of the exact cardinality switch when the two shores partition
the whole vertex type.  This is the socket consumed by component extension. -/
theorem bipartition_signSwitch_adjMatrix_eigen_three_of_card
    {X : Type*} [Fintype X] [DecidableEq X]
    (D : SimpleGraph X) [DecidableRel D.Adj]
    (A B : Finset X) (hAB : Disjoint A B)
    (hpartition : A ∪ B = Finset.univ)
    (s : X → ℤ)
    (hsign : ∀ x, s x = -1 ∨ s x = 1)
    (hAAcard : ∀ x ∈ A,
      ((D.neighborFinset x).filter (· ∈ A)).card = 3)
    (hAAsame : ∀ x ∈ A,
      (((D.neighborFinset x).filter (· ∈ A)).filter
        (fun y ↦ s y = s x)).card = 1)
    (hABcard : ∀ x ∈ A,
      ((D.neighborFinset x).filter (· ∈ B)).card = 4)
    (hABsame : ∀ x ∈ A,
      (((D.neighborFinset x).filter (· ∈ B)).filter
        (fun y ↦ s y = s x)).card = 0)
    (hBBcard : ∀ x ∈ B,
      ((D.neighborFinset x).filter (· ∈ B)).card = 3)
    (hBBsame : ∀ x ∈ B,
      (((D.neighborFinset x).filter (· ∈ B)).filter
        (fun y ↦ s y = s x)).card = 1)
    (hBAcard : ∀ x ∈ B,
      ((D.neighborFinset x).filter (· ∈ A)).card = 4)
    (hBAsame : ∀ x ∈ B,
      (((D.neighborFinset x).filter (· ∈ A)).filter
        (fun y ↦ s y = s x)).card = 0) :
    let t : X → ℤ := fun x ↦ if x ∈ B then -s x else s x
    (D.adjMatrix ℤ).mulVec t = 3 • t := by
  classical
  dsimp only
  have hrows := bipartition_signSwitch_eigen_three_of_card D A B hAB
    (fun _x y _hy ↦ by rw [hpartition]; exact Finset.mem_univ y)
    s (fun x _hx ↦ hsign x) hAAcard hAAsame hABcard hABsame
      hBBcard hBBsame hBAcard hBAsame
  funext x
  rw [D.adjMatrix_mulVec_apply]
  simpa [hpartition] using hrows x (by rw [hpartition]; exact Finset.mem_univ x)

/-- Component-row form of the exact `mu=-5` shore switch.  It accepts the
`componentNeighborFinset` cardinalities produced by quotient arguments. -/
theorem twoComponent_signSwitch_adjMatrix_eigen_three
    {X : Type*} [Fintype X] [DecidableEq X]
    (D H : SimpleGraph X) [DecidableRel D.Adj] [DecidableRel H.Adj]
    [DecidableEq H.ConnectedComponent]
    (a b : H.ConnectedComponent) (hab : a ≠ b)
    (hpartition : ∀ x, x ∈ a.supp ∨ x ∈ b.supp)
    (s : X → ℤ) (hsign : ∀ x, s x = -1 ∨ s x = 1)
    (hAAcard : ∀ x, x ∈ a.supp →
      (componentNeighborFinset D H a x).card = 3)
    (hAAsame : ∀ x, x ∈ a.supp →
      ((componentNeighborFinset D H a x).filter
        (fun y ↦ s y = s x)).card = 1)
    (hABcard : ∀ x, x ∈ a.supp →
      (componentNeighborFinset D H b x).card = 4)
    (hABsame : ∀ x, x ∈ a.supp →
      ((componentNeighborFinset D H b x).filter
        (fun y ↦ s y = s x)).card = 0)
    (hBBcard : ∀ x, x ∈ b.supp →
      (componentNeighborFinset D H b x).card = 3)
    (hBBsame : ∀ x, x ∈ b.supp →
      ((componentNeighborFinset D H b x).filter
        (fun y ↦ s y = s x)).card = 1)
    (hBAcard : ∀ x, x ∈ b.supp →
      (componentNeighborFinset D H a x).card = 4)
    (hBAsame : ∀ x, x ∈ b.supp →
      ((componentNeighborFinset D H a x).filter
        (fun y ↦ s y = s x)).card = 0) :
    let B := (Finset.univ : Finset X).filter
      (fun x ↦ H.connectedComponentMk x = b)
    let t : X → ℤ := fun x ↦ if x ∈ B then -s x else s x
    (D.adjMatrix ℤ).mulVec t = 3 • t := by
  classical
  dsimp only
  let A := (Finset.univ : Finset X).filter
    (fun x ↦ H.connectedComponentMk x = a)
  let B := (Finset.univ : Finset X).filter
    (fun x ↦ H.connectedComponentMk x = b)
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    have hxa := (Finset.mem_filter.mp hxA).2
    have hxb := (Finset.mem_filter.mp hxB).2
    exact hab (hxa.symm.trans hxb)
  have hpart : A ∪ B = Finset.univ := by
    ext x
    simp only [A, B, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and, iff_true]
    rcases hpartition x with hxa | hxb
    · exact Or.inl ((SimpleGraph.ConnectedComponent.mem_supp_iff a x).mp hxa)
    · exact Or.inr ((SimpleGraph.ConnectedComponent.mem_supp_iff b x).mp hxb)
  have hrow (d : H.ConnectedComponent) (x : X) :
      (D.neighborFinset x).filter (fun y ↦ y ∈
        (Finset.univ : Finset X).filter
          (fun z ↦ H.connectedComponentMk z = d)) =
      componentNeighborFinset D H d x := by
    ext y
    simp [componentNeighborFinset, SimpleGraph.mem_neighborFinset]
  apply bipartition_signSwitch_adjMatrix_eigen_three_of_card D A B hAB hpart s hsign
  · intro x hx
    rw [hrow a x]
    exact hAAcard x ((SimpleGraph.ConnectedComponent.mem_supp_iff a x).mpr
      (Finset.mem_filter.mp hx).2)
  · intro x hx
    rw [hrow a x]
    exact hAAsame x ((SimpleGraph.ConnectedComponent.mem_supp_iff a x).mpr
      (Finset.mem_filter.mp hx).2)
  · intro x hx
    rw [hrow b x]
    exact hABcard x ((SimpleGraph.ConnectedComponent.mem_supp_iff a x).mpr
      (Finset.mem_filter.mp hx).2)
  · intro x hx
    rw [hrow b x]
    exact hABsame x ((SimpleGraph.ConnectedComponent.mem_supp_iff a x).mpr
      (Finset.mem_filter.mp hx).2)
  · intro x hx
    rw [hrow b x]
    exact hBBcard x ((SimpleGraph.ConnectedComponent.mem_supp_iff b x).mpr
      (Finset.mem_filter.mp hx).2)
  · intro x hx
    rw [hrow b x]
    exact hBBsame x ((SimpleGraph.ConnectedComponent.mem_supp_iff b x).mpr
      (Finset.mem_filter.mp hx).2)
  · intro x hx
    rw [hrow a x]
    exact hBAcard x ((SimpleGraph.ConnectedComponent.mem_supp_iff b x).mpr
      (Finset.mem_filter.mp hx).2)
  · intro x hx
    rw [hrow a x]
    exact hBAsame x ((SimpleGraph.ConnectedComponent.mem_supp_iff b x).mpr
      (Finset.mem_filter.mp hx).2)

/-- Quotient-level form of the `(k,r)=(1,4)` switch.  The four quotient
entries supply the total block degrees, while the signed ledger supplies
same-sign degrees one on the diagonal and zero across. -/
theorem twoComponent_quotient_signSwitch_adjMatrix_eigen_three
    {X : Type*} [Fintype X] [DecidableEq X]
    (D H : SimpleGraph X) [DecidableRel D.Adj] [DecidableRel H.Adj]
    [DecidableEq H.ConnectedComponent]
    (a b : H.ConnectedComponent) (hab : a ≠ b)
    (hdegree : ∀ x, H.degree x = 2)
    (hcomm : D.adjMatrix ℝ * H.adjMatrix ℝ =
      H.adjMatrix ℝ * D.adjMatrix ℝ)
    (hpartition : ∀ x, x ∈ a.supp ∨ x ∈ b.supp)
    (s : X → ℤ) (hsign : ∀ x, s x = -1 ∨ s x = 1)
    (haa : componentQuotientMatrix D H a a = 3)
    (habq : componentQuotientMatrix D H a b = 4)
    (hbaq : componentQuotientMatrix D H b a = 4)
    (hbb : componentQuotientMatrix D H b b = 3)
    (hAAsame : ∀ x, x ∈ a.supp →
      ((componentNeighborFinset D H a x).filter
        (fun y ↦ s y = s x)).card = 1)
    (hABsame : ∀ x, x ∈ a.supp →
      ((componentNeighborFinset D H b x).filter
        (fun y ↦ s y = s x)).card = 0)
    (hBBsame : ∀ x, x ∈ b.supp →
      ((componentNeighborFinset D H b x).filter
        (fun y ↦ s y = s x)).card = 1)
    (hBAsame : ∀ x, x ∈ b.supp →
      ((componentNeighborFinset D H a x).filter
        (fun y ↦ s y = s x)).card = 0) :
    let B := (Finset.univ : Finset X).filter
      (fun x ↦ H.connectedComponentMk x = b)
    let t : X → ℤ := fun x ↦ if x ∈ B then -s x else s x
    (D.adjMatrix ℤ).mulVec t = 3 • t := by
  apply twoComponent_signSwitch_adjMatrix_eigen_three D H a b hab hpartition
    s hsign
  · intro x hx
    rw [← componentQuotientMatrix_apply_eq D H 2 hdegree hcomm a a hx]
    exact haa
  · exact hAAsame
  · intro x hx
    rw [← componentQuotientMatrix_apply_eq D H 2 hdegree hcomm a b hx]
    exact habq
  · exact hABsame
  · intro x hx
    rw [← componentQuotientMatrix_apply_eq D H 2 hdegree hcomm b b hx]
    exact hbb
  · exact hBBsame
  · intro x hx
    rw [← componentQuotientMatrix_apply_eq D H 2 hdegree hcomm b a hx]
    exact hbaq
  · exact hBAsame

end

end Erdos85

#print axioms Erdos85.bipartition_signSwitch_eigen_three
#print axioms Erdos85.bipartition_signSwitch_eigen_sub
#print axioms Erdos85.signed_sum_eq_two_same_sub_card
#print axioms Erdos85.bipartition_signSwitch_eigen_three_of_card
#print axioms Erdos85.bipartition_signSwitch_adjMatrix_eigen_three_of_card
#print axioms Erdos85.twoComponent_signSwitch_adjMatrix_eigen_three
#print axioms Erdos85.twoComponent_quotient_signSwitch_adjMatrix_eigen_three
