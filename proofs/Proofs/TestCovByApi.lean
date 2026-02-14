import Mathlib

/-
Test file to explore CovBy/⋖ API and rank function capabilities
-/

variable (α : Type*) [PartialOrder α] [Fintype α]

#check CovBy
#check (· ⋖ · : α → α → Prop)

-- Test: What lemmas exist about CovBy?
#check @CovBy.lt
#check @CovBy.le

-- Test: Can we make a rank function?
-- Count elements strictly below an element
def rankFun (a : α) : ℕ :=
  (Finset.filter (fun x => x < a) Finset.univ).card

-- Test: Is there a height function?
#check Order.height
