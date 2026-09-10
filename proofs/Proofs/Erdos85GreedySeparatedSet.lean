import Mathlib

namespace Erdos85

def listedSeparatedCap {V : Type*} [DecidableEq V]
    (D : List (Finset V)) (X : Finset V) : Bool :=
  D.all fun S => decide ((X ∩ S).card ≤ 1)

/-- Greedily retain vertices while no candidate block contains two retained vertices. -/
def greedySeparatedSet {V : Type*} [DecidableEq V]
    (D : List (Finset V)) : List V → Finset V → Finset V
  | [], X => X
  | x::xs, X =>
    if listedSeparatedCap D (insert x X) then
      greedySeparatedSet D xs (insert x X)
    else greedySeparatedSet D xs X

theorem greedySeparatedSet_cap {V : Type*} [DecidableEq V]
    (D : List (Finset V)) (todo : List V) (X : Finset V)
    (hX : listedSeparatedCap D X = true) :
    listedSeparatedCap D (greedySeparatedSet D todo X) = true := by
  induction todo generalizing X with
  | nil => exact hX
  | cons x xs ih =>
    simp only [greedySeparatedSet]
    split
    · rename_i h
      exact ih _ h
    · exact ih _ hX

theorem greedySeparatedSet_subset {V : Type*} [DecidableEq V]
    (D : List (Finset V)) (todo : List V) (X R : Finset V)
    (hX : X ⊆ R) (htodo : ∀ x ∈ todo, x ∈ R) :
    greedySeparatedSet D todo X ⊆ R := by
  induction todo generalizing X with
  | nil => exact hX
  | cons x xs ih =>
    have hx : x ∈ R := htodo x (by simp)
    have hxs : ∀ y ∈ xs, y ∈ R := fun y hy => htodo y (by simp [hy])
    simp only [greedySeparatedSet]
    split
    · exact ih _ (Finset.insert_subset hx hX) hxs
    · exact ih _ hX hxs

end Erdos85
#print axioms Erdos85.greedySeparatedSet_cap
#print axioms Erdos85.greedySeparatedSet_subset
