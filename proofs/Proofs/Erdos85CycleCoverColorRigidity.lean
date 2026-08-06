import Proofs.Erdos85OddComponentClosure

/-!
# Color rigidity of cyclic quotient covers

Every defect component is monochromatic: all its defect edges are either
original triangle-free edges or all are antipodal nonedges.  A quotient-one
cyclic cover cannot join two components of the first kind.  Indeed two
successive cover edges together with the corresponding two triangle-free
cycle edges are the rim of a `C₄`.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Two triangle-free-colored cycles cannot be joined by a globally oriented
one-neighbour cyclic cover in a `C₄`-free graph. -/
theorem false_of_cycleCover_between_triangleFree_cycles
    {V : Type*} [Fintype V] [DecidableEq V]
    {r n : ℕ} [NeZero r] [NeZero n]
    (hr : 3 ≤ r) (hn : 3 ≤ n)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : ZMod r → V) (v : ZMod n → V)
    (hu : Function.Injective u) (hv : Function.Injective v)
    (hsep : ∀ x y, u x ≠ v y)
    (f : ZMod n → ZMod r)
    (hcover : ∀ x y, G.Adj (u x) (v y) ↔ x = f y)
    (horient : (∀ y, f (y + 1) = f y + 1) ∨
      (∀ y, f (y + 1) = f y - 1))
    (huTri : ∀ x, G.Adj (u x) (u (x + 1)))
    (hvTri : ∀ y, G.Adj (v y) (v (y + 1)))
    (hfree : ¬ containsC4 V G) : False := by
  letI : Fact (1 < r) := ⟨by omega⟩
  letI : Fact (1 < n) := ⟨by omega⟩
  have hcross0 : G.Adj (u (f 0)) (v 0) :=
    (hcover (f 0) 0).mpr rfl
  have hcross1 : G.Adj (u (f (0 + 1))) (v (0 + 1)) :=
    (hcover (f (0 + 1)) (0 + 1)).mpr rfl
  have huf : G.Adj (u (f 0)) (u (f (0 + 1))) := by
    rcases horient with hplus | hminus
    · rw [hplus 0]
      exact huTri (f 0)
    · rw [hminus 0]
      simpa using (huTri (f 0 - 1)).symm
  have hv01 : G.Adj (v 0) (v (0 + 1)) := hvTri 0
  have hfne : f (0 + 1) ≠ f 0 := by
    rcases horient with hplus | hminus
    · rw [hplus 0]
      intro h
      have hone : (1 : ZMod r) = 0 := by linear_combination h
      exact one_ne_zero hone
    · rw [hminus 0]
      intro h
      have hone : (1 : ZMod r) = 0 := by linear_combination -h
      exact one_ne_zero hone
  have hvne : v 0 ≠ v (0 + 1) := by
    intro h
    have heq := hv h
    have hone : (0 : ZMod n) = 1 := by simpa using heq
    exact zero_ne_one hone
  apply hfree
  exact containsC4_of_rim huf hcross1 hv01.symm hcross0.symm
    (hsep (f 0) (0 + 1))
    (hsep (f (0 + 1)) 0)
    (fun h ↦ hfne (hu h))
    (hsep (f (0 + 1)) (0 + 1))
    (hsep (f 0) 0).symm
    hvne

end

end Erdos85
