import Proofs.Erdos85ThreeSeparatorPositiveSpikeSmallSideLocation

/-!
# Uniform attachment bound for an exceptional separator point

When the exceptional point `c` lies in the three-separator `W`, (B18)
places `c` and every one of its defect neighbors in `K`.  Its `m` neighbors
on `X`, together with `c`, therefore consume `m+1` points of the B16
small-side K-budget.  This gives (B21).
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- The subtraction-safe form of (B21), together with the displayed ledger
form.  The lower bound on `m` is the separator-minimality input. -/
theorem exceptionalPoint_W_attachment_bound
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (X W K : Finset V) (c : V) (a rX m : ℕ)
    (hXW : Disjoint X W)
    (hcW : c ∈ W)
    (hcK : c ∈ K)
    (hneighborsK : D.neighborFinset c ⊆ K)
    (hm : (D.neighborFinset c ∩ X).card = m)
    (hmpos : 1 ≤ m)
    (hsmall : (K ∩ (X ∪ W)).card + rX = 3 * a + 3) :
    1 ≤ m ∧ m + rX ≤ 3 * a + 2 ∧ m ≤ 3 * a + 2 - rX := by
  have hcnotX : c ∉ X := by
    intro hcX
    exact Finset.disjoint_left.mp hXW hcX hcW
  have hcnotNX : c ∉ D.neighborFinset c ∩ X := by
    simp [hcnotX]
  have hcard : (insert c (D.neighborFinset c ∩ X)).card = m + 1 := by
    rw [Finset.card_insert_of_notMem hcnotNX, hm]
  have hsubset : insert c (D.neighborFinset c ∩ X) ⊆ K ∩ (X ∪ W) := by
    intro v hv
    simp only [Finset.mem_insert] at hv
    rcases hv with rfl | hv
    · exact Finset.mem_inter.mpr ⟨hcK, Finset.mem_union_right X hcW⟩
    · have hvN : v ∈ D.neighborFinset c := Finset.mem_inter.mp hv |>.1
      have hvX : v ∈ X := Finset.mem_inter.mp hv |>.2
      exact Finset.mem_inter.mpr
        ⟨hneighborsK hvN, Finset.mem_union_left W hvX⟩
  have hmle : m + 1 ≤ (K ∩ (X ∪ W)).card := by
    rw [← hcard]
    exact Finset.card_le_card hsubset
  constructor
  · exact hmpos
  constructor <;> omega

end

end Erdos85

#print axioms Erdos85.exceptionalPoint_W_attachment_bound
