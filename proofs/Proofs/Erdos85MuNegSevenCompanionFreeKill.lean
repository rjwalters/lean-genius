import Proofs.Erdos85BinarySquareAllOddBipartitePartsExclusion
import Proofs.Erdos85SizeTwoEigenlineGridInstantiation

/-!
# The companion-free μ = -(q-1) kill

Editor repair item (2) of squad msg 13926: the old μ=-7 exclusion at
`q = 8` was routed through the seven-component companions, which are
vacuous under regularity.  This replacement is companion-free and
uniform in every `q ≡ 0 (mod 4)`: a `-(q-1)` defect eigenline forces
sign reversal across every defect edge of its component (the defect row
sum `-(q-1)·s` with `q-1` summands of modulus one forces each summand to
be `-s`), so the component is bipartite, contradicting
`binarySquare_regular_no_bipartite_defectComponent`.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- **Companion-free `μ = -(q-1)` exclusion.**  No defect component of a
`q`-regular C4-free graph on `q²` vertices (`4 ∣ q`) carries a `±1` line
with defect row sums `-(q-1)·s`. -/
theorem binarySquare_regular_allOpposite_defectEigenline_false
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q) (hq4 : 4 ∣ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (s : V → ℤ)
    (hs_in : ∀ x ∈ c.supp, s x = -1 ∨ s x = 1)
    (hD : ∀ z ∈ c.supp,
      ∑ y ∈ (secondOrderDefectGraph G).neighborFinset z, s y =
        (1 - (q : ℤ)) * s z) :
    False := by
  classical
  -- Component sizes are uniform multiples of `q`.
  have hm : ∀ c' : (secondOrderDefectGraph G).ConnectedComponent,
      c'.supp.ncard = q * (c'.supp.ncard / q) := by
    intro c'
    obtain ⟨k, hk⟩ := binarySquare_regular_dvd_defectComponent_card
      G hfree hq hreg hcard c'
    rw [hk]
    congr 1
    rw [Nat.mul_div_cancel_left k (by omega : 0 < q)]
  -- Every defect edge inside `c` reverses the sign.
  have hall : ∀ x ∈ c.supp, ∀ y ∈
      (secondOrderDefectGraph G).neighborFinset x, s y = -s x := by
    intro x hx
    have hTcard : ((secondOrderDefectGraph G).neighborFinset x).card =
        q - 1 := by
      have h := defect_degree G hfree hq hreg hcard x
      rwa [SimpleGraph.degree] at h
    have hsum0 : ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x,
        (s y + s x) = 0 := by
      rw [Finset.sum_add_distrib, hD x hx, Finset.sum_const, hTcard,
        nsmul_eq_mul]
      have hcast : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by
        have : 1 ≤ q := by omega
        push_cast [Nat.cast_sub this]
        ring
      rw [hcast]
      ring
    have hmem : ∀ y ∈ (secondOrderDefectGraph G).neighborFinset x,
        y ∈ c.supp := by
      intro y hy
      exact defect_neighbor_mem_supp G c hx
        ((SimpleGraph.mem_neighborFinset _ _ _).mp hy)
    rcases hs_in x hx with hsx | hsx
    · -- `s x = -1`: all summands nonpositive.
      have hnonpos : ∀ y ∈ (secondOrderDefectGraph G).neighborFinset x,
          s y + s x ≤ 0 := by
        intro y hy
        rcases hs_in y (hmem y hy) with h | h <;> rw [h, hsx] <;> norm_num
      intro y hy
      have hzero := (Finset.sum_eq_zero_iff_of_nonpos hnonpos).mp hsum0 y hy
      linarith
    · -- `s x = 1`: all summands nonnegative.
      have hnonneg : ∀ y ∈ (secondOrderDefectGraph G).neighborFinset x,
          0 ≤ s y + s x := by
        intro y hy
        rcases hs_in y (hmem y hy) with h | h <;> rw [h, hsx] <;> norm_num
      intro y hy
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum0 y hy
      linarith
  -- The sign line is a proper two-coloring of the component.
  exact binarySquare_regular_no_bipartite_defectComponent
    G hfree hq hq4 hreg hcard
    (fun c' => c'.supp.ncard / q) hm c
    (fun x => decide (s x = 1))
    (by
      intro x y hx hy hadj hcol
      have hy' : y ∈ (secondOrderDefectGraph G).neighborFinset x :=
        (SimpleGraph.mem_neighborFinset _ _ _).mpr hadj
      have hsy : s y = -s x := hall x hx y hy'
      rcases hs_in x hx with h | h <;>
        rcases hs_in y (defect_neighbor_mem_supp G c hx hadj) with h' | h' <;>
        simp [h, h'] at hcol hsy ⊢)

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_allOpposite_defectEigenline_false
