import Proofs.Erdos85OrderSixteenCyclePartition

/-! # Nonlinear primary-degree ledger for order-sixteen cycle partitions

After the three partitions containing a cycle whose order is divisible by
four are removed, the remaining nine cycle partitions have nonlinear defect
fields of degrees only `2`, `3`, `5`, and `6`.  This file records that finite
ledger separately from the forthcoming theorem identifying the actual
Chebyshev factors with these entries.
-/

namespace Erdos85

/-- The distinct nonlinear primary degrees attached to each of the nine
cycle partitions which remain after the divisible-by-four cases are removed.
Multiplicity is deliberately suppressed: the terminal only needs a primary
factor of one of the recorded degrees. -/
def OrderSixteenCyclePrimaryDegreeProfile
    (cycles degrees : List ℕ) : Prop :=
  (cycles = [13, 3] ∧ degrees = [6]) ∨
  (cycles = [11, 5] ∧ degrees = [5, 2]) ∨
  (cycles = [10, 6] ∧ degrees = [2]) ∨
  (cycles = [10, 3, 3] ∧ degrees = [2]) ∨
  (cycles = [9, 7] ∧ degrees = [3, 3]) ∨
  (cycles = [7, 6, 3] ∧ degrees = [3]) ∨
  (cycles = [7, 3, 3, 3] ∧ degrees = [3]) ∨
  (cycles = [6, 5, 5] ∧ degrees = [2]) ∨
  (cycles = [5, 5, 3, 3] ∧ degrees = [2])

/-- Excluding cycle orders divisible by four removes exactly `[16]`,
`[8,8]`, and `[8,5,3]` from the twelve-case census and supplies the explicit
nonlinear-degree profile of every remaining case. -/
theorem exists_orderSixteenCyclePrimaryDegreeProfile
    {cycles : List ℕ} (hcensus : OrderSixteenCyclePartition cycles)
    (hnotFourDvd : ∀ r ∈ cycles, ¬ 4 ∣ r) :
    ∃ degrees, OrderSixteenCyclePrimaryDegreeProfile cycles degrees := by
  rcases hcensus with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  all_goals simp_all [OrderSixteenCyclePrimaryDegreeProfile]

/-- Every nonlinear primary in the surviving order-sixteen ledger has one
of the four degrees already covered by the exact square-sector audits. -/
theorem orderSixteenCyclePrimaryDegreeProfile_mem
    {cycles degrees : List ℕ}
    (hprofile : OrderSixteenCyclePrimaryDegreeProfile cycles degrees) :
    ∀ d ∈ degrees, d = 2 ∨ d = 3 ∨ d = 5 ∨ d = 6 := by
  rcases hprofile with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals simp

/-- In particular, no surviving cycle-primary degree exceeds six. -/
theorem orderSixteenCyclePrimaryDegreeProfile_le_six
    {cycles degrees : List ℕ}
    (hprofile : OrderSixteenCyclePrimaryDegreeProfile cycles degrees)
    {d : ℕ} (hd : d ∈ degrees) :
    d ≤ 6 := by
  rcases orderSixteenCyclePrimaryDegreeProfile_mem hprofile d hd with
    rfl | rfl | rfl | rfl <;> omega

/-- Generic terminal dispatcher: four degree-specific exclusions consume the
entire surviving cycle-primary ledger.  The eventual spectral adapter can
instantiate `Excluded` with the square-primary impossibility predicate. -/
theorem orderSixteenCyclePrimaryDegreeProfile_all
    (Excluded : ℕ → Prop)
    (h2 : Excluded 2) (h3 : Excluded 3)
    (h5 : Excluded 5) (h6 : Excluded 6)
    {cycles degrees : List ℕ}
    (hprofile : OrderSixteenCyclePrimaryDegreeProfile cycles degrees) :
    ∀ d ∈ degrees, Excluded d := by
  intro d hd
  rcases orderSixteenCyclePrimaryDegreeProfile_mem hprofile d hd with
    rfl | rfl | rfl | rfl
  · exact h2
  · exact h3
  · exact h5
  · exact h6

end Erdos85
