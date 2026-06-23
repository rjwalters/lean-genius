/-
  Aristotle targets for ShannonChannelCodingOQ02OQ01 (Fano's inequality, Unit case)
  Routine lemmas for automated proof search.
  See ShannonChannelCodingOQ02OQ01.lean for the main formalization.

  The 1 sorry in the main file is in `fano_trivial_singleton`, which proves
  Fano's inequality for the trivial case where |X| = 1 (Unit type).

  Proof strategy for `fano_trivial_singleton`:

  KEY INSIGHT: When α = Unit, all sums collapse to a single term at ().
  This makes:
    1. conditionalEntropy pXY = 0
       ∑_{x:Unit} ∑_y [pXY(x,y)*log(pXY(x,y)/∑_{x':Unit} pXY(x',y))]
       = ∑_y pXY((),y) * log(pXY((),y)/pXY((),y))
       = ∑_y pXY((),y) * log(1)     [since a/a = 1 when a ≠ 0]
       = ∑_y pXY((),y) * 0 = 0
    2. P_e = 1 - ∑_{y:β} pXY((),y)^2/pXY((),y) = 1 - ∑_{y:β} pXY((),y) = 1 - 1 = 0
       (from hsum: ∑ x : Unit×β, pXY x = ∑_y pXY((),y) = 1)
    3. RHS = h(0) + 0 * log(1-1) = 0 + 0 * log(0) = 0 + 0 = 0
       (using: h_zero, Real.log_zero convention, mul_zero)
    4. 0 ≤ 0 by le_refl

  Most tractable targets:
  - `conditional_entropy_unit_zero`: uses Fintype.sum_unique + div_self + log_one
  - `Pe_unit_zero`: uses Finset.sum_product + hsum + div_self
  - `fano_trivial_singleton_ari`: assembles the above two
-/
import Mathlib
import Proofs.ShannonChannelCodingOQ03
import Proofs.ShannonChannelCodingOQ04

open Real Finset FanoInequality InformationTheory.BinaryEntropy

namespace ShannonOQ02OQ01Aristotle

variable {β : Type*} [Fintype β] [DecidableEq β]

/-
TARGET 1 (most tractable)
Unit sums collapse: ∑ x : Unit, f x = f ()

Uses: Fintype.sum_unique or Finset.univ_unique for Unit.
The default element of Unit is Unit.unit = ().
-/
theorem unit_sum_collapse {M : Type*} [AddCommMonoid M] (f : Unit → M) :
    ∑ x : Unit, f x = f () := by
  sorry

/-
TARGET 2
For Unit type, the conditional entropy is 0.

∑ x : Unit, ∑ y : β, (if pXY(x,y)=0 then 0 else pXY(x,y)*log(pXY(x,y)/∑_{x':Unit} pXY(x',y)))
= ∑ y : β, (if pXY((),y)=0 then 0 else pXY((),y)*log(pXY((),y)/pXY((),y)))
= ∑ y : β, (if pXY((),y)=0 then 0 else pXY((),y)*log(1))
= ∑ y : β, (if pXY((),y)=0 then 0 else pXY((),y)*0)
= ∑ y : β, 0 = 0

Strategy:
  simp [conditionalEntropy, unit_sum_collapse, div_self, Real.log_one]
  or use: Fintype.sum_unique, then split_ifs, then div_self, Real.log_one, mul_zero
-/
theorem conditional_entropy_unit_zero (pXY : Unit × β → ℝ) :
    FanoInequality.conditionalEntropy pXY = 0 := by
  sorry

/-
TARGET 3 (most tractable via hsum)
P_e for Unit type equals 0.

P_e = 1 - ∑_{y:β} ∑_{x:Unit} pXY(x,y)^2 / (∑_{x':Unit} pXY(x',y))
    = 1 - ∑_{y:β} pXY((),y)^2 / pXY((),y)   [by unit_sum_collapse]
    = 1 - ∑_{y:β} pXY((),y)                  [since a^2/a = a when a≠0, else 0/0=0]
    = 1 - 1 = 0                                [from hsum]

The key: ∑ x : Unit×β, pXY x = ∑ y : β, ∑ x : Unit, pXY (x,y) = ∑ y : β, pXY ((),y).

Strategy:
  conv_lhs => simp [unit_sum_collapse]
  then show ∑ y, pXY((),y)^2/pXY((),y) = ∑ y, pXY((),y)
  using: if pXY((),y)=0 then 0^2/0=0; else pXY((),y)^2/pXY((),y)=pXY((),y)
  then use hsum to show ∑ y, pXY((),y) = 1
-/
theorem Pe_unit_zero (pXY : Unit × β → ℝ) (hsum : ∑ x, pXY x = 1) :
    1 - ∑ y : β, ∑ x : Unit, pXY (x, y) ^ 2 / (∑ x' : Unit, pXY (x', y)) = 0 := by
  sorry

/-
TARGET 4 (main target, depends on 2 and 3)
Fano's inequality for the trivial singleton case.

Proof:
  have h1 := conditional_entropy_unit_zero pXY  -- LHS = 0
  have h2 := Pe_unit_zero pXY hsum              -- P_e = 0
  rw [conditional_entropy_unit_zero, h2]
  simp [InformationTheory.BinaryEntropy.h_zero, Real.log_zero, mul_zero]

The RHS simplifies to: h(0) + 0*log(0) = 0 + 0*0 = 0
(using: h_zero, Real.log_zero = 0 by Lean convention, mul_zero, add_zero)
Then: 0 ≤ 0 by le_refl.
-/
theorem fano_trivial_singleton_ari (pXY : Unit × β → ℝ)
    (hp : ∀ x, 0 ≤ pXY x) (hsum : ∑ x, pXY x = 1) :
    FanoInequality.conditionalEntropy pXY ≤
      h (1 - ∑ y : β, ∑ x : Unit, pXY (x, y) ^ 2 / (∑ x' : Unit, pXY (x', y))) +
      (1 - ∑ y : β, ∑ x : Unit, pXY (x, y) ^ 2 / (∑ x' : Unit, pXY (x', y))) *
      Real.log ((Fintype.card Unit : ℝ) - 1) := by
  sorry

end ShannonOQ02OQ01Aristotle
