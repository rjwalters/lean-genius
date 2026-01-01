import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic

/-!
# Burnside's Lemma and Counting Applications

## What This Proves

We demonstrate applications of Burnside's lemma (also known as the Cauchy-Frobenius lemma
or the orbit-counting theorem) to classic combinatorial counting problems.

**Burnside's Lemma**: For a finite group G acting on a finite set X, the number of
orbits equals the average number of fixed points:
  |X/G| = (1/|G|) * Σ_{g ∈ G} |Fix(g)|

Or equivalently (avoiding division):
  Σ_{g ∈ G} |Fix(g)| = |X/G| * |G|

## Applications

1. **Necklace Counting**: Count distinct necklaces with n beads and k colors
   under cyclic rotation.

2. **Binary Necklaces**: Special case k=2 with explicit computations.

## Approach

- **Foundation**: We use `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`
  from Mathlib, which is Burnside's lemma.
- **Original Contributions**: Concrete applications to necklace counting with
  verified examples.

## Status
- [x] Burnside's lemma statement (from Mathlib)
- [x] Cyclic group action on colorings
- [x] Binary necklace counting for n=4
- [x] Verified computation: 6 distinct binary 4-necklaces

## Mathlib Dependencies
- `Mathlib.GroupTheory.GroupAction.Quotient` : Burnside's lemma
- `Mathlib.GroupTheory.SpecificGroups.Cyclic` : Cyclic groups
- `Mathlib.Data.ZMod.Basic` : Z/nZ arithmetic
-/

namespace BurnsideCounting

open Finset MulAction

/-! ## Part I: Burnside's Lemma from Mathlib -/

/-- Burnside's lemma: the sum of fixed point counts equals orbits times group size.
    This is the multiplicative form avoiding division. -/
theorem burnside_lemma {G : Type*} {X : Type*} [Group G] [MulAction G X]
    [Fintype G] [(g : G) → Fintype (fixedBy X g)] [Fintype (orbitRel.Quotient G X)] :
    ∑ g : G, Fintype.card (fixedBy X g) =
      Fintype.card (orbitRel.Quotient G X) * Fintype.card G :=
  MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X

/-! ## Part II: Colorings and Cyclic Actions

A coloring of n positions with k colors is a function Fin n → Fin k.
The cyclic group Z_n acts on colorings by rotation. -/

/-- A coloring of n positions with k colors. -/
abbrev Coloring (n k : ℕ) := Fin n → Fin k

/-- The cyclic group Z_n represented as ZMod n. -/
abbrev CyclicGroup (n : ℕ) := ZMod n

/-- Rotate a coloring by r positions: (rotate r c) i = c (i - r).
    This defines the cyclic group action on colorings. -/
def rotateColoring {n k : ℕ} (r : ZMod n) (c : Coloring n k) : Coloring n k :=
  fun i => c (i - r)

/-- The rotation action is a group action. -/
instance cyclicActionOnColorings (n k : ℕ) [NeZero n] :
    MulAction (ZMod n) (Coloring n k) where
  smul := rotateColoring
  one_smul := fun c => by
    ext i
    simp only [rotateColoring, sub_zero]
  mul_smul := fun r s c => by
    ext i
    simp only [rotateColoring]
    ring_nf

/-! ## Part III: Fixed Points Under Rotation

A coloring c is fixed by rotation r iff c(i) = c(i - r) for all i.
This means c has period dividing gcd(r, n). -/

/-- A coloring is fixed by rotation r iff it's periodic with period dividing r. -/
theorem fixed_iff_periodic {n k : ℕ} [NeZero n] (r : ZMod n) (c : Coloring n k) :
    r • c = c ↔ ∀ i, c i = c (i - r) := by
  constructor
  · intro h i
    have : (r • c) i = c i := congr_fun h i
    simp only [rotateColoring] at this
    exact this.symm
  · intro h
    ext i
    simp only [rotateColoring]
    exact (h i).symm

/-! ## Part IV: Binary Necklaces of Length 4

We compute the number of distinct binary necklaces of length 4.
By Burnside's lemma:
  |orbits| = (|Fix(0)| + |Fix(1)| + |Fix(2)| + |Fix(3)|) / 4

Where:
- Fix(0) = 16 (identity fixes all 2^4 colorings)
- Fix(1) = 2 (only constant colorings: 0000, 1111)
- Fix(2) = 4 (period divides 2: 0000, 0101, 1010, 1111)
- Fix(3) = 2 (only constant colorings: 0000, 1111)

Total = (16 + 2 + 4 + 2) / 4 = 24 / 4 = 6 -/

/-- Total number of binary colorings of length 4. -/
theorem binary_colorings_4 : Fintype.card (Coloring 4 2) = 16 := by
  simp only [Fintype.card_fun, Fintype.card_fin]

/-- Fixed points of identity rotation (all colorings). -/
theorem fixed_by_zero_4 : Fintype.card (fixedBy (Coloring 4 2) (0 : ZMod 4)) = 16 := by
  have h : fixedBy (Coloring 4 2) (0 : ZMod 4) = Set.univ := by
    ext c
    simp only [fixedBy, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    ext i
    simp only [rotateColoring, sub_zero]
  simp only [h]
  rw [Set.toFinset_univ, Finset.card_univ]
  simp only [Fintype.card_fun, Fintype.card_fin]

/-- A coloring has period 1 (constant) iff fixed by rotation 1. -/
def isConstant {n k : ℕ} (c : Coloring n k) : Prop :=
  ∀ i j, c i = c j

/-- Count of constant colorings. -/
theorem constant_colorings_count (n k : ℕ) [NeZero n] [NeZero k] :
    Fintype.card { c : Coloring n k // isConstant c } = k := by
  -- Each constant coloring is determined by the single color value
  have : { c : Coloring n k // isConstant c } ≃ Fin k := {
    toFun := fun ⟨c, _⟩ => c 0
    invFun := fun v => ⟨fun _ => v, fun _ _ => rfl⟩
    left_inv := fun ⟨c, hc⟩ => by
      simp only
      ext i
      exact hc 0 i
    right_inv := fun v => rfl
  }
  rw [Fintype.card_congr this, Fintype.card_fin]

/-- For n=4, k=2: exactly 2 constant colorings. -/
theorem constant_colorings_4_2 :
    Fintype.card { c : Coloring 4 2 // isConstant c } = 2 :=
  constant_colorings_count 4 2

/-! ## Part V: Period-2 Colorings

A coloring has period dividing 2 iff c(i) = c(i+2) for all i.
For n=4, these are: 0000, 0101, 1010, 1111. -/

/-- A coloring has period dividing 2. -/
def hasPeriod2 {k : ℕ} (c : Coloring 4 k) : Prop :=
  ∀ i : Fin 4, c i = c (i + 2)

/-- The period-2 colorings for binary case. -/
theorem period2_colorings_4_2 :
    Fintype.card { c : Coloring 4 2 // hasPeriod2 c } = 4 := by
  -- A period-2 coloring is determined by c(0) and c(1)
  have equiv : { c : Coloring 4 2 // hasPeriod2 c } ≃ (Fin 2 × Fin 2) := {
    toFun := fun ⟨c, _⟩ => (c 0, c 1)
    invFun := fun ⟨a, b⟩ => ⟨
      fun i => if i.val % 2 = 0 then a else b,
      fun i => by
        simp only [hasPeriod2]
        fin_cases i <;> simp
    ⟩
    left_inv := fun ⟨c, hc⟩ => by
      simp only
      ext i
      fin_cases i <;> simp [hc]
    right_inv := fun ⟨a, b⟩ => by simp
  }
  rw [Fintype.card_congr equiv]
  simp only [Fintype.card_prod, Fintype.card_fin]

/-! ## Part VI: Fixed Point Counts

Now we compute |Fix(r)| for each r ∈ Z_4. -/

/-- Fixed by rotation 1: only constant colorings (period 1). -/
theorem fixed_by_one_4 : Fintype.card (fixedBy (Coloring 4 2) (1 : ZMod 4)) = 2 := by
  -- A coloring fixed by rotation 1 must satisfy c(i) = c(i-1) for all i
  -- This means c is constant
  have h : fixedBy (Coloring 4 2) (1 : ZMod 4) = { c | isConstant c } := by
    ext c
    simp only [fixedBy, Set.mem_setOf_eq, isConstant]
    constructor
    · intro hfix i j
      -- c is fixed by rotation 1, so c(i) = c(i-1) for all i
      -- By transitivity, all values are equal
      have step : ∀ k : Fin 4, c k = c (k - 1) := fun k => by
        have := congr_fun hfix k
        simp only [rotateColoring] at this
        exact this.symm
      -- Chain: c(i) = c(i-1) = c(i-2) = ... = c(j)
      induction' i using Fin.inductionOn with i' ih
      · induction' j using Fin.inductionOn with j' jh
        · rfl
        · calc c 0 = c (0 - 1) := step 0
            _ = c (↑3 : Fin 4) := by norm_num
            _ = c (3 - 1) := step 3
            _ = c (↑2 : Fin 4) := by norm_num
            _ = c (2 - 1) := step 2
            _ = c (↑1 : Fin 4) := by norm_num
            _ = c (1 - 1) := step 1
            _ = c (↑0 : Fin 4) := by norm_num
            _ = c j'.succ := by
              fin_cases j' <;> simp [step]
      · calc c i'.succ = c (i'.succ - 1) := step i'.succ
          _ = c i' := by simp
          _ = c j := ih
    · intro hconst
      ext i
      simp only [rotateColoring]
      exact (hconst i (i - 1)).symm
  rw [h]
  convert constant_colorings_4_2
  ext c
  simp only [Set.mem_setOf_eq]

/-- Fixed by rotation 2: period divides 2. -/
theorem fixed_by_two_4 : Fintype.card (fixedBy (Coloring 4 2) (2 : ZMod 4)) = 4 := by
  have h : fixedBy (Coloring 4 2) (2 : ZMod 4) = { c | hasPeriod2 c } := by
    ext c
    simp only [fixedBy, Set.mem_setOf_eq, hasPeriod2]
    constructor
    · intro hfix i
      have := congr_fun hfix i
      simp only [rotateColoring] at this
      -- c(i) = c(i - 2) = c(i + 2) in Z_4
      have key : i - (2 : ZMod 4) = i + 2 := by
        fin_cases i <;> native_decide
      rw [key] at this
      exact this.symm
    · intro hper
      ext i
      simp only [rotateColoring]
      have key : i - (2 : ZMod 4) = i + 2 := by
        fin_cases i <;> native_decide
      rw [key]
      exact (hper i).symm
  rw [h]
  convert period2_colorings_4_2
  ext c
  simp only [Set.mem_setOf_eq]

/-- Fixed by rotation 3: same as rotation 1 (generator). -/
theorem fixed_by_three_4 : Fintype.card (fixedBy (Coloring 4 2) (3 : ZMod 4)) = 2 := by
  -- Rotation by 3 is equivalent to rotation by -1, which generates Z_4
  have h : fixedBy (Coloring 4 2) (3 : ZMod 4) = { c | isConstant c } := by
    ext c
    simp only [fixedBy, Set.mem_setOf_eq, isConstant]
    constructor
    · intro hfix i j
      have step : ∀ k : Fin 4, c k = c (k - 3) := fun k => by
        have := congr_fun hfix k
        simp only [rotateColoring] at this
        exact this.symm
      -- -3 ≡ 1 (mod 4), so stepping by -3 is same as stepping by 1
      fin_cases i <;> fin_cases j <;> try rfl
      all_goals {
        simp only [step]
        fin_cases i <;> fin_cases j <;> simp [step]
      }
    · intro hconst
      ext i
      simp only [rotateColoring]
      exact (hconst i (i - 3)).symm
  rw [h]
  convert constant_colorings_4_2
  ext c
  simp only [Set.mem_setOf_eq]

/-! ## Part VII: Main Counting Theorem -/

/-- **Binary Necklaces of Length 4**:
    There are exactly 6 distinct binary necklaces of length 4.

    By Burnside's lemma:
    Sum of fixed points = 16 + 2 + 4 + 2 = 24
    Number of orbits = 24 / 4 = 6 -/
theorem binary_necklaces_4 :
    Fintype.card (orbitRel.Quotient (ZMod 4) (Coloring 4 2)) = 6 := by
  -- Apply Burnside's lemma
  have burnside := burnside_lemma (G := ZMod 4) (X := Coloring 4 2)
  -- Sum of fixed points
  have sum_fixed : ∑ g : ZMod 4, Fintype.card (fixedBy (Coloring 4 2) g) = 24 := by
    -- Enumerate over Z_4 = {0, 1, 2, 3}
    have : (Finset.univ : Finset (ZMod 4)) = {0, 1, 2, 3} := by
      ext x; fin_cases x <;> simp
    rw [Finset.sum_eq_sum_finset_of_eq_on (s := {0, 1, 2, 3})]
    · simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
                 one_ne_zero, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, not_false_eq_true,
                 Finset.sum_singleton]
      rw [fixed_by_zero_4, fixed_by_one_4, fixed_by_two_4, fixed_by_three_4]
      norm_num
    · intro x _; rfl
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      fin_cases x <;> simp
  -- Group size
  have group_size : Fintype.card (ZMod 4) = 4 := ZMod.card 4
  -- Combine
  rw [sum_fixed, group_size] at burnside
  omega

/-! ## Part VIII: Summary and Exports -/

#check burnside_lemma
#check cyclicActionOnColorings
#check binary_necklaces_4
#check fixed_by_zero_4
#check fixed_by_one_4
#check fixed_by_two_4
#check fixed_by_three_4

end BurnsideCounting
