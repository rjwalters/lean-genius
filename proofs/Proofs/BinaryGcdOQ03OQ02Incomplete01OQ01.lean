/-
  Schönhage's Recursive HGCD — the Size-Reduction Recurrence and O(M(n)·log n) Bound
  ==================================================================================

  Problem: binary-gcd-oq-03-oq-02-incomplete-01-oq-01
  "HGCD size-reduction bound giving O(M(n)·log n) complexity"

  Context. The recursive half-GCD entry `binary-gcd-oq-03-oq-02`
  (BinaryGcdOQ03OQ02.lean) formalizes Schönhage's algorithm and proves the
  GCD-preservation invariant, but explicitly DEFERS the bit-complexity claim:
  its own docstring states "The bit-complexity claim O(M(n)·log n) requires a
  Mathlib model of [the recurrence]". The sibling companion
  `binary-gcd-oq-03-oq-02-incomplete-01` (BinaryGcdOQ03OQ02Incomplete01.lean)
  isolates the unimodular GROUP structure and remarks that "size-reduction is the
  only genuinely hard part".

  This file closes the complexity strand at the abstract-recurrence level, fully
  axiom-free. Schönhage's HGCD on an n-bit input performs two recursive calls,
  each on operands of at most ⌊n/2⌋ bits (the SIZE-REDUCTION / halving property),
  plus O(M(n)) work for the multiplications joining the two halves. Writing T(n)
  for the total cost this is the divide-and-conquer recurrence

        T(n) ≤ 2·T(⌊n/2⌋) + M(n),      T(n) ≤ M(n) for n ≤ 1.                (★)

  The classical solution, under the standard regularity hypothesis that the merge
  on the two halves never costs more than the merge on the whole
  (`2·M(⌊n/2⌋) ≤ M(n)`, the "superlinear multiplication" assumption satisfied by
  every realistic M — schoolbook n², Karatsuba n^log₂3, and quasi-linear
  n·log n·log log n), is

        T(n) ≤ (⌊log₂ n⌋ + 1)·M(n)  =  O(M(n)·log n).

  We prove exactly this (`cost_le`), abstractly over M and T, by strong induction
  on n. The factor `Nat.log 2 n + 1` is precisely the recursion DEPTH — the number
  of halving steps — and equals the bit-length `Nat.size n` (`depth_eq_size`), so
  the bound reads `T(n) ≤ (bit-length of n)·M(n)` (`cost_le_size`). The linear
  merge model `M = id` gives the clean corollary `T(n) ≤ (⌊log₂ n⌋ + 1)·n`
  (`cost_le_linear`), i.e. O(n log n).

  We use FLOOR division ⌊n/2⌋ in (★): the standard textbook normalization for
  divide-and-conquer upper bounds, which makes the depth exactly `Nat.log 2 n`
  (`Nat.log_of_one_lt_of_le`). The ceiling variant differs only by ±1 rounding and
  has the same O(M(n)·log n) asymptotics.

  Self-contained: no dependency on the parent's `native_decide` results.
  0 sorries, 0 axioms.
-/

import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic

namespace SchonhageHGCD.Complexity

/-! ### The size-reduction regularity condition -/

/-- A cost/merge function `M : ℕ → ℕ` is *halving-regular* when a single merge
    step on the two size-`⌊n/2⌋` halves costs at most the merge on the whole:
    `2·M(⌊n/2⌋) ≤ M(n)` for `n ≥ 2`. This is the standard "superlinear
    multiplication" hypothesis of the master theorem; it holds for every
    super-additive monotone `M`, in particular `M(n) = n·(log n)ᵏ` and `M(n) = nᵃ`
    with `a ≥ 1`. -/
def HalvingRegular (M : ℕ → ℕ) : Prop := ∀ n, 2 ≤ n → 2 * M (n / 2) ≤ M n

/-- Every super-additive, monotone cost function is halving-regular:
    `M(⌊n/2⌋) + M(⌊n/2⌋) ≤ M(⌊n/2⌋ + ⌊n/2⌋) ≤ M(n)`, since `2·⌊n/2⌋ ≤ n`. -/
theorem halvingRegular_of_superadditive {M : ℕ → ℕ}
    (hmono : Monotone M) (hsuper : ∀ a b, M a + M b ≤ M (a + b)) :
    HalvingRegular M := by
  intro n _
  calc 2 * M (n / 2) = M (n / 2) + M (n / 2) := by ring
    _ ≤ M (n / 2 + n / 2) := hsuper _ _
    _ ≤ M n := hmono (by omega)

/-! ### The master-theorem bound -/

/-- **HGCD complexity bound.** Any cost function `T` satisfying the size-reduction
    recurrence `T(n) ≤ 2·T(⌊n/2⌋) + M(n)` (with base `T(n) ≤ M(n)` for `n ≤ 1`) and
    driven by a halving-regular merge `M` obeys

        `T(n) ≤ (Nat.log 2 n + 1) · M(n)`,

    i.e. `T(n) = O(M(n)·log n)`. The factor `Nat.log 2 n + 1` is the recursion
    depth: the number of halving steps until the base case. -/
theorem cost_le (M T : ℕ → ℕ)
    (hreg : HalvingRegular M)
    (hbase : ∀ n, n ≤ 1 → T n ≤ M n)
    (hrec : ∀ n, 2 ≤ n → T n ≤ 2 * T (n / 2) + M n) :
    ∀ n, T n ≤ (Nat.log 2 n + 1) * M n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases le_or_gt n 1 with hn | hn
    · -- base case: n ≤ 1, so log₂ n = 0 and the bound is T n ≤ M n
      have hl0 : Nat.log 2 n = 0 := Nat.log_of_lt (by omega)
      simpa [hl0] using hbase n hn
    · -- inductive step: n ≥ 2
      have h2 : 2 ≤ n := hn
      have hhalf : n / 2 < n := Nat.div_lt_self (by omega) (by norm_num)
      have IH : T (n / 2) ≤ (Nat.log 2 (n / 2) + 1) * M (n / 2) := ih _ hhalf
      have hlog : Nat.log 2 n = Nat.log 2 (n / 2) + 1 :=
        Nat.log_of_one_lt_of_le (by norm_num) h2
      have hr : 2 * M (n / 2) ≤ M n := hreg n h2
      calc T n
          ≤ 2 * T (n / 2) + M n := hrec n h2
        _ ≤ 2 * ((Nat.log 2 (n / 2) + 1) * M (n / 2)) + M n := by gcongr
        _ = (Nat.log 2 (n / 2) + 1) * (2 * M (n / 2)) + M n := by ring
        _ ≤ (Nat.log 2 (n / 2) + 1) * M n + M n := by gcongr
        _ = (Nat.log 2 (n / 2) + 1 + 1) * M n := by ring
        _ = (Nat.log 2 n + 1) * M n := by rw [hlog]

/-! ### The recursion depth is the bit-length -/

/-- The recursion depth `⌊log₂ n⌋ + 1` equals the bit-length `Nat.size n` of the
    input (for `n > 0`): each halving level strips one bit off the operands, so the
    number of levels is exactly the number of bits. -/
theorem depth_eq_size {n : ℕ} (hn : 0 < n) : Nat.log 2 n + 1 = Nat.size n := by
  have h1 : Nat.log 2 n < Nat.size n :=
    Nat.lt_size.mpr (Nat.pow_log_le_self 2 (by omega))
  have h2 : Nat.size n ≤ Nat.log 2 n + 1 :=
    Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by norm_num) n)
  omega

/-- **HGCD complexity in bit-length form.** For a positive-size input the total
    cost is at most `(bit-length of n)·M(n)`, making the size-reduction depth
    explicit as `Nat.size n` and exhibiting the `O(M(n)·log n)` bound. -/
theorem cost_le_size (M T : ℕ → ℕ) (hreg : HalvingRegular M)
    (hbase : ∀ n, n ≤ 1 → T n ≤ M n)
    (hrec : ∀ n, 2 ≤ n → T n ≤ 2 * T (n / 2) + M n)
    {n : ℕ} (hn : 0 < n) : T n ≤ Nat.size n * M n := by
  have h := cost_le M T hreg hbase hrec n
  rwa [depth_eq_size hn] at h

/-! ### Concrete model: linear merge gives O(n · log n) -/

/-- The identity merge `M = id` (a linear-time join) is halving-regular:
    `2·⌊n/2⌋ ≤ n`. -/
theorem halvingRegular_id : HalvingRegular id := fun n _ => by
  simp only [id_eq]; omega

/-- **Linear-merge corollary (O(n·log n)).** With a linear merge cost the total
    HGCD cost is `T(n) ≤ (⌊log₂ n⌋ + 1)·n`. This is the shape of the classical
    Θ(n log n) bound for Schönhage-style GCD with (quasi-)linear multiplication. -/
theorem cost_le_linear (T : ℕ → ℕ)
    (hbase : ∀ n, n ≤ 1 → T n ≤ n)
    (hrec : ∀ n, 2 ≤ n → T n ≤ 2 * T (n / 2) + n) :
    ∀ n, T n ≤ (Nat.log 2 n + 1) * n := by
  intro n
  have h := cost_le id T halvingRegular_id hbase hrec n
  simpa using h

/-! ### Axiom audit -/

-- Confirm the whole development rests only on the standard foundational axioms
-- (no `sorryAx`, no `Lean.ofReduceBool`): the bound is fully machine-checked.
#print axioms cost_le
#print axioms cost_le_size
#print axioms cost_le_linear
#print axioms depth_eq_size

end SchonhageHGCD.Complexity
