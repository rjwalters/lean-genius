import Mathlib

/-
# The Simplicial Figurate-Number Tower as a Single Parametrized Family

## Open Question (combinations-formula-oq-06, OQ-01)

The parent entry `combinations-formula-oq-06` formalized the general hockey-stick
identity `∑_{m ∈ Icc k n} C(m, k) = C(n+1, k+1)` and then *read off* its figurate
consequences only at the first two rungs `k = 1` (triangular) and `k = 2` (tetrahedral)
as separate hand-built theorems.  Its conclusion explicitly raises the question of
whether the uniform statement specializes to arbitrary `k`-dimensional figurate numbers
`C(n+k-1, k)`, "giving the full Pythagorean tower as a single parametrized family."

## Contribution

We package the *entire* simplicial ladder as one Lean object.  The `k`-dimensional
figurate number is the multiset coefficient

  `S(k, n) = C(n + k - 1, k) = multichoose n k`,

so `S(1, n) = n` (linear), `S(2, n) = C(n+1, 2)` (triangular),
`S(3, n) = C(n+2, 3)` (tetrahedral), and so on up the dimensional ladder.  We prove,
*uniformly in the dimension* `k`:

1. `S_succ_succ`   — the Pascal-type recurrence `S(k+1, n+1) = S(k+1, n) + S(k, n+1)`,
   the single recurrence that drives the whole family.
2. `sum_Icc_S`     — the **tower identity** `∑_{m=1}^{n} S(k, m) = S(k+1, n)`: each
   dimension is the running total of the one beneath it.  The induction step is *exactly*
   the recurrence (1), so the proof is the same one line for every `k`.
3. `sum_Icc_S_pred`— the classical figurate restatement `∑_{m=1}^{n} S(k-1, m) = S(k, n)`
   for `k ≥ 1` (the triangular → tetrahedral → pentatope → … stacking of antiquity).
4. `S_one`, `S_two`, `S_three` — the `k = 1, 2, 3` slices recover the natural, triangular,
   and tetrahedral numbers, subsuming the parent's hand-built instances; `S_two_closed`
   recovers the closed form `n(n+1)/2`.
5. `sum_triangular`, `sum_tetrahedral` — the parent's `triangular` and `tetrahedral`
   tower steps fall out as the `k = 1` and `k = 2` cases of the single theorem (2).

## Mathematical Context

The whole development rests on `Nat.multichoose` and its Pascal recurrence
`Nat.multichoose_succ_succ`.  Reading that recurrence as a statement about partial sums
gives the figurate recurrences `T_n = T_{n-1} + n`, `Te_n = Te_{n-1} + T_n`, … all at
once — which is precisely why a *single* induction, parametrized by the dimension `k`,
covers every column of Pascal's triangle simultaneously.  The bridge to binomial form is
`Nat.multichoose_eq : multichoose n k = C(n + k - 1, k)`.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFigurateTower

open Finset

/-- The `k`-dimensional simplicial (figurate) number,
    `S(k, n) = C(n + k - 1, k) = multichoose n k`.  The index `k` is the "dimension":
    `k = 1` counts points on a line, `k = 2` triangles, `k = 3` tetrahedra, and so on. -/
def S (k n : ℕ) : ℕ := Nat.multichoose n k

theorem S_def (k n : ℕ) : S k n = Nat.multichoose n k := rfl

/-- `S(k, n)` in pure binomial form: the multiset coefficient `C(n + k - 1, k)`. -/
theorem S_eq_choose (k n : ℕ) : S k n = Nat.choose (n + k - 1) k := by
  rw [S_def, Nat.multichoose_eq]

/-- **Pascal-type recurrence.**  Each figurate number is its predecessor in the same
    dimension plus the figurate number one dimension down:
    `S(k+1, n+1) = S(k+1, n) + S(k, n+1)`.  This single recurrence drives the entire
    simplicial family. -/
theorem S_succ_succ (k n : ℕ) : S (k + 1) (n + 1) = S (k + 1) n + S k (n + 1) := by
  simp only [S_def]
  rw [Nat.multichoose_succ_succ]

/-- **The figurate tower (parametrized form).**  Uniformly in the dimension `k`, each
    layer is the running total of the layer below it: `∑_{m=1}^{n} S(k, m) = S(k+1, n)`.
    The induction step is exactly the recurrence `S_succ_succ`, so one proof serves every
    dimension at once. -/
theorem sum_Icc_S (k n : ℕ) :
    ∑ m ∈ Finset.Icc 1 n, S k m = S (k + 1) n := by
  induction n with
  | zero => simp [S]
  | succ n ih =>
      rw [Finset.sum_Icc_succ_top (show (1 : ℕ) ≤ n + 1 by omega), ih, S_succ_succ]

/-- **The figurate tower (classical figurate form).**  For `k ≥ 1`, the `k`-dimensional
    figurate numbers are the running totals of the `(k-1)`-dimensional ones:
    `∑_{m=1}^{n} S(k-1, m) = S(k, n)`.  With `k ≥ 2` this is the
    triangular → tetrahedral → pentatope → … stacking of antiquity. -/
theorem sum_Icc_S_pred (k n : ℕ) (hk : 1 ≤ k) :
    ∑ m ∈ Finset.Icc 1 n, S (k - 1) m = S k n := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos hk).symm⟩
  simpa using sum_Icc_S j n

/-- `S(1, n) = n`: the linear (counting) numbers. -/
@[simp] theorem S_one (n : ℕ) : S 1 n = n := Nat.multichoose_one_right n

/-- `S(2, n) = C(n+1, 2)`: the triangular numbers. -/
theorem S_two (n : ℕ) : S 2 n = Nat.choose (n + 1) 2 := by
  rw [S_eq_choose, show n + 2 - 1 = n + 1 by omega]

/-- `S(3, n) = C(n+2, 3)`: the tetrahedral numbers. -/
theorem S_three (n : ℕ) : S 3 n = Nat.choose (n + 2) 3 := by
  rw [S_eq_choose, show n + 3 - 1 = n + 2 by omega]

/-- The triangular number `S(2, n) = C(n+1, 2)` in its familiar closed form `n(n+1)/2`,
    recovering the parent's `triangular_closed_form`. -/
theorem S_two_closed (n : ℕ) : S 2 n = n * (n + 1) / 2 := by
  rw [S_two, Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm]

/-- Recovers the parent's triangular identity as the `k = 1` case of the tower:
    the running total of `1, 2, …, n` is the triangular number `C(n+1, 2)`. -/
theorem sum_triangular (n : ℕ) :
    ∑ m ∈ Finset.Icc 1 n, m = Nat.choose (n + 1) 2 := by
  simpa [S_two] using sum_Icc_S 1 n

/-- Recovers the parent's tetrahedral tower as the `k = 2` case of the tower:
    the running total of the triangular numbers `T_m = C(m+1, 2)` is the tetrahedral
    number `C(n+2, 3)`. -/
theorem sum_tetrahedral (n : ℕ) :
    ∑ m ∈ Finset.Icc 1 n, Nat.choose (m + 1) 2 = Nat.choose (n + 2) 3 := by
  simpa [S_two, S_three] using sum_Icc_S 2 n

-- Concrete verifications.  (`multichoose` is compiled by well-founded recursion, so we
-- route these through the binomial form, which the kernel `decide` can evaluate.)
/-- Tetrahedral number `S(3, 4) = C(6, 3) = 20`. -/
example : S 3 4 = 20 := by rw [S_three]; decide
/-- The tower at `k = 2`: `T_1 + T_2 + T_3 + T_4 = 1 + 3 + 6 + 10 = 20 = S(3, 4)`. -/
example : ∑ m ∈ Finset.Icc 1 4, S 2 m = S 3 4 := by simp only [S_two, S_three]; decide
/-- The Pascal recurrence numerically: `S(3, 5) = S(3, 4) + S(2, 5) = 20 + 15 = 35`. -/
example : S 3 5 = S 3 4 + S 2 5 := by simp only [S_three, S_two]; decide

end CombinationsFigurateTower
