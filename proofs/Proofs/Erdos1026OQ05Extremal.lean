/-
  Erdős Problem #1026, open question OQ-05 — the Erdős–Szekeres **extremal staircase**.

  The base development (`Erdos1026OQ05.lean`) and its companions establish, for the
  covering number `minMonotonicParts seq` (the least number of monotone subsequences whose
  images cover a length-`n` sequence), the two-sided **bracket**

      n / max (LIS, LDS)  ≤  minMonotonicParts seq  ≤  min (LIS, LDS)      (for distinct reals)

  where the lower half is the elementary Mirsky/Dilworth bound
  (`Erdos1026OQ05.minMonotonicParts_ge`) and the upper half is the sharp identity bound
  (`Erdos1026OQ05IncreasingIdentity.minMonotonicParts_le_min_LIS_LDS`).

  Neither bound, on its own, pins the covering number, and neither exhibits a sequence that
  *forces* many pieces. This file supplies the missing **extremal witness**: the classic
  Erdős–Szekeres staircase on `n = k²` points

      value(i) = k·(i / k) − (i % k)         (blocks of length k, increasing across blocks,
                                              strictly decreasing within each block)

  for which we prove, axiom-free,

      LIS  = k,      LDS = k,      value is injective,

  so that the general bracket **collapses**:

      k = (k²) / max(k, k)  ≤  minMonotonicParts  ≤  min(k, k) = k,

  giving `minMonotonicParts (staircase k) = k = √n`.

  Consequence (`exists_sqrt_monotone_parts_needed`): for every `n = k²` there is a sequence
  whose covering number is exactly `√n`. Hence **Θ(√n) monotone pieces are sometimes
  necessary**, and the general two-sided bracket is **tight** (both bounds are attained
  simultaneously by this family).

  Scope / honesty. This is the *lower-bound* extremal side: it shows `√n` pieces can be
  forced. It does **not** prove the hard universal *upper* bound of Hanani's theorem — that
  `O(√n)` pieces always *suffice* for an arbitrary sequence — which remains open (stated,
  not axiomatized) in `Erdos1026OQ05.lean`.
-/
import Mathlib
import Proofs.Erdos1026OQ05
import Proofs.Erdos1026OQ05IncreasingIdentity

open Finset
open scoped Classical

namespace Erdos1026OQ05Extremal

open Erdos1026OQ05
open Erdos1026OQ05IncreasingIdentity

variable {k : ℕ}

/-- Integer value of the staircase at index `i`: `k·(i/k) − (i%k)`.  Blocks of length `k`
(indexed by the quotient `i/k`) climb by `k` each step, while inside a block the value
strictly decreases as the remainder `i%k` grows. -/
def sval (k : ℕ) (i : Fin (k * k)) : ℤ :=
  (k : ℤ) * (i.val / k : ℕ) - (i.val % k : ℕ)

/-- The Erdős–Szekeres staircase sequence of length `n = k²`. -/
def staircase (k : ℕ) : RealSeq (k * k) := fun i => (sval k i : ℝ)

@[simp] lemma staircase_apply (i : Fin (k * k)) :
    staircase k i = (sval k i : ℝ) := rfl

/-! ### Three elementary value comparisons

These are the only arithmetic facts about the staircase we need. Each isolates one way two
indices can be ordered, and each avoids nonlinearity by cancelling a common block term. -/

/-- **Within a block, the value strictly decreases.** If `i < j` sit in the same block
(`i/k = j/k`), then `sval j < sval i`. -/
lemma sval_lt_of_same_block {i j : Fin (k * k)} (hlt : i.val < j.val)
    (hblk : i.val / k = j.val / k) : sval k j < sval k i := by
  have hi := Nat.div_add_mod i.val k
  have hj := Nat.div_add_mod j.val k
  rw [hblk] at hi
  -- same quotient block term, `i < j` forces the remainders to increase
  have hmod : i.val % k < j.val % k := by omega
  have hcast : (i.val % k : ℤ) < (j.val % k : ℤ) := by exact_mod_cast hmod
  unfold sval
  rw [hblk]
  linarith

/-- **Crossing to a later block, the value strictly increases.** If `i/k < j/k` then
`sval i < sval j`: the block gap contributes at least `k`, dominating the `< k` penalty
from the remainder. -/
lemma sval_lt_of_diff_block {i j : Fin (k * k)} (hk : 0 < k)
    (hblk : i.val / k < j.val / k) : sval k i < sval k j := by
  have hri : (0 : ℤ) ≤ (i.val % k : ℕ) := by positivity
  have hrj : (j.val % k : ℤ) ≤ (k : ℤ) - 1 := by
    have hjm : j.val % k < k := Nat.mod_lt _ hk
    have hjm' : (j.val % k : ℤ) < (k : ℤ) := by exact_mod_cast hjm
    omega
  have hqlt : ((i.val / k : ℕ) : ℤ) + 1 ≤ ((j.val / k : ℕ) : ℤ) := by
    have hq : i.val / k + 1 ≤ j.val / k := hblk
    exact_mod_cast hq
  have hk0 : (0 : ℤ) ≤ (k : ℤ) := by positivity
  unfold sval
  nlinarith [mul_le_mul_of_nonneg_right hqlt hk0, hri, hrj]

/-- **Within a column, the value strictly increases.** If `i < j` share a remainder
(`i%k = j%k`, i.e. the same position inside their blocks) then `sval i < sval j`. -/
lemma sval_lt_of_same_col {i j : Fin (k * k)} (hlt : i.val < j.val)
    (hcol : i.val % k = j.val % k) : sval k i < sval k j := by
  have hi := Nat.div_add_mod i.val k
  have hj := Nat.div_add_mod j.val k
  rw [hcol] at hi
  -- equal remainders, `i < j` forces the block terms `k·(·/k)` to increase
  have hblk : k * (i.val / k) < k * (j.val / k) := by omega
  have hcast : ((k * (i.val / k) : ℕ) : ℤ) < ((k * (j.val / k) : ℕ) : ℤ) := by
    exact_mod_cast hblk
  have hccol : (i.val % k : ℤ) = (j.val % k : ℤ) := by exact_mod_cast hcol
  unfold sval
  push_cast at hcast ⊢
  linarith

/-! ### Injectivity of the staircase -/

/-- The staircase value function is injective: distinct indices carry distinct values.
Needed for the sharp upper bound `minMonotonicParts ≤ min (LIS, LDS)`. -/
theorem staircase_injective (hk : 0 < k) : Function.Injective (staircase k) := by
  intro i j hij
  by_contra hne
  -- reduce to an equation of integer values, then compare via the block structure
  have hval : sval k i = sval k j := by
    have hr : (sval k i : ℝ) = (sval k j : ℝ) := hij
    exact_mod_cast hr
  have hvne : i.val ≠ j.val := fun h => hne (Fin.ext h)
  rcases lt_trichotomy i.val j.val with hlt | heq | hgt
  · -- i before j
    have hdle : i.val / k ≤ j.val / k := Nat.div_le_div_right (le_of_lt hlt)
    rcases eq_or_lt_of_le hdle with hblk | hblk
    · exact absurd hval (ne_of_gt (sval_lt_of_same_block hlt hblk))
    · exact absurd hval (ne_of_lt (sval_lt_of_diff_block hk hblk))
  · exact hvne heq
  · -- j before i (symmetric)
    have hdle : j.val / k ≤ i.val / k := Nat.div_le_div_right (le_of_lt hgt)
    rcases eq_or_lt_of_le hdle with hblk | hblk
    · exact absurd hval.symm (ne_of_gt (sval_lt_of_same_block hgt hblk))
    · exact absurd hval.symm (ne_of_lt (sval_lt_of_diff_block hk hblk))

/-! ### `LIS = k`: no increasing run longer than `k`, and one of length `k` -/

/-- Upper bound: any increasing subsequence hits each block at most once, so its length is
at most the number of blocks, `k`. -/
theorem staircase_LIS_le (hk : 0 < k) : LIS (staircase k) ≤ k := by
  apply csSup_le ⟨0, Subsequence.mk Fin.elim0 (fun a => a.elim0), by intro a; exact a.elim0⟩
  rintro m ⟨sub, hInc⟩
  -- block of each chosen index
  have hblt : ∀ j : Fin m, (sub.indices j).val / k < k := by
    intro j
    have hlt : (sub.indices j).val < k * k := (sub.indices j).isLt
    exact (Nat.div_lt_iff_lt_mul hk).mpr hlt
  let blk : Fin m → Fin k := fun j => ⟨(sub.indices j).val / k, hblt j⟩
  have hkey : ∀ a b : Fin m, a < b → blk a ≠ blk b := by
    intro a b hab hblkeq
    have hidx : (sub.indices a).val < (sub.indices b).val := sub.strictMono hab
    have hbeq : (sub.indices a).val / k = (sub.indices b).val / k := by
      have hc := congrArg Fin.val hblkeq; simpa [blk] using hc
    -- same block ⇒ value decreases, contradicting the increasing subsequence
    have hdec : sval k (sub.indices b) < sval k (sub.indices a) :=
      sval_lt_of_same_block hidx hbeq
    have hinc : (staircase k) (sub.indices a) < (staircase k) (sub.indices b) := hInc hab
    simp only [staircase_apply] at hinc
    have hsi : sval k (sub.indices a) < sval k (sub.indices b) := by exact_mod_cast hinc
    exact absurd hdec (not_lt.mpr (le_of_lt hsi))
  have hinj : Function.Injective blk := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hkey a b h hab
    · exact hkey b a h hab.symm
  have hcard := Fintype.card_le_of_injective blk hinj
  simpa using hcard

/-- Lower bound: the "first-column" subsequence `j ↦ k·j` (block index `j`, remainder `0`)
is strictly increasing of length `k`. -/
theorem staircase_LIS_ge (hk : 0 < k) : k ≤ LIS (staircase k) := by
  have hbound : ∀ j : Fin k, k * j.val < k * k := fun j => mul_lt_mul_of_pos_left j.isLt hk
  let sub : Subsequence (k * k) k :=
    ⟨fun j => ⟨k * j.val, hbound j⟩, by
      intro a b hab
      have hab' : a.val < b.val := hab
      simp only [Fin.mk_lt_mk]
      exact mul_lt_mul_of_pos_left hab' hk⟩
  have hval : ∀ j : Fin k, sval k (sub.indices j) = (k : ℤ) * j.val := by
    intro j
    have hq : ((sub.indices j).val) / k = j.val := by
      show (k * j.val) / k = j.val
      exact Nat.mul_div_cancel_left j.val hk
    have hr : ((sub.indices j).val) % k = 0 := by
      have hdm := Nat.div_add_mod ((sub.indices j).val) k
      rw [hq] at hdm
      have hval2 : (sub.indices j).val = k * j.val := rfl
      omega
    unfold sval
    rw [hq, hr]
    push_cast; ring
  have hInc : IsIncreasing (staircase k) sub := by
    intro a b hab
    have hab' : a.val < b.val := hab
    show (staircase k) (sub.indices a) < (staircase k) (sub.indices b)
    rw [staircase_apply, staircase_apply, hval, hval]
    have hkpos : (0 : ℤ) < k := by exact_mod_cast hk
    have hlt : (k : ℤ) * a.val < (k : ℤ) * b.val := by
      have hcab : (a.val : ℤ) < (b.val : ℤ) := by exact_mod_cast hab'
      exact (mul_lt_mul_left hkpos).mpr hcab
    exact_mod_cast hlt
  exact len_le_LIS_of_increasing hInc

theorem staircase_LIS (hk : 0 < k) : LIS (staircase k) = k :=
  le_antisymm (staircase_LIS_le hk) (staircase_LIS_ge hk)

/-! ### `LDS = k`: no decreasing run longer than `k`, and one of length `k` -/

/-- Upper bound: any decreasing subsequence hits each column (remainder class) at most once,
so its length is at most `k`. -/
theorem staircase_LDS_le (hk : 0 < k) : LDS (staircase k) ≤ k := by
  apply csSup_le ⟨0, Subsequence.mk Fin.elim0 (fun a => a.elim0), by intro a b hab; exact a.elim0⟩
  rintro m ⟨sub, hDec⟩
  let col : Fin m → Fin k := fun j => ⟨(sub.indices j).val % k, Nat.mod_lt _ hk⟩
  have hkey : ∀ a b : Fin m, a < b → col a ≠ col b := by
    intro a b hab hcoleq
    have hidx : (sub.indices a).val < (sub.indices b).val := sub.strictMono hab
    have hceq : (sub.indices a).val % k = (sub.indices b).val % k := by
      have hc := congrArg Fin.val hcoleq; simpa [col] using hc
    -- same column ⇒ value increases, contradicting the decreasing subsequence
    have hinc : sval k (sub.indices a) < sval k (sub.indices b) :=
      sval_lt_of_same_col hidx hceq
    have hdec : (staircase k) (sub.indices b) < (staircase k) (sub.indices a) := hDec a b hab
    simp only [staircase_apply] at hdec
    have hsi : sval k (sub.indices b) < sval k (sub.indices a) := by exact_mod_cast hdec
    exact absurd hinc (not_lt.mpr (le_of_lt hsi))
  have hinj : Function.Injective col := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hkey a b h hab
    · exact hkey b a h hab.symm
  have hcard := Fintype.card_le_of_injective col hinj
  simpa using hcard

/-- Lower bound: the "first-block" subsequence `j ↦ j` (block `0`, remainder `j`) is
strictly decreasing of length `k`. -/
theorem staircase_LDS_ge (hk : 0 < k) : k ≤ LDS (staircase k) := by
  have hbound : ∀ j : Fin k, j.val < k * k := by
    intro j
    have hkk : k ≤ k * k := le_mul_of_one_le_left (Nat.zero_le k) hk
    exact lt_of_lt_of_le j.isLt hkk
  let sub : Subsequence (k * k) k :=
    ⟨fun j => ⟨j.val, hbound j⟩, by
      intro a b hab
      have hab' : a.val < b.val := hab
      simp only [Fin.mk_lt_mk]
      exact hab'⟩
  have hval : ∀ j : Fin k, sval k (sub.indices j) = -(j.val : ℤ) := by
    intro j
    have hq : ((sub.indices j).val) / k = 0 := by
      show j.val / k = 0
      exact Nat.div_eq_of_lt j.isLt
    have hr : ((sub.indices j).val) % k = j.val := by
      show j.val % k = j.val
      exact Nat.mod_eq_of_lt j.isLt
    unfold sval
    rw [hq, hr]
    push_cast; ring
  have hDec : IsDecreasing (staircase k) sub := by
    intro a b hab
    have hab' : a.val < b.val := hab
    show (staircase k) (sub.indices b) < (staircase k) (sub.indices a)
    rw [staircase_apply, staircase_apply, hval, hval]
    have hlt : (-(b.val : ℤ)) < (-(a.val : ℤ)) := by
      have hcab : (a.val : ℤ) < (b.val : ℤ) := by exact_mod_cast hab'
      linarith
    exact_mod_cast hlt
  exact len_le_LDS_of_decreasing hDec

theorem staircase_LDS (hk : 0 < k) : LDS (staircase k) = k :=
  le_antisymm (staircase_LDS_le hk) (staircase_LDS_ge hk)

/-! ### The bracket collapses: `minMonotonicParts (staircase k) = k = √n` -/

/-- **Extremal identity.** For the Erdős–Szekeres staircase on `n = k²` points the covering
number is exactly `k`. Both sides of the general bracket coincide:

* lower bound `k²/max(LIS,LDS) = k²/k = k ≤ minMonotonicParts`   (`minMonotonicParts_ge`), and
* upper bound `minMonotonicParts ≤ min(LIS,LDS) = k`             (`minMonotonicParts_le_min_LIS_LDS`).
-/
theorem minMonotonicParts_staircase (hk : 0 < k) :
    minMonotonicParts (staircase k) = k := by
  have hLIS := staircase_LIS hk
  have hLDS := staircase_LDS hk
  -- upper: minMonotonicParts ≤ min (LIS, LDS) = k
  have hup : minMonotonicParts (staircase k) ≤ k := by
    have h := minMonotonicParts_le_min_LIS_LDS (staircase k) (staircase_injective hk)
    rw [hLIS, hLDS, min_self] at h
    exact h
  -- lower: k = (k*k)/k = (k*k)/max(LIS,LDS) ≤ minMonotonicParts
  have hlo : k ≤ minMonotonicParts (staircase k) := by
    have h := minMonotonicParts_ge (staircase k)
    rw [hLIS, hLDS, max_self] at h
    rwa [Nat.mul_div_cancel_left k hk] at h
  exact le_antisymm hup hlo

/-- The covering number of the length-`n = k²` staircase equals `√n`. -/
theorem minMonotonicParts_staircase_eq_sqrt (hk : 0 < k) :
    minMonotonicParts (staircase k) = Nat.sqrt (k * k) := by
  rw [minMonotonicParts_staircase hk, Nat.sqrt_eq]

/-- **`Θ(√n)` monotone pieces are sometimes necessary.** For every `n = k²` (with `k ≥ 1`)
there is a length-`n` sequence whose covering number is exactly `√n`. Together with the
elementary upper bound `minMonotonicParts ≤ min(LIS,LDS)`, this shows the two-sided bracket
is tight and that no bound better than `√n` holds for the worst case. -/
theorem exists_sqrt_monotone_parts_needed (hk : 0 < k) :
    ∃ seq : RealSeq (k * k), minMonotonicParts seq = Nat.sqrt (k * k) :=
  ⟨staircase k, minMonotonicParts_staircase_eq_sqrt hk⟩

end Erdos1026OQ05Extremal
