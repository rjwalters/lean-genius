import Mathlib
import Proofs.LucasTheoremOQ01

/-!
# The Sierpiński count: `3^m` odd entries in the first `2^m` rows of Pascal's triangle

The parent file (`Proofs.LucasTheoremOQ01`) proves **Glaisher's closed form** for the
number of odd entries in a *single* row of Pascal's triangle:

> `oddCount n = 2 ^ s₂(n)`,

where `s₂(n)` is the binary digit sum of `n`.  This file answers the listed next step
"sum over rows": the **total** number of odd entries in the first `2^m` rows
(`n = 0, 1, …, 2^m − 1`) is exactly

> `∑_{n < 2^m} oddCount n = 3^m`.

This is the arithmetic shadow of the **Sierpiński triangle**: colouring the odd entries
of Pascal's triangle black produces the Sierpiński gasket, and the count `3^m` over a
`2^m`-tall block is precisely the self-similarity that gives the gasket its fractal
(Hausdorff) dimension `log₂ 3 ≈ 1.585`.

The engine is the single new digit lemma
`s2_two_pow_add : s₂(2^m + k) = s₂(k) + 1` for `k < 2^m` (prepending a leading `1`-bit
adds one to the digit sum), combined with the parent's Glaisher formula.  The sum then
satisfies the doubling recursion `T(m+1) = T(m) + 2·T(m) = 3·T(m)`, because the upper
half `[2^m, 2^{m+1})` reindexes to `2^m + k` and each term `2^{s₂(2^m+k)} = 2·2^{s₂ k}`
is doubled.

All results are fully machine-checked: `0` `sorry`, `0` `axiom`, no `native_decide`.
-/

open Nat Finset

open LucasOddEntries

namespace LucasSierpinski

/-! ## The binary digit sum: step relation and leading-bit lemma -/

/-- The binary-digit-sum recursion `s₂ n = (n mod 2) + s₂(n / 2)`, valid for **all** `n`
(the parent's `s2_pos` requires `0 < n`; the `n = 0` case is `0 = 0 + 0`). -/
theorem s2_step (n : ℕ) : s2 n = n % 2 + s2 (n / 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [s2]
  · exact s2_pos n hn

/-- Prepending a leading `1`-bit at position `m` increments the binary digit sum:
for `k < 2^m`, the binary expansion of `2^m + k` is that of `k` with a fresh top `1`,
so `s₂(2^m + k) = s₂(k) + 1`. -/
theorem s2_two_pow_add (m : ℕ) : ∀ k, k < 2 ^ m → s2 (2 ^ m + k) = s2 k + 1 := by
  induction m with
  | zero =>
    intro k hk
    interval_cases k
    -- `s₂(2^0 + 0) = s₂ 1 = 1 = s₂ 0 + 1`
    simp only [pow_zero, Nat.add_zero]
    rw [s2_step 1, s2_zero]
  | succ m ih =>
    intro k hk
    rw [s2_step (2 ^ (m + 1) + k)]
    -- The new top bit is even, so the low bit is unchanged: `(2^{m+1} + k) % 2 = k % 2`.
    have e1 : (2 ^ (m + 1) + k) % 2 = k % 2 := by
      rw [pow_succ]; omega
    -- Halving drops to one lower level: `(2^{m+1} + k) / 2 = 2^m + k / 2`.
    have e2 : (2 ^ (m + 1) + k) / 2 = 2 ^ m + k / 2 := by
      rw [pow_succ]; omega
    have hk2 : k / 2 < 2 ^ m := by
      rw [pow_succ] at hk; omega
    rw [e1, e2, ih (k / 2) hk2, s2_step k]
    ring

/-! ## The Sierpiński sum identity -/

/-- The sum of `2^{s₂ n}` over a `2^m`-block is `3^m`.  This is the abstract form of the
Sierpiński count, independent of the binomial-coefficient interpretation. -/
theorem sum_two_pow_s2 (m : ℕ) : ∑ n ∈ range (2 ^ m), 2 ^ s2 n = 3 ^ m := by
  induction m with
  | zero => simp [s2_zero]
  | succ m ih =>
    -- Split `[0, 2^{m+1}) = [0, 2^m) ∪ [2^m, 2^{m+1})` via `2^{m+1} = 2^m + 2^m`.
    have hsplit : (2 : ℕ) ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; ring
    rw [hsplit, Finset.sum_range_add]
    -- The upper half doubles, by the leading-bit lemma.
    have hsecond : ∑ n ∈ range (2 ^ m), 2 ^ s2 (2 ^ m + n)
        = 2 * ∑ n ∈ range (2 ^ m), 2 ^ s2 n := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun n hn => ?_)
      rw [Finset.mem_range] at hn
      rw [s2_two_pow_add m n hn, pow_succ]
      ring
    rw [hsecond, ih, pow_succ]
    ring

/-! ## The Pascal-triangle count -/

/-- **Sierpiński count.** The total number of odd entries in the first `2^m` rows of
Pascal's triangle (rows `0, 1, …, 2^m − 1`) equals `3^m`.  Combined with the fractal
self-similarity `oddCount` exhibits, this is the discrete origin of the Sierpiński
gasket's Hausdorff dimension `log₂ 3`. -/
theorem sum_oddCount_eq_three_pow (m : ℕ) :
    ∑ n ∈ range (2 ^ m), oddCount n = 3 ^ m := by
  rw [← sum_two_pow_s2 m]
  exact Finset.sum_congr rfl (fun n _ => oddCount_eq_two_pow_s2 n)

/-! ## Sanity checks -/

/-- The first `4 = 2²` rows `1 | 1 1 | 1 2 1 | 1 3 3 1` contain
`1 + 2 + 2 + 4 = 9 = 3²` odd entries. -/
example : ∑ n ∈ range (2 ^ 2), oddCount n = 9 := by decide

/-- The first `8 = 2³` rows contain `3³ = 27` odd entries. -/
example : ∑ n ∈ range (2 ^ 3), oddCount n = 27 := by decide

end LucasSierpinski
