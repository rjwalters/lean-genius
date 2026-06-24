import Mathlib
import Proofs.LucasTheoremOQ01OQ01

/-!
# Row-sum fractal dimension: `∑_{n < pᵐ} fineCount p n = (p(p+1)/2)ᵐ`

For a prime `p`, `fineCount p n` (from `LucasTheoremOQ01OQ01`, **Fine's theorem**) counts
the entries of row `n` of Pascal's triangle that are *not* divisible by `p`; it equals the
digit product `∏ᵢ (nᵢ + 1)` over the base-`p` digits of `n`.

Summing `fineCount` over a full block of `pᵐ` rows gives a clean closed form:

> **Row-sum identity.** `∑_{n < pᵐ} fineCount p n = (p(p+1)/2)ᵐ`.

For `p = 2` this is the total `3ᵐ` non-divisible (odd) entries in the first `2ᵐ` rows of
Pascal's triangle — the Sierpiński-gasket count of `LucasTheoremOQ01OQ02` — and the
exponential growth rate `log_p (p(p+1)/2)` is the box-counting (fractal) dimension of the
mod-`p` Pascal triangle, generalising the Sierpiński dimension `log₂ 3`.

## The proof

The engine is the multiplicative recursion `fineCount_recursion` already established for
Fine's theorem,

* `fineCount p (p·j + r) = (r + 1) · fineCount p j`  for `r < p`.

Partition the block `{0, …, pᵐ⁺¹ − 1}` by the last base-`p` digit: every `n < pᵐ⁺¹` is
uniquely `n = p·j + r` with `j < pᵐ` and `r < p`.  Summing the recursion over `r` factors
out the triangular number `∑_{r < p} (r + 1) = p(p+1)/2`, leaving `fineCount p j`, so

* `∑_{n < pᵐ⁺¹} fineCount p n = (p(p+1)/2) · ∑_{j < pᵐ} fineCount p j`,

and a one-line induction closes the closed form.  Two reusable arithmetic facts are proved
along the way:

* `tri_sum`  : `∑_{r < p} (r + 1) = p(p+1)/2`  (Gauss's triangular number), and
* `sum_range_mul_split` : the Euclidean-division reindexing
  `∑_{n < p·M} f n = ∑_{j < M} ∑_{r < p} f (p·j + r)`.

All results are fully machine-checked: `0` `sorry`, `0` `axiom`, no `native_decide`.
-/

open Nat Finset

namespace LucasRowSum

/-! ## Gauss's triangular number -/

/-- The doubled triangular sum, free of natural-number division. -/
theorem tri_two (p : ℕ) : 2 * ∑ r ∈ Finset.range p, (r + 1) = p * (p + 1) := by
  induction p with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring

/-- **Gauss's triangular number.** `∑_{r < p} (r + 1) = 1 + 2 + ⋯ + p = p(p+1)/2`. -/
theorem tri_sum (p : ℕ) : ∑ r ∈ Finset.range p, (r + 1) = p * (p + 1) / 2 := by
  have h := tri_two p
  omega

/-! ## Euclidean-division reindexing of a range sum -/

/-- **Block reindexing.** Splitting `{0, …, p·M − 1}` by Euclidean division by `p`:
`∑_{n < p·M} f n = ∑_{j < M} ∑_{r < p} f (p·j + r)`.  Each `n` is uniquely `p·j + r`
with `j < M` and `r < p`. -/
theorem sum_range_mul_split (p M : ℕ) (f : ℕ → ℕ) :
    ∑ n ∈ Finset.range (p * M), f n
      = ∑ j ∈ Finset.range M, ∑ r ∈ Finset.range p, f (p * j + r) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

/-! ## The row-sum identity -/

/-- Total count of entries not divisible by `p` in the first `pᵐ` rows of Pascal's
triangle. -/
def rowSum (p m : ℕ) : ℕ := ∑ n ∈ Finset.range (p ^ m), FineTheorem.fineCount p n

/-- **Row-sum identity / fractal dimension.** For a prime `p`,
`∑_{n < pᵐ} fineCount p n = (p(p+1)/2)ᵐ`.

The base-`2` case is the Sierpiński count `3ᵐ`; the exponential rate
`log_p (p(p+1)/2)` is the box-counting dimension of the mod-`p` Pascal triangle. -/
theorem rowSum_eq {p : ℕ} (hp : p.Prime) (m : ℕ) :
    rowSum p m = (p * (p + 1) / 2) ^ m := by
  induction m with
  | zero => simp [rowSum, FineTheorem.fineCount_zero hp]
  | succ m ih =>
    have hstep : ∀ j, ∑ r ∈ Finset.range p, FineTheorem.fineCount p (p * j + r)
        = (p * (p + 1) / 2) * FineTheorem.fineCount p j := by
      intro j
      rw [Finset.sum_congr rfl
        (fun r hr => FineTheorem.fineCount_recursion hp (Finset.mem_range.mp hr) j),
        ← Finset.sum_mul, tri_sum]
    calc rowSum p (m + 1)
        = ∑ n ∈ Finset.range (p * p ^ m), FineTheorem.fineCount p n := by
            rw [rowSum, pow_succ']
      _ = ∑ j ∈ Finset.range (p ^ m), ∑ r ∈ Finset.range p,
            FineTheorem.fineCount p (p * j + r) :=
            sum_range_mul_split p (p ^ m) _
      _ = ∑ j ∈ Finset.range (p ^ m), (p * (p + 1) / 2) * FineTheorem.fineCount p j :=
            Finset.sum_congr rfl (fun j _ => hstep j)
      _ = (p * (p + 1) / 2) * ∑ j ∈ Finset.range (p ^ m), FineTheorem.fineCount p j := by
            rw [Finset.mul_sum]
      _ = (p * (p + 1) / 2) * rowSum p m := by rw [rowSum]
      _ = (p * (p + 1) / 2) * (p * (p + 1) / 2) ^ m := by rw [ih]
      _ = (p * (p + 1) / 2) ^ (m + 1) := by rw [pow_succ']

/-! ## Sanity checks -/

/-- `p = 2`, `m = 2`: the first `4` rows of Pascal's triangle contain `1+2+2+4 = 9 = 3²`
odd entries. -/
example : rowSum 2 2 = 9 := by decide

/-- `p = 2`, `m = 3`: `3³ = 27` odd entries in the first `8` rows. -/
example : rowSum 2 3 = 27 := by decide

/-- `p = 3`, `m = 1`: rows `0,1,2` have `1 + 2 + 3 = 6 = (3·4/2)¹` entries. -/
example : rowSum 3 1 = 6 := by decide

/-- `p = 3`, `m = 2`: `(3·4/2)² = 36`. -/
example : rowSum 3 2 = 36 := by decide

/-- The closed form, instantiated at `p = 2`, `m = 3`. -/
example : rowSum 2 3 = (2 * (2 + 1) / 2) ^ 3 := rowSum_eq (by norm_num) 3

end LucasRowSum
