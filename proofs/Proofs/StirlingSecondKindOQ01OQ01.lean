/-
Stirling Numbers of the Second Kind: the three-block column  S(n,3) = (3^(n-1)+1)/2 − 2^(n-1)

Source: Open question from the stirling-second-kind / stirling-second-kind-oq-01 gallery family
Status: VERIFIED (0 axioms, 0 sorries)

`Nat.stirlingSecond n k` counts the partitions of an `n`-element set into exactly
`k` nonempty, unlabeled blocks. The gallery entry `stirling-second-kind-oq-01`
records the first nontrivial column

      S(n, 2) = 2^(n-1) − 1     (n ≥ 2),

obtained by solving the inhomogeneous geometric recurrence
`S(n+1,2) = 2·S(n,2) + 1`. This entry climbs one more rung of the
"column closed-forms" family and pins down the third column:

      S(n, 3) = (3^(n-1) + 1)/2 − 2^(n-1)     (n ≥ 3).

The Pascal recurrence specialised to the third column is the genuinely
inhomogeneous first-order recursion

      S(n+1, 3) = 3·S(n, 3) + S(n, 2) = 3·S(n, 3) + (2^(n-1) − 1),

a recurrence with two competing exponential modes (`3^n` and `2^n`). Solving it
gives the stated closed form. Unlike the `k = 2` column the answer carries a
genuine division by `2`; we sidestep `ℕ` truncated-division pitfalls by first
proving the *denominator-free* shifted identity

      2·S(m+3, 3) + 2^(m+3) = 3^(m+2) + 1                         (`stirlingSecond_three_add`)

purely by induction over the Pascal recurrence, and only then dividing to recover
the textbook form. The denominator-free statement is also the cleaner object: it
makes manifest that `3^(n-1) + 1` is always even (the right side is `2·(…)`),
which is exactly why the division in the closed form is exact.

We prove:
1. `stirlingSecond_three_add` — denominator-free shifted form 2·S(m+3,3)+2^(m+3)=3^(m+2)+1
2. `stirlingSecond_three`     — textbook form S(n,3) = (3^(n-1)+1)/2 − 2^(n-1) for n ≥ 3
3. `stirlingSecond_three_pos` — there is always at least one three-block partition (n ≥ 3)

The supporting two-block value `S(n,2) = 2^(n-1) − 1` is re-derived inline
(`aux_two`) so the file is self-contained and depends only on Mathlib.
-/

import Mathlib

open Nat

namespace StirlingSecondKindOQ01OQ01

/-- **Two-block column, shifted form** (re-derived inline from the Pascal
recurrence, mirroring `stirling-second-kind-oq-01`). The number of partitions of
an `(m+2)`-element set into two nonempty blocks is `2^(m+1) − 1`. Used as the
inhomogeneous driving term for the three-block recurrence. -/
private theorem aux_two (m : ℕ) :
    Nat.stirlingSecond (m + 2) 2 = 2 ^ (m + 1) - 1 := by
  induction m with
  | zero => decide
  | succ m ih =>
    have key : Nat.stirlingSecond (m + 1 + 2) 2
        = 2 * Nat.stirlingSecond (m + 2) 2 + Nat.stirlingSecond (m + 2) 1 :=
      Nat.stirlingSecond_succ_succ (m + 2) 1
    have hone : Nat.stirlingSecond (m + 2) 1 = 1 := Nat.stirlingSecond_one_right (m + 1)
    have h1 : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
    have h2 : 2 ^ (m + 1 + 1) = 2 * 2 ^ (m + 1) := by ring
    rw [key, ih, hone]
    omega

/-- **Three-block column, denominator-free shifted form.**

For every `m ≥ 0`,
$$2\cdot S(m+3,\,3) + 2^{\,m+3} = 3^{\,m+2} + 1.$$

Equivalently `S(m+3,3) = (3^(m+2)+1)/2 − 2^(m+2)`, but stated without division so the
induction stays inside `ℕ`. Proof by induction using the Pascal recurrence
`S((m+3)+1, 3) = 3·S(m+3,3) + S(m+3,2)` together with the two-block value
`S(m+3,2) = 2^(m+2) − 1`. The recursion `a(m+1) = 3·a(m) + 2^(m+2) − 1` is solved
by `a(m) = (3^(m+2)+1)/2 − 2^(m+2)`; in the doubled, subtraction-free form the
inductive step is linear and closed by `omega` once the powers are expanded. -/
theorem stirlingSecond_three_add (m : ℕ) :
    2 * Nat.stirlingSecond (m + 3) 3 + 2 ^ (m + 3) = 3 ^ (m + 2) + 1 := by
  induction m with
  | zero => decide
  | succ m ih =>
    -- Pascal recurrence specialised to the third column (k = 2):
    --   S(m+4, 3) = 3·S(m+3, 3) + S(m+3, 2).
    have key : Nat.stirlingSecond (m + 3 + 1) 3
        = 3 * Nat.stirlingSecond (m + 3) 3 + Nat.stirlingSecond (m + 3) 2 :=
      Nat.stirlingSecond_succ_succ (m + 3) 2
    -- The inhomogeneous term: the two-block value S(m+3, 2) = 2^(m+2) − 1.
    have hS2 : Nat.stirlingSecond (m + 3) 2 = 2 ^ (m + 2) - 1 := aux_two (m + 1)
    have hPpos : 1 ≤ 2 ^ (m + 2) := Nat.one_le_two_pow
    -- Expand the powers so `omega` can treat 2^(m+2) and 3^(m+2) as opaque atoms.
    have e2a : 2 ^ (m + 3) = 2 * 2 ^ (m + 2) := by ring
    have e2b : 2 ^ (m + 1 + 3) = 4 * 2 ^ (m + 2) := by ring
    have e3 : 3 ^ (m + 1 + 2) = 3 * 3 ^ (m + 2) := by ring
    rw [key, hS2]
    omega

/-- **Three-block column, textbook form.** For `n ≥ 3`, the number of partitions of
an `n`-element set into exactly three nonempty blocks is
$$S(n,3) = \frac{3^{\,n-1}+1}{2} - 2^{\,n-1}.$$
The division by `2` is exact because `3^(n-1)` is odd. -/
theorem stirlingSecond_three {n : ℕ} (hn : 3 ≤ n) :
    Nat.stirlingSecond n 3 = (3 ^ (n - 1) + 1) / 2 - 2 ^ (n - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h := stirlingSecond_three_add m
  have he : m + 3 - 1 = m + 2 := by omega
  have e2 : 2 ^ (m + 3) = 2 * 2 ^ (m + 2) := by ring
  rw [he]
  omega

/-- **Existence of a three-block partition.** Any set with at least three elements
can be split into three nonempty blocks, i.e. `S(n,3) > 0` for `n ≥ 3`.

Concretely `2·S(n,3) = 3^(n-1) + 1 − 2^n` and `3^(n-1) + 1 > 2^n` for `n ≥ 3`
(the `3^(n-1)` mode dominates), so `S(n,3) ≥ 1`. -/
theorem stirlingSecond_three_pos {n : ℕ} (hn : 3 ≤ n) :
    0 < Nat.stirlingSecond n 3 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have h := stirlingSecond_three_add m
  -- `2^(m+3) = 8·2^m ≤ 9·3^m = 3^(m+2)`, so the doubled value `3^(m+2)+1 − 2^(m+3)`
  -- is at least `1`, giving `S(m+3,3) ≥ 1`.
  have hdom : 2 ^ (m + 3) ≤ 3 ^ (m + 2) := by
    have hle : 2 ^ m ≤ 3 ^ m := Nat.pow_le_pow_left (by norm_num) m
    have e2 : 2 ^ (m + 3) = 8 * 2 ^ m := by ring
    have e3 : 3 ^ (m + 2) = 9 * 3 ^ m := by ring
    omega
  omega

end StirlingSecondKindOQ01OQ01
