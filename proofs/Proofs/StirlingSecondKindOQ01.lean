/-
Stirling Numbers of the Second Kind: the two-block column  S(n,2) = 2^(n-1) − 1

Source: Open question from the stirling-second-kind gallery family
Status: VERIFIED (0 axioms, 0 sorries)

`Nat.stirlingSecond n k` counts the partitions of an `n`-element set into exactly
`k` nonempty, unlabeled blocks. Mathlib (`Mathlib/Combinatorics/Enumerative/Stirling.lean`)
provides the Pascal-style recurrences together with the boundary columns

  S(n,n)   = 1                      (`stirlingSecond_self`)
  S(n+1,1) = 1                      (`stirlingSecond_one_right`)
  S(n+1,n) = C(n+1,2)               (`stirlingSecond_succ_self_left`)

but it does NOT record the classical closed form for the `k = 2` column. We fill
that gap:

      S(n, 2) = 2^(n-1) − 1     for n ≥ 2.

Combinatorial meaning: an unordered split of an `n`-set into two nonempty parts is
obtained from one of the `2^n` subsets by discarding the two improper subsets
(∅ and the whole set) and then identifying a part with its complement — giving
`(2^n − 2)/2 = 2^(n-1) − 1`. We prove it purely from the recurrence

      S(n+1, 2) = 2·S(n, 2) + S(n, 1) = 2·S(n, 2) + 1,

which is the inhomogeneous geometric recursion solved by `2^(n-1) − 1`.

We prove:
1. `stirlingSecond_two_add` — the shifted form S(n+2,2) = 2^(n+1) − 1 (induction-friendly)
2. `stirlingSecond_two`     — the textbook form S(n,2) = 2^(n-1) − 1 for n ≥ 2
3. `stirlingSecond_two_pos` — there is always at least one two-block partition (n ≥ 2)
-/

import Mathlib

open Nat

namespace StirlingSecondKindOQ01

/-- **Two-block column, shifted form.** The number of partitions of an
`(n+2)`-element set into two nonempty blocks is `2^(n+1) − 1`.

Proof by induction using the Pascal recurrence
`S(m+1,2) = 2·S(m,2) + S(m,1)` together with `S(m,1) = 1`. The recursion
`a(n+1) = 2·a(n) + 1` with `a(0) = 1` solves to `a(n) = 2^(n+1) − 1`. -/
theorem stirlingSecond_two_add (n : ℕ) :
    Nat.stirlingSecond (n + 2) 2 = 2 ^ (n + 1) - 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    -- Pascal recurrence specialised to the second column.
    have key : Nat.stirlingSecond (n + 1 + 2) 2
        = 2 * Nat.stirlingSecond (n + 2) 2 + Nat.stirlingSecond (n + 2) 1 :=
      Nat.stirlingSecond_succ_succ (n + 2) 1
    have hone : Nat.stirlingSecond (n + 2) 1 = 1 := Nat.stirlingSecond_one_right (n + 1)
    rw [key, ih, hone]
    have h1 : 1 ≤ 2 ^ (n + 1) := Nat.one_le_two_pow
    have h2 : 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by ring
    omega

/-- **Two-block column, textbook form.** For `n ≥ 2`, the number of partitions of
an `n`-element set into exactly two nonempty blocks is `2^(n-1) − 1`. -/
theorem stirlingSecond_two {n : ℕ} (hn : 2 ≤ n) :
    Nat.stirlingSecond n 2 = 2 ^ (n - 1) - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  -- `m + 2 - 1` is definitionally `m + 1`.
  exact stirlingSecond_two_add m

/-- **Existence of a two-block partition.** Any set with at least two elements can
be split into two nonempty blocks, i.e. `S(n,2) > 0` for `n ≥ 2`. -/
theorem stirlingSecond_two_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < Nat.stirlingSecond n 2 := by
  rw [stirlingSecond_two hn]
  have h2 : 2 ≤ 2 ^ (n - 1) := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

end StirlingSecondKindOQ01
