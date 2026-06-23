/-
# Uniform Bell numbers and the multinomial structure of equal-block partitions

`Nat.uniformBell m n` counts the partitions of an `m·n`-element set into `m`
*unordered* blocks, each of size `n`.  Pinned Mathlib defines it as
`Multiset.bell (Multiset.replicate m n)` and records the cornerstone structural
identity

    uniformBell m n · (n!)^m · m! = (m·n)!            (`Nat.uniformBell_mul_eq`)

together with its division form
`uniformBell m n = (m·n)! / ((n!)^m · m!)` (`Nat.uniformBell_eq_div`).  This file
re-exports those two cornerstones and then adds the material the gallery — and
Mathlib — lack:

* **Ordered vs. unordered blocks.**  The number of ways to split `m·n` labelled
  items into `m` *ordered* blocks of size `n` is the multinomial coefficient
  `multinomial (range m) (fun _ => n)`.  We prove the ordered count
      (n!)^m · multinomial (range m) (const n) = (m·n)!
  (`multinomial_range_const`) and the bridge
      uniformBell m n · m! = multinomial (range m) (const n)
  (`uniformBell_mul_factorial`), making precise that "forgetting the order of the
  `m` equal blocks" divides the ordered count by exactly `m!`.
* **Positivity** `0 < uniformBell m n` — an equal-block partition always exists.
* **A factorial divisibility corollary** `(n!)^m · m! ∣ (m·n)!`, the integrality
  statement underlying the closed form.
* **Concrete instances** `uniformBell 2 2 = 3`, `uniformBell 2 3 = 10`,
  `uniformBell 3 2 = 15`, checked against the closed product form.

## Main results (0 sorry, 0 axiom, no `native_decide`)
* `uniformBell_mul_eq'`        — `uniformBell m n · (n!)^m · m! = (m·n)!` (re-export)
* `uniformBell_eq_div'`        — division form (re-export)
* `multinomial_range_const`    — `(n!)^m · multinomial (range m) (const n) = (m·n)!`
* `uniformBell_mul_factorial`  — `uniformBell m n · m! = multinomial (range m) (const n)`
* `uniformBell_pos`            — `0 < uniformBell m n`
* `factorial_pow_mul_factorial_dvd` — `(n!)^m · m! ∣ (m·n)!`
* `uniformBell_two_two`, `uniformBell_two_three`, `uniformBell_three_two`

Fully machine-checked, no extra axioms, no `native_decide`.
-/

import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic

namespace UniformBellMultinomialOQ01

open Nat Finset

/-- **Re-export of the cornerstone uniform-Bell identity.**  Splitting an
`m·n`-element set into `m` unordered blocks of size `n` satisfies
`uniformBell m n · (n!)^m · m! = (m·n)!`. -/
theorem uniformBell_mul_eq' (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    uniformBell m n * n ! ^ m * m ! = (m * n)! :=
  Nat.uniformBell_mul_eq m hn

/-- **Re-export of the division form** `uniformBell m n = (m·n)! / ((n!)^m · m!)`. -/
theorem uniformBell_eq_div' (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    uniformBell m n = (m * n)! / (n ! ^ m * m !) :=
  Nat.uniformBell_eq_div m hn

/-- **Ordered equal-block count.**  The number of ways to split `m·n` labelled
items into a sequence of `m` *ordered* blocks of size `n` is the multinomial
coefficient `multinomial (range m) (const n)`, and it satisfies
`(n!)^m · multinomial (range m) (const n) = (m·n)!`.  This is the "ordered"
analogue of `uniformBell_mul_eq`. -/
theorem multinomial_range_const (m n : ℕ) :
    n ! ^ m * Nat.multinomial (Finset.range m) (fun _ => n) = (m * n)! := by
  have h := Nat.multinomial_spec (Finset.range m) (fun _ => n)
  simpa [Finset.prod_const, Finset.sum_const, Finset.card_range, smul_eq_mul] using h

/-- **The unordered/ordered bridge.**  Forgetting the order of the `m` equal-size
blocks divides the ordered count by exactly `m!`:
`uniformBell m n · m! = multinomial (range m) (const n)`. -/
theorem uniformBell_mul_factorial (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    uniformBell m n * m ! = Nat.multinomial (Finset.range m) (fun _ => n) := by
  have hpos : 0 < n ! ^ m := pow_pos (Nat.factorial_pos n) m
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc n ! ^ m * (uniformBell m n * m !)
      = uniformBell m n * n ! ^ m * m ! := by ring
    _ = (m * n)! := Nat.uniformBell_mul_eq m hn
    _ = n ! ^ m * Nat.multinomial (Finset.range m) (fun _ => n) :=
        (multinomial_range_const m n).symm

/-- **Positivity.**  An equal-block partition always exists, so `0 < uniformBell m n`. -/
theorem uniformBell_pos (m n : ℕ) : 0 < uniformBell m n := by
  rcases Nat.eq_zero_or_pos (uniformBell m n) with h0 | h0
  · exfalso
    rcases Nat.eq_zero_or_pos n with hn | hn
    · rw [hn, Nat.uniformBell_zero_right] at h0
      exact one_ne_zero h0
    · have h := Nat.uniformBell_mul_eq m hn.ne'
      rw [h0, zero_mul, zero_mul] at h
      exact Nat.factorial_ne_zero _ h.symm
  · exact h0

/-- **Factorial divisibility corollary.**  The denominator of the closed form
divides the factorial: `(n!)^m · m! ∣ (m·n)!`.  This is the integrality statement
that makes `uniformBell_eq_div` an honest natural number. -/
theorem factorial_pow_mul_factorial_dvd (m : ℕ) {n : ℕ} (hn : n ≠ 0) :
    n ! ^ m * m ! ∣ (m * n)! :=
  ⟨uniformBell m n, by rw [← Nat.uniformBell_mul_eq m hn]; ring⟩

/-- `uniformBell 2 2 = 3`: the three pairings of a 4-element set into two pairs. -/
theorem uniformBell_two_two : uniformBell 2 2 = 3 := by
  simp only [Nat.uniformBell_eq, Finset.prod_range_succ, Finset.prod_range_zero]
  decide

/-- `uniformBell 2 3 = 10`: splits of a 6-element set into two triples. -/
theorem uniformBell_two_three : uniformBell 2 3 = 10 := by
  simp only [Nat.uniformBell_eq, Finset.prod_range_succ, Finset.prod_range_zero]
  decide

/-- `uniformBell 3 2 = 15`: splits of a 6-element set into three pairs. -/
theorem uniformBell_three_two : uniformBell 3 2 = 15 := by
  simp only [Nat.uniformBell_eq, Finset.prod_range_succ, Finset.prod_range_zero]
  decide

end UniformBellMultinomialOQ01
