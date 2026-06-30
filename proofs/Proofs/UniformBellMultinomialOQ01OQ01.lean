/-
# The non-uniform bridge: `Multiset.bell` is a multinomial coefficient

The parent entry (`UniformBellMultinomialOQ01`) proved the *equal-block* bridge

    uniformBell m n · m! = multinomial (range m) (const n),

making precise that forgetting the order of the `m` equal-size blocks divides the
ordered count by `m!`.  Its first open question asks whether this bridge
generalises to blocks of **prescribed, non-uniform** sizes:

> Does `Multiset.bell m · ∏ (multiplicities)! = multinomial` of the size profile?

This file answers it affirmatively.  Fix a *size profile* `s : Multiset ℕ`
(the multiset of block sizes; `s.sum` is the size of the ground set).  Mathlib's
`Multiset.bell s` counts the **unordered** set-partitions of an `s.sum`-element
set whose block sizes are exactly `s`, and records the cornerstone

    bell s · (s.map (·!)).prod · ∏_{j ∈ s.toFinset.erase 0} (s.count j)!  =  s.sum!   (`Multiset.bell_mul_eq`)

The **ordered** count — the number of ways to drop `s.sum` labelled items into a
*sequence* of disjoint blocks of the prescribed sizes — is the multinomial
coefficient `multinomial s.toEnumFinset Prod.fst = s.sum! / (s.map (·!)).prod`
(here `s.toEnumFinset` indexes the `|s|` blocks, `Prod.fst` reads off each block's
size, so repeated sizes are kept distinct).  The bridge is then exactly the
statement that passing from ordered to unordered blocks divides by
`∏_j (s.count j)!`, the number of ways to permute the equal-size blocks among
themselves:

    bell s · ∏_{j ∈ s.toFinset.erase 0} (s.count j)!  =  multinomial s.toEnumFinset Prod.fst.

## Main results (0 sorry, 0 axiom, no `native_decide`)
* `sum_fst_toEnumFinset`           — `∑ i ∈ s.toEnumFinset, i.1 = s.sum`
* `prod_factorial_fst_toEnumFinset`— `∏ i ∈ s.toEnumFinset, (i.1)! = (s.map (·!)).prod`
* `factorialProd_mul_multinomial`  — `(s.map (·!)).prod · multinomial = s.sum!` (ordered count)
* `bell_mul_count_eq_multinomial`  — **the bridge** `bell s · ∏ count! = multinomial`
* `multinomial_eq_bell_mul_count`  — the bridge, multinomial-side
* `factorialProd_dvd_factorial_sum`— `(s.map (·!)).prod ∣ s.sum!`
* `bell_dvd_multinomial`           — `bell s ∣ multinomial s.toEnumFinset Prod.fst`
* `bell_mul_factorial_recovers_uniform` — specialises to the parent's `uniformBell · m!`
* concrete `bell {1,1,2} = 6`, `multinomial … = 12`

Fully machine-checked, no extra axioms, no `native_decide`.
-/

import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Multiset.Fintype
import Mathlib.Tactic

namespace UniformBellMultinomialOQ01OQ01

open Nat Finset

variable (s : Multiset ℕ)

/-- **Sum over the enumeration Finset.**  Reading off the size `i.1` of each of the
`|s|` indexed blocks and summing recovers the ground-set size `s.sum`. -/
theorem sum_fst_toEnumFinset : (∑ i ∈ s.toEnumFinset, i.1) = s.sum := by
  rw [← Multiset.sum_eq_sum_toEnumFinset]

/-- **Product of block-size factorials over the enumeration Finset** equals the
multiset product of factorials `(s.map (·!)).prod`.  This is the denominator of
the multinomial coefficient written in `toEnumFinset` form. -/
theorem prod_factorial_fst_toEnumFinset :
    (∏ i ∈ s.toEnumFinset, (i.1)!) = (s.map (fun j => j !)).prod := by
  conv_rhs => rw [← Multiset.map_toEnumFinset_fst s, Multiset.map_map]
  rfl

/-- **Ordered equal-block count, non-uniform version.**  The multinomial
coefficient indexed by `s.toEnumFinset` (one index per block, valued by its size)
is the number of ways to drop `s.sum` labelled items into an ordered sequence of
disjoint blocks of the prescribed sizes, and satisfies
`(s.map (·!)).prod · multinomial = s.sum!`. -/
theorem factorialProd_mul_multinomial :
    (s.map (fun j => j !)).prod * Nat.multinomial s.toEnumFinset Prod.fst = (s.sum)! := by
  have h := Nat.multinomial_spec s.toEnumFinset (Prod.fst)
  rw [prod_factorial_fst_toEnumFinset, sum_fst_toEnumFinset] at h
  exact h

/-- Positivity of the factorial denominator `0 < (s.map (·!)).prod`. -/
theorem factorialProd_pos : 0 < (s.map (fun j => j !)).prod := by
  apply Nat.pos_of_ne_zero
  apply Multiset.prod_ne_zero
  rw [Multiset.mem_map]
  rintro ⟨a, _, ha⟩
  exact Nat.factorial_ne_zero a ha

/-- **The non-uniform bridge** (answer to the open question).  For any size
profile `s`, the unordered partition count `bell s` times the number of
permutations of the equal-size blocks `∏_{j} (s.count j)!` equals the ordered
count, i.e. the multinomial coefficient of the profile:

    bell s · ∏_{j ∈ s.toFinset.erase 0} (s.count j)!  =  multinomial s.toEnumFinset Prod.fst.

Forgetting the order of equal-size blocks divides the ordered count by exactly
the product of the block-multiplicity factorials. -/
theorem bell_mul_count_eq_multinomial :
    Multiset.bell s * ∏ j ∈ s.toFinset.erase 0, (s.count j)!
      = Nat.multinomial s.toEnumFinset Prod.fst := by
  have hP : 0 < (s.map (fun j => j !)).prod := factorialProd_pos s
  refine Nat.eq_of_mul_eq_mul_left hP ?_
  calc
    (s.map (fun j => j !)).prod * (Multiset.bell s * ∏ j ∈ s.toFinset.erase 0, (s.count j)!)
        = Multiset.bell s * (s.map (fun j => j !)).prod
            * ∏ j ∈ s.toFinset.erase 0, (s.count j)! := by ring
    _ = (s.sum)! := Multiset.bell_mul_eq s
    _ = (s.map (fun j => j !)).prod * Nat.multinomial s.toEnumFinset Prod.fst :=
        (factorialProd_mul_multinomial s).symm

/-- The bridge, stated multinomial-side. -/
theorem multinomial_eq_bell_mul_count :
    Nat.multinomial s.toEnumFinset Prod.fst
      = Multiset.bell s * ∏ j ∈ s.toFinset.erase 0, (s.count j)! :=
  (bell_mul_count_eq_multinomial s).symm

/-- **Integrality of the multinomial closed form.**  The denominator
`(s.map (·!)).prod` divides `s.sum!`, witnessed by the multinomial coefficient. -/
theorem factorialProd_dvd_factorial_sum :
    (s.map (fun j => j !)).prod ∣ (s.sum)! :=
  ⟨Nat.multinomial s.toEnumFinset Prod.fst, (factorialProd_mul_multinomial s).symm⟩

/-- `bell s` divides the multinomial coefficient of its size profile: the
unordered count is a genuine divisor of the ordered count. -/
theorem bell_dvd_multinomial :
    Multiset.bell s ∣ Nat.multinomial s.toEnumFinset Prod.fst :=
  ⟨∏ j ∈ s.toFinset.erase 0, (s.count j)!, (bell_mul_count_eq_multinomial s).symm⟩

/-- **Positivity of `bell`.**  An ordered count is positive, hence so is the
unordered count: `0 < bell s`. -/
theorem bell_pos : 0 < Multiset.bell s := by
  rcases Nat.eq_zero_or_pos (Multiset.bell s) with h0 | h0
  · exfalso
    have h := bell_mul_count_eq_multinomial s
    rw [h0, zero_mul] at h
    exact (Nat.multinomial_pos s.toEnumFinset Prod.fst).ne' h.symm
  · exact h0

end UniformBellMultinomialOQ01OQ01

namespace UniformBellMultinomialOQ01OQ01

open Nat Finset

/-! ### Recovering the parent's equal-block bridge

When the size profile is constant, `s = replicate m n`, `Multiset.bell` is by
definition `Nat.uniformBell m n`, and for `n ≠ 0`, `m ≠ 0` the multiplicity
product collapses to the single factor `m!`.  The general bridge then specialises
to the parent's `uniformBell m n · m! = multinomial`. -/

/-- The multiplicity-factorial product collapses to `m!` for the constant profile
`replicate m n` with `n ≠ 0`, `m ≠ 0`. -/
theorem count_prod_replicate (m : ℕ) {n : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    ∏ j ∈ (Multiset.replicate m n).toFinset.erase 0, ((Multiset.replicate m n).count j)!
      = m ! := by
  rw [Multiset.toFinset_replicate, if_neg hm]
  rw [Finset.erase_eq_of_notMem (by simp only [Finset.mem_singleton]; omega)]
  rw [Finset.prod_singleton, Multiset.count_replicate_self]

/-- **The general bridge specialises to the parent's equal-block bridge.**  For a
constant size profile, `bell (replicate m n) · m! = multinomial`, i.e.
`uniformBell m n · m! = multinomial (replicate m n).toEnumFinset Prod.fst`. -/
theorem bell_mul_factorial_recovers_uniform (m : ℕ) {n : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) :
    Nat.uniformBell m n * m !
      = Nat.multinomial (Multiset.replicate m n).toEnumFinset Prod.fst := by
  have h := bell_mul_count_eq_multinomial (Multiset.replicate m n)
  rw [count_prod_replicate m hn hm] at h
  rw [← h]
  rfl

/-! ### Concrete instance: profile `{1, 1, 2}`

Partitions of a 4-element set into two singletons and one pair: choose the pair
`C(4,2) = 6`, the remaining two elements are forced singletons, so `bell = 6`.
The ordered (multinomial) count is `4!/(1!·1!·2!) = 12`, and the equal-block
multiplicity factor is `(count 1)! = 2! = 2`, giving `6 · 2 = 12`. -/

/-- `bell {1,1,2} = 6`. -/
theorem bell_one_one_two : Multiset.bell {1, 1, 2} = 6 := by decide

/-- The ordered count of the profile `{1,1,2}` is `12`. -/
theorem multinomial_one_one_two :
    Nat.multinomial ({1, 1, 2} : Multiset ℕ).toEnumFinset Prod.fst = 12 := by
  rw [multinomial_eq_bell_mul_count]
  decide

end UniformBellMultinomialOQ01OQ01
