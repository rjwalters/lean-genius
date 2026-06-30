/-
# Erdős Problem #10 — Open Question 02: the popcount decision procedure

**Parent.** Erdős Problem #10 — sums of a prime and powers of 2.

**Open question (oq-02).** *Granville–Soundararajan (1998).* Is every odd
integer `n > 1` the sum of a prime and **at most 3** powers of 2? (open)

## What this file adds

`Erdos10OQ02.lean` (S3) proved the reduction lemma (`≤ k` powers ⟺ `≤ k`
*distinct* powers). `Erdos10OQ02Decidable.lean` (S4) bounded the exponents
(`a < 2^a ≤ n`) and the prime (`p ≤ n`), giving decidability **in principle**
via a `Finset.range (n+1)` powerset search — but that search has `2^(n+1)`
candidates, so it is *not* feasible for `native_decide` on the witnesses (the
smallest even integer needing 3 powers is `906`).

This file supplies the **efficient** decision procedure. The minimal number of
*distinct* powers of two summing to `m` is exactly the binary popcount of `m`,
i.e. the length of `Nat.bitIndices m`. The non-trivial direction is the
**uniqueness of the binary representation**, which Mathlib provides as
`Finset.toFinset_bitIndices_twoPowSum` (the inverse leg of the bijection
`Finset.equivBitIndices : ℕ ≃ Finset ℕ`). The result is the clean
characterization

> `RepWithAtMost k n ↔ (Nat.bitIndices n).length ≤ k`

whose right-hand side is `O(log n)` to evaluate. From it we derive genuine
`Decidable` instances for both `RepWithAtMost k` and `IsPrimePlusKPowers k`
(the latter via the S4 prime-side bound, a search over `p ∈ range (n+1)`), and
discharge concrete witnesses by `native_decide` — including the fact that `906`
is a prime plus `≤ 3` powers but **not** a prime plus `≤ 2` powers.

This fills the gap recorded in the problem metadata ("no `Decidable` instance
wired for `sumPrimeAndTwoPows` / `IsPrimePlusKPowers`") with the
computationally usable instance, rather than the in-principle powerset one.

**Build status.** Registered in `Proofs.lean` and machine-checked under the
pinned v4.26 toolchain. The decision facts are additionally validated
independently in `research/problems/erdos-10-oq-02/verify_decidable_membership.py`
(`RepWithAtMost k m ⟺ popcount m ≤ k`; `IsPrimePlusKPowers 2 906` is false,
`IsPrimePlusKPowers 3 906` is true; `906` is the smallest even integer in
`S₃ ∖ S₂`).

## References

- Granville, A.; Soundararajan, K. (1998). *A binary additive problem of Erdős
  and the order of `2 mod p²`.* Ramanujan J. 2, 283–298.
- Nelson, P. *Nat.bitIndices* (Mathlib, `Mathlib/Data/Nat/BitIndices.lean`) and
  *Finset.equivBitIndices* (`Mathlib/Combinatorics/Colex.lean`).
-/

import Mathlib.Combinatorics.Colex
import Mathlib.Tactic
import Proofs.Erdos10OQ02
import Proofs.Erdos10OQ02Decidable

namespace Erdos10OQ02

/-! ## Part VIII: The popcount characterization

`RepWithAtMost k n` holds iff the number of set bits of `n` (the length of
`Nat.bitIndices n`) is at most `k`. -/

/-- **Popcount characterization.** `n` is a sum of at most `k` powers of two iff
its binary popcount `(Nat.bitIndices n).length` is at most `k`.

Forward: by the S3 reduction lemma a representation can be taken with a `Nodup`
exponent multiset `s`; turning `s` into a `Finset` and applying the uniqueness
of the binary expansion (`Finset.toFinset_bitIndices_twoPowSum`) identifies that
`Finset` with `(Nat.bitIndices n).toFinset`, so `(Nat.bitIndices n).length =
s.card ≤ k`. Reverse: `Nat.bitIndices n` is itself a representation of `n` with
exactly `(Nat.bitIndices n).length` (distinct) powers. -/
theorem repWithAtMost_iff_bitIndices_length (k n : ℕ) :
    RepWithAtMost k n ↔ (Nat.bitIndices n).length ≤ k := by
  constructor
  · intro h
    obtain ⟨s, hnd, hcard, hsum⟩ := (repWithAtMost_iff_repDistinct k n).mp h
    -- The Finset of exponents has the same `∑ 2^i` as `powSum s = n`.
    have hFsum : ∑ i ∈ s.toFinset, (2 : ℕ) ^ i = n := by
      have hval : ∑ i ∈ s.toFinset, (2 : ℕ) ^ i = powSum s := by
        rw [Finset.sum_eq_multiset_sum, Multiset.toFinset_val, hnd.dedup]
        rfl
      rw [hval, hsum]
    -- Uniqueness of the binary representation pins the Finset.
    have hEq : (Nat.bitIndices n).toFinset = s.toFinset := by
      have huniq := Finset.toFinset_bitIndices_twoPowSum s.toFinset
      rwa [hFsum] at huniq
    have hlen : (Nat.bitIndices n).length = s.toFinset.card := by
      rw [← List.toFinset_card_of_nodup (@Nat.bitIndices_sorted n).nodup, hEq]
    rw [hlen, Multiset.toFinset_card_of_nodup hnd]
    exact hcard
  · intro h
    refine ⟨(Nat.bitIndices n : Multiset ℕ), ?_, ?_⟩
    · rwa [Multiset.coe_card]
    · show ((Nat.bitIndices n : Multiset ℕ).map (fun i => 2 ^ i)).sum = n
      rw [Multiset.map_coe, Multiset.sum_coe]
      exact Nat.twoPowSum_bitIndices n

/-! ## Part IX: Decidable instances

The popcount characterization makes `RepWithAtMost k` decidable in `O(log n)`,
and combining it with the S4 prime-side bound makes `IsPrimePlusKPowers k`
decidable by a search over `p ∈ Finset.range (n+1)`. -/

/-- Efficient `Decidable` instance for `RepWithAtMost`, via the popcount
characterization (`O(log n)`, contrast the in-principle powerset search). -/
instance decidableRepWithAtMost (k n : ℕ) : Decidable (RepWithAtMost k n) :=
  decidable_of_iff _ (repWithAtMost_iff_bitIndices_length k n).symm

/-- `IsPrimePlusKPowers` as a search over primes `p ∈ Finset.range (n+1)` with a
`≤ k`-power representation of `n - p`. This is the decidable form; the prime
bound comes from `isPrimePlusKPowers_bounded` (S4). -/
theorem isPrimePlusKPowers_iff_range (k n : ℕ) :
    IsPrimePlusKPowers k n ↔
      ∃ p ∈ Finset.range (n + 1), p.Prime ∧ RepWithAtMost k (n - p) := by
  rw [isPrimePlusKPowers_bounded]
  constructor
  · rintro ⟨p, hpn, hp, hr⟩
    exact ⟨p, Finset.mem_range.mpr (by omega), hp, hr⟩
  · rintro ⟨p, hpr, hp, hr⟩
    have := Finset.mem_range.mp hpr
    exact ⟨p, by omega, hp, hr⟩

/-- `Decidable` instance for `IsPrimePlusKPowers`, by the finite prime search. -/
instance decidableIsPrimePlusKPowers (k n : ℕ) : Decidable (IsPrimePlusKPowers k n) :=
  decidable_of_iff _ (isPrimePlusKPowers_iff_range k n).symm

/-! ## Part X: Concrete witnesses

These close by `native_decide` once the file is built. Each is independently
validated in `verify_decidable_membership.py`. -/

-- `8 = 2^3` needs a single power.
example : RepWithAtMost 1 8 := by native_decide

-- The empty sum represents `0`.
example : RepWithAtMost 0 0 := by native_decide

-- `7 = 111₂` has popcount 3, so it is not a sum of `≤ 2` powers of two.
example : ¬ RepWithAtMost 2 7 := by native_decide

-- `906` is the smallest even integer that is a prime plus `≤ 3` powers of two
-- but not a prime plus `≤ 2` powers (Granville–Soundararajan even side).
example : ¬ IsPrimePlusKPowers 2 906 := by native_decide
example : IsPrimePlusKPowers 3 906 := by native_decide

#check @repWithAtMost_iff_bitIndices_length
#check @isPrimePlusKPowers_iff_range
#check (inferInstance : Decidable (RepWithAtMost 3 906))
#check (inferInstance : Decidable (IsPrimePlusKPowers 3 906))

end Erdos10OQ02
