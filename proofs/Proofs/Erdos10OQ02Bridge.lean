/-
# Erdős Problem #10 — OQ-02: bridge to the parent set definition

**Parent.** Erdős Problem #10 — sums of a prime and powers of 2.
**Open question (oq-02).** *Granville–Soundararajan (1998).* Is every odd
integer `n > 1` the sum of a prime and at most 3 powers of 2? (open)

## What this file adds

The parent entry (`Erdos10Problem.lean`) states the headline object as a set
```
sumPrimeAndTwoPows k = { n | ∃ p pows, p.Prime ∧ pows.card ≤ k
                              ∧ n = p + (pows.map (2 ^ ·)).sum }.
```
The OQ-02 stack instead works with the predicate
`IsPrimePlusKPowers k n` (`Erdos10OQ02.lean`), for which the popcount
characterization (`Erdos10OQ02Popcount.lean`) supplies an `O(log n)`
`Decidable` instance. The two say the same thing — they differ only by whether
the exponent multiset is inlined or factored through `RepWithAtMost`.

This file records that identification:

> `n ∈ sumPrimeAndTwoPows k ↔ IsPrimePlusKPowers k n`

transports the efficient decision procedure onto **membership in the parent
set**, and restates the Granville–Soundararajan odd conjecture directly against
`sumPrimeAndTwoPows 3`. The concrete witnesses (the smallest even integer
needing 3 powers, `906`) then close by `native_decide` *against the headline
definition*, not just the OQ-02 reformulation.

**Build status.** Registered in `Proofs.lean` and machine-checked under the
pinned Lean toolchain. Every step is definitional unfolding of the two
definitions plus the existing OQ-02 `Decidable` instance.
-/

import Proofs.Erdos10Problem
import Proofs.Erdos10OQ02Popcount

namespace Erdos10OQ02

/-- **Bridge.** The parent set `sumPrimeAndTwoPows k` and the OQ-02 predicate
`IsPrimePlusKPowers k` describe exactly the same numbers: both say
`n = p + (a sum of at most k powers of two)`. The proof is pure existential
reassociation — `powSum` is by definition `(·.map (2 ^ ·)).sum`. -/
theorem mem_sumPrimeAndTwoPows_iff (k n : ℕ) :
    n ∈ sumPrimeAndTwoPows k ↔ IsPrimePlusKPowers k n := by
  constructor
  · rintro ⟨p, pows, hp, hcard, hn⟩
    exact ⟨p, hp, powSum pows, ⟨pows, hcard, rfl⟩, hn⟩
  · rintro ⟨p, hp, m, ⟨s, hcard, hsum⟩, hn⟩
    refine ⟨p, s, hp, hcard, ?_⟩
    show n = p + powSum s
    rw [hn, ← hsum]

/-- Membership in the parent set `sumPrimeAndTwoPows k` is decidable in
`O(log n)`, inherited from the popcount decision procedure for
`IsPrimePlusKPowers` via the bridge. -/
instance decidableMemSumPrimeAndTwoPows (k n : ℕ) :
    Decidable (n ∈ sumPrimeAndTwoPows k) :=
  decidable_of_iff _ (mem_sumPrimeAndTwoPows_iff k n).symm

/-- Granville–Soundararajan (odd part) restated against the parent set: it is
equivalent to "every odd `n ≥ 3` lies in `sumPrimeAndTwoPows 3`". (Open.) -/
theorem granvilleSoundararajanOdd_iff :
    GranvilleSoundararajanOdd ↔
      ∀ n : ℕ, Odd n → 3 ≤ n → n ∈ sumPrimeAndTwoPows 3 := by
  unfold GranvilleSoundararajanOdd
  simp only [mem_sumPrimeAndTwoPows_iff]

/-! ## Concrete witnesses against the headline definition

These close by `native_decide` once the file is built, using the inherited
decidable membership instance. -/

-- `906` is the smallest even integer that is a prime plus `≤ 3` powers of two…
example : (906 : ℕ) ∈ sumPrimeAndTwoPows 3 := by native_decide

-- …but it is *not* a prime plus `≤ 2` powers of two (Granville–Soundararajan
-- even side; the `k = 3` in the conjecture is genuinely needed).
example : (906 : ℕ) ∉ sumPrimeAndTwoPows 2 := by native_decide

end Erdos10OQ02
