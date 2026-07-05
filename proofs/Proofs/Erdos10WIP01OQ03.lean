/-
# Erdős Problem #10 — WIP OQ-03 — The covering-congruence reduction for `Sₖ`

Erdős Problem #10 asks for a finite `k` with every large integer a prime plus at most `k`
powers of two.  Writing `Sₖ = { n | IsPrimePlusKPowers k n }`, the seeker's open question
asks to *formalize the covering-congruence construction giving infinitely many even integers
outside `S₃`*.  This file supplies the **verified reduction skeleton** for that method and
demonstrates it end-to-end at level `k = 1`.

## What the covering method actually needs (`not_isPrimePlusKPowers_iff`)

The sibling thread `Erdos10WIP01` proved the popcount characterization
`isPrimePlusKPowers_iff_popcount`:
`IsPrimePlusKPowers k n ↔ ∃ prime p ≤ n, popcount (n − p) ≤ k`, where
`popcount m = (Nat.bitIndices m).length` is the number of binary `1`-bits (equivalently, the
minimal number of powers of two summing to `m`).  Re-indexing the existential by the *offset*
`w = n − p` (so `p = n − w` is the candidate prime and `w` is the "sum of ≤ k powers" part)
turns non-membership into a clean universal statement:

>  `¬ IsPrimePlusKPowers k n  ↔  ∀ w ≤ n, popcount w ≤ k → ¬ (n − w).Prime.`

This is exactly the object a covering system must control: to place `n` outside `Sₖ` one must
show that **for every offset `w ≤ n` with at most `k` binary ones, the difference `n − w` is
composite** (or `≤ 1`).  A covering system does this by supplying, for each such `w`, a small
prime dividing `n − w`.

## The level-1 demonstration and the barrier at `k ≥ 2`

At `k = 1` the offsets `w` with `popcount w ≤ 1` are exactly `0` and the single powers `2^a`
(`eq_two_pow_of_pos_of_popcount_le_one`).  For an *even* `n > 242` in Erdős's explicit
covering residue class (built in `Erdos10OQ01Incomplete01` / `Erdos10Incomplete01OQ02`), the
offset `w = 0` gives `n` itself (even, `> 2`, composite), and each `w = 2^a` gives `n − 2^a`,
which the covering obstruction `prime_forced_small` forces to be composite (any prime here is
one of the six *odd* covering primes, whence `2^a` is odd, `a = 0`, `n = p + 1 ≤ 242`, absurd).
So the reduction reproduces, natively in the canonical `IsPrimePlusKPowers` predicate,
**infinitely many even integers outside `S₁`** (`infinite_even_not_isPrimePlusKPowers_one`).

For `k ≥ 2` the offset set `{ w : popcount w ≤ k }` contains genuine *sums* of powers, e.g.
`w = 2^a + 2^b + 2^c` for `k = 3`.  Erdős's `k = 1` covering only controls single powers:
`n ≡ 2^a (mod q)` on each covering class forces `q ∣ n − 2^a`, but says nothing about
`n − (2^a + 2^b + 2^c)`.  Killing every three-bit offset simultaneously is a strictly harder
construction — this is exactly the regime of Crocker's 1971 theorem (`k = 2`) and its
unresolved extensions (`k = 3`), which the parent files (`Erdos10OQ01`) can only axiomatize.
The reduction below isolates precisely this missing input: an even-`S₃` covering must exhibit,
for each `n` in an arithmetic progression and each `≤ 3`-bit offset `w`, a proper prime divisor
of `n − w`.  Building such a system is out of reach of the elementary `k = 1` covering and is
recorded as the open next step.

## Contents (0 axioms, 0 sorries)

* `not_isPrimePlusKPowers_iff` — the covering-method reduction, for **every** `k`.
* `eq_two_pow_of_pos_of_popcount_le_one` — the `k = 1` offsets are `0` and the powers `2^a`.
* `not_isPrimePlusKPowers_of_even` — even-integer form (the `w = 0` offset is automatic).
* `not_isPrimePlusKPowers_one_of_even_covering` — even `n > 242` in the covering class ∉ `S₁`.
* `infinite_even_not_isPrimePlusKPowers_one` — infinitely many even integers ∉ `S₁`.

## References
- Erdős, P. (1950). "On integers of the form `2^k + p` and some related problems."
  Summa Brasiliensis Mathematicae 2, 113–123.
- Crocker, R. (1971). "On the sum of a prime and of two powers of two."
  Pacific J. Math. 36, 103–107.
- [erdosproblems.com/10](https://www.erdosproblems.com/10)
-/

import Proofs.Erdos10WIP01
import Proofs.Erdos10Incomplete01OQ02

namespace Erdos10WIP01OQ03

open Erdos10OQ02 Erdos10WIP01 Erdos10OQ01Incomplete01 Erdos10Incomplete01OQ02

/-! ## Part I: The covering-method reduction (all `k`)

Non-membership in `Sₖ`, re-indexed from "no prime `p` with small `popcount (n − p)`" into
"every small-popcount offset `w` leaves `n − w` composite" — the exact target of a covering
system. -/

/-- **Covering-method reduction.**  `n` is *not* a prime plus at most `k` powers of two iff for
every offset `w ≤ n` whose binary popcount is at most `k`, the difference `n − w` fails to be
prime.  This is `isPrimePlusKPowers_iff_popcount` with the existential re-indexed by the offset
`w = n − p`; it holds for every `k`, and phrases the goal a covering construction must meet. -/
theorem not_isPrimePlusKPowers_iff (k n : ℕ) :
    ¬ IsPrimePlusKPowers k n ↔ ∀ w, w ≤ n → popcount w ≤ k → ¬ (n - w).Prime := by
  rw [isPrimePlusKPowers_iff_popcount]
  constructor
  · intro h w hwn hwc hp
    apply h
    refine ⟨n - w, hp, Nat.sub_le n w, ?_⟩
    rw [Nat.sub_sub_self hwn]
    exact hwc
  · rintro h ⟨p, hp, hpn, hpc⟩
    have hcontra := h (n - p) (Nat.sub_le n p) hpc
    rw [Nat.sub_sub_self hpn] at hcontra
    exact hcontra hp

/-- At `k = 1`, a positive offset of popcount `≤ 1` is a single power of two.  (`popcount w ≤ 1`
means `w` is a sum of at most one power of two; positivity rules out the empty sum.) -/
theorem eq_two_pow_of_pos_of_popcount_le_one {w : ℕ} (hw : 0 < w) (h : popcount w ≤ 1) :
    ∃ a, w = 2 ^ a := by
  rw [popcount_le_iff] at h
  obtain ⟨s, hcard, hsum⟩ := h
  rcases Nat.eq_zero_or_pos s.card with hc0 | hc1
  · rw [Multiset.card_eq_zero] at hc0
    subst hc0
    rw [powSum_zero] at hsum
    omega
  · have hc : s.card = 1 := by omega
    obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp hc
    refine ⟨a, ?_⟩
    rw [← hsum]
    simp [powSum]

/-! ## Part II: The even-integer form

For even `n > 2` the offset `w = 0` is free (it yields `n`, which is even and `> 2`, hence
composite), so a covering construction only has to handle the *positive* offsets. -/

/-- **Even-integer reduction.**  An even `n > 2` avoids `Sₖ` as soon as every *positive* offset
`w ≤ n` of popcount `≤ k` leaves `n − w` non-prime; the `w = 0` case is automatic because an
even number exceeding `2` is composite. -/
theorem not_isPrimePlusKPowers_of_even {k n : ℕ} (he : n % 2 = 0) (hn : 2 < n)
    (h : ∀ w, 0 < w → w ≤ n → popcount w ≤ k → ¬ (n - w).Prime) :
    ¬ IsPrimePlusKPowers k n := by
  rw [not_isPrimePlusKPowers_iff]
  intro w hwn hwc
  rcases Nat.eq_zero_or_pos w with hw0 | hwpos
  · subst hw0
    simp only [Nat.sub_zero]
    intro hp
    have h2 : (2 : ℕ) ∣ n := Nat.dvd_of_mod_eq_zero he
    rcases hp.eq_one_or_self_of_dvd 2 h2 with h1 | h1
    · norm_num at h1
    · omega
  · exact h w hwpos hwn hwc

/-! ## Part III: Level-1 demonstration and infinitude

Instantiating the reduction at `k = 1` against Erdős's explicit covering system reproduces the
classical even-`S₁` exclusion — now stated for the canonical `IsPrimePlusKPowers` predicate. -/

/-- **Even `S₁` exclusion via the covering system.**  An even `n > 242` lying in Erdős's CRT
residue class is not a prime plus a single power of two.  Proof through the reduction: the only
positive offsets of popcount `≤ 1` are the powers `2^a`, and for each, `n − 2^a` prime would
force (by `prime_forced_small`) an *odd* covering prime `p ≤ 241`, so `2^a = n − p` is odd,
`a = 0`, and `n = p + 1 ≤ 242` — contradicting `n > 242`. -/
theorem not_isPrimePlusKPowers_one_of_even_covering {n : ℕ}
    (h3 : n % 3 = 1) (h7 : n % 7 = 1) (h5 : n % 5 = 2)
    (h17 : n % 17 = 8) (h13 : n % 13 = 11) (h241 : n % 241 = 121)
    (heven : n % 2 = 0) (hbig : 242 < n) :
    ¬ IsPrimePlusKPowers 1 n := by
  refine not_isPrimePlusKPowers_of_even heven (by omega) ?_
  intro w hwpos hwn hwc hp
  obtain ⟨a, rfl⟩ := eq_two_pow_of_pos_of_popcount_le_one hwpos hwc
  set p := n - 2 ^ a with hpdef
  have hrep : n = 2 ^ a + p := by omega
  have hpc : p ∈ coveringPrimes := prime_forced_small h3 h7 h5 h17 h13 h241 hp hrep
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (coveringPrimes_odd hpc)
  have hple : p ≤ 241 := coveringPrimes_le hpc
  have hpow : 2 ^ a % 2 = 1 := by omega
  have ha0 : a = 0 := by
    by_contra ha
    have : Even (2 ^ a) := by rw [Nat.even_pow]; exact ⟨by decide, ha⟩
    rw [Nat.even_iff] at this
    omega
  subst ha0
  simp only [pow_zero] at hrep
  omega

/-- **Main result.**  There are infinitely many *even* integers that are not a prime plus a
single power of two, exhibited by the explicit even progression
`family s = 2036812 + 11184810 · s`.  This is the classical Erdős (1950) even-`S₁` exclusion,
recast in the `IsPrimePlusKPowers` predicate and reached natively through the covering-method
reduction of Part I. -/
theorem infinite_even_not_isPrimePlusKPowers_one :
    {n : ℕ | n % 2 = 0 ∧ ¬ IsPrimePlusKPowers 1 n}.Infinite := by
  have hinj : Function.Injective family := by
    intro a b hab
    unfold family at hab
    omega
  have hmem : ∀ s : ℕ, family s ∈ {n : ℕ | n % 2 = 0 ∧ ¬ IsPrimePlusKPowers 1 n} := by
    intro s
    obtain ⟨h3, h7, h5, h17, h13, h241, heven, hbig⟩ := family_props s
    exact ⟨heven,
      not_isPrimePlusKPowers_one_of_even_covering h3 h7 h5 h17 h13 h241 heven hbig⟩
  exact Set.infinite_of_injective_forall_mem hinj hmem

#check @not_isPrimePlusKPowers_iff
#check @not_isPrimePlusKPowers_of_even
#check @infinite_even_not_isPrimePlusKPowers_one

end Erdos10WIP01OQ03
