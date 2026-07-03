/-
# Erdős Problem #10 — Incomplete 01 — OQ-02
## Bridging the covering obstruction to the headline set `sumPrimeAndTwoPows 1`

Erdős Problem #10 asks for a finite `k` such that every (sufficiently large) integer is a
prime plus at most `k` powers of `2`.  The parent file `Erdos10Incomplete01.lean` defines the
canonical representation family

  `sumPrimeAndTwoPows k = { n | ∃ p (pows : Multiset ℕ),
                                p.Prime ∧ pows.card ≤ k ∧ n = p + (pows.map (2^·)).sum }`,

and pins down its two smallest levels exactly (`mem_zero_iff`, `mem_one_iff`).  The sibling
file `Erdos10OQ01Incomplete01.lean` proves the elementary **covering-congruence obstruction**
`prime_forced_small`: for `n` in an explicit CRT residue class, *every* representation
`n = 2^a + p` with `p` prime forces `p` to be one of the six covering primes
`{3, 5, 7, 13, 17, 241}`.

This file connects the two.  It restates `prime_forced_small` directly against membership in
`sumPrimeAndTwoPows 1` (`mem_one_forced`), and then extracts an **explicit infinite family of
integers that lie outside level 1** entirely (`infinite_not_mem_one`).

## The key parity observation

The six covering primes are all **odd**.  So if `n` is *even*, a representation
`n = p + 2^a` with `p` one of the covering primes forces `2^a` to be odd, i.e. `a = 0`, giving
`n = p + 1 ≤ 242`.  Consequently **every even integer `> 242` in the covering residue class is
not a prime plus a single power of two.**  The even sub-progression

  `n(s) = 2036812 + 11184810 · s`   (`11184810 = 2 · 3 · 5 · 7 · 13 · 17 · 241`)

is an explicit infinite family of such integers.  This sharpens the sibling file's
`infinitely_many_forced` (which only bounded the prime, still leaving those six values open)
into an unconditional exclusion from `sumPrimeAndTwoPows 1`, with **no axioms and no sorries**.

## References
- Erdős, P. (1950). "On integers of the form `2^k + p` and some related problems."
  Summa Brasiliensis Mathematicae 2, 113–123.
- [erdosproblems.com/10](https://www.erdosproblems.com/10)
-/

import Proofs.Erdos10Incomplete01
import Proofs.Erdos10OQ01Incomplete01

namespace Erdos10Incomplete01OQ02

open Erdos10Incomplete01 Erdos10OQ01Incomplete01

/-! ## Elementary facts about the covering primes -/

/-- Each of the six covering primes `{3, 5, 7, 13, 17, 241}` is odd. -/
theorem coveringPrimes_odd {q : ℕ} (hq : q ∈ coveringPrimes) : Odd q := by
  fin_cases hq <;> decide

/-- Each of the six covering primes is at most `241`. -/
theorem coveringPrimes_le {q : ℕ} (hq : q ∈ coveringPrimes) : q ≤ 241 := by
  fin_cases hq <;> decide

/-! ## Bridge: `prime_forced_small` restated against `sumPrimeAndTwoPows 1` -/

/-- **Bridge restatement.** For `n` in the covering-system residue class, membership in the
headline set `sumPrimeAndTwoPows 1` forces `n` to be prime, or of the shape `2^a + q` with `q`
one of the six covering primes.  This is `prime_forced_small` transported onto the parent set
via `mem_one_iff`. -/
theorem mem_one_forced {n : ℕ}
    (h3 : n % 3 = 1) (h7 : n % 7 = 1) (h5 : n % 5 = 2)
    (h17 : n % 17 = 8) (h13 : n % 13 = 11) (h241 : n % 241 = 121)
    (hn : n ∈ sumPrimeAndTwoPows 1) :
    n.Prime ∨ ∃ a q, q ∈ coveringPrimes ∧ n = 2 ^ a + q := by
  rw [mem_one_iff] at hn
  rcases hn with hp | ⟨p, a, hp, hrep⟩
  · exact Or.inl hp
  · have hrep' : n = 2 ^ a + p := by omega
    exact Or.inr ⟨a, p, prime_forced_small h3 h7 h5 h17 h13 h241 hp hrep', hrep'⟩

/-! ## The parity refinement: even numbers in the class are outside level 1 -/

/-- **Core exclusion.** An *even* integer `n > 242` lying in the covering residue class is not a
prime plus a single power of two.  Indeed `n` is even and `> 2`, hence composite (not prime);
and any representation `n = p + 2^a` would force `p` to be an odd covering prime, so `2^a` would
be odd, i.e. `a = 0` and `n = p + 1 ≤ 242`, contradicting `n > 242`. -/
theorem not_mem_one_of_even {n : ℕ}
    (h3 : n % 3 = 1) (h7 : n % 7 = 1) (h5 : n % 5 = 2)
    (h17 : n % 17 = 8) (h13 : n % 13 = 11) (h241 : n % 241 = 121)
    (heven : n % 2 = 0) (hbig : 242 < n) :
    n ∉ sumPrimeAndTwoPows 1 := by
  intro hn
  rw [mem_one_iff] at hn
  rcases hn with hp | ⟨p, a, hp, hrep⟩
  · -- `n` even and `> 2` cannot be prime.
    have h2 : (2 : ℕ) ∣ n := Nat.dvd_of_mod_eq_zero heven
    rcases hp.eq_one_or_self_of_dvd 2 h2 with h | h
    · exact absurd h (by norm_num)
    · omega
  · -- `n = p + 2^a`: the covering obstruction forces `p ∈ coveringPrimes` (all odd).
    have hrep' : n = 2 ^ a + p := by omega
    have hpc : p ∈ coveringPrimes := prime_forced_small h3 h7 h5 h17 h13 h241 hp hrep'
    have hpodd : p % 2 = 1 := Nat.odd_iff.mp (coveringPrimes_odd hpc)
    have hple : p ≤ 241 := coveringPrimes_le hpc
    -- Parity of `n = p + 2^a`: `n` even, `p` odd ⟹ `2^a` odd ⟹ `a = 0`.
    have hpow : 2 ^ a % 2 = 1 := by omega
    have ha0 : a = 0 := by
      by_contra ha
      have : Even (2 ^ a) := by rw [Nat.even_pow]; exact ⟨by decide, ha⟩
      rw [Nat.even_iff] at this
      omega
    subst ha0
    -- Now `n = p + 2^0 = p + 1 ≤ 242`, contradicting `n > 242`.
    norm_num at hrep
    omega

/-! ## The explicit infinite family -/

/-- The explicit even arithmetic progression `n(s) = 2036812 + 11184810 · s`.  The common
difference `11184810 = 2 · 3 · 5 · 7 · 13 · 17 · 241` is even and divisible by each covering
prime, so every term is even and shares the residue class of the sibling file's CRT witness. -/
def family (s : ℕ) : ℕ := 2036812 + 11184810 * s

/-- Every term of `family` is even, exceeds `242`, and lies in the covering residue class. -/
theorem family_props (s : ℕ) :
    (family s % 3 = 1) ∧ (family s % 7 = 1) ∧ (family s % 5 = 2) ∧
    (family s % 17 = 8) ∧ (family s % 13 = 11) ∧ (family s % 241 = 121) ∧
    (family s % 2 = 0) ∧ (242 < family s) := by
  unfold family
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Each term of the family is outside `sumPrimeAndTwoPows 1`. -/
theorem family_not_mem_one (s : ℕ) : family s ∉ sumPrimeAndTwoPows 1 := by
  obtain ⟨h3, h7, h5, h17, h13, h241, heven, hbig⟩ := family_props s
  exact not_mem_one_of_even h3 h7 h5 h17 h13 h241 heven hbig

/-- **Main result.** There are infinitely many integers that are *not* a prime plus a single
power of two — an explicit infinite family lying outside `sumPrimeAndTwoPows 1`.  This upgrades
the sibling file's `infinitely_many_forced` (which only forced the prime to be small) to an
unconditional exclusion from level 1 of the Erdős #10 representation hierarchy. -/
theorem infinite_not_mem_one :
    {n : ℕ | n ∉ sumPrimeAndTwoPows 1}.Infinite := by
  have hinj : Function.Injective family := by
    intro a b hab
    unfold family at hab
    omega
  have hmem : ∀ s : ℕ, family s ∈ {n : ℕ | n ∉ sumPrimeAndTwoPows 1} := fun s =>
    family_not_mem_one s
  exact Set.infinite_of_injective_forall_mem hinj hmem

#check @mem_one_forced
#check @not_mem_one_of_even
#check @infinite_not_mem_one

end Erdos10Incomplete01OQ02
