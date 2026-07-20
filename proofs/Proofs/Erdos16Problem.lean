/-
Erdős Problem #16: Odd Integers Not of the Form 2^k + p

Is the set of odd integers not of the form 2^k + p (where p is prime)
the union of an infinite arithmetic progression and a set of density 0?

**Status**: SOLVED (Disproved by Chen 2023)

**Answer**: NO. The exceptional set has more complex structure.

**Background**:
- Erdős called this conjecture "rather silly"
- Using covering congruences, Erdős (1950) proved the exceptional set
  contains an infinite arithmetic progression
- Chen (2023) proved the conjecture is false

**Related**: Problems #9, #10, #11 (Romanoff-type problems)

Reference: https://erdosproblems.com/16
OEIS: A006285 (odd numbers not of form 2^k + p)
-/

import Mathlib

open Finset
open scoped BigOperators

namespace Erdos16

/-
## Background

The Romanoff theorem (1934) states that a positive proportion of odd integers
can be written as 2^k + p for some k ≥ 1 and prime p.

This problem asks about the structure of the "exceptional" odd integers
that CANNOT be written in this form.

Examples of exceptional odd integers (OEIS A006285):
1, 127, 149, 251, 331, 337, 373, 509, 599, 701, ...

Note: 1 is trivially exceptional (no prime + power of 2 equals 1).
-/

/-
## Core Definitions
-/

/-- An odd integer n is "Romanoff" if n = 2^k + p for some k ≥ 1 and prime p. -/
def IsRomanoff (n : ℕ) : Prop :=
  ∃ k p : ℕ, k ≥ 1 ∧ Nat.Prime p ∧ n = 2^k + p

/-- The set of odd integers that are NOT Romanoff (the exceptional set). -/
def ExceptionalSet : Set ℕ :=
  { n : ℕ | Odd n ∧ ¬IsRomanoff n }

/-  Alternative characterization: n is exceptional if for all k with 2^k < n,
    the number n - 2^k is not prime. -/

/-
## The Romanoff Theorem

Romanoff (1934) proved that a positive density of odd integers are Romanoff.
-/

/-- The density of a set A ⊆ ℕ up to N.
    We use classical decidability for the filter. -/
noncomputable def density (A : Set ℕ) (N : ℕ) : ℝ :=
  (Finset.filter (fun x => @Decidable.decide (x ∈ A) (Classical.dec _))
    (Finset.range (N + 1))).card / (N + 1)

/-- The asymptotic lower density of a set. -/
noncomputable def lowerDensity (A : Set ℕ) : ℝ :=
  ⨅ (N : ℕ), ⨆ (M : ℕ) (_ : M ≥ N), density A M

/-  Romanoff's Theorem (1934): A positive proportion of odd integers are Romanoff. -/

/-  Corollary: The exceptional set has density less than 1/2. -/

/-
## Erdős's Covering Congruence Result (1950)

Using covering congruences, Erdős proved that the exceptional set
contains an infinite arithmetic progression.
-/

/-- A covering congruence system: residue classes that cover all integers. -/
def IsCoveringSystem (residues : List (ℕ × ℕ)) : Prop :=
  ∀ n : ℤ, ∃ rm ∈ residues, rm.2 > 0 ∧ n % rm.2 = rm.1

/-  Erdős's construction (1950): The exceptional set contains an
    infinite arithmetic progression. -/

/-
## The Conjecture and Its Disproof

Erdős conjectured (calling it "rather silly") that the exceptional set
is essentially just an arithmetic progression plus a negligible part.
-/

/-- Erdős's original conjecture: The exceptional set equals an arithmetic
    progression union a density-0 set. -/
def ErdosConjecture16 : Prop :=
  ∃ a d : ℕ, d > 0 ∧
    lowerDensity (ExceptionalSet \ { n | ∃ m, n = a + m * d }) = 0

/-  Chen's Theorem (2023): The conjecture is FALSE. -/

/-  Consequence: The exceptional set contains elements from multiple
    "essentially different" arithmetic progressions, or has positive
    density outside any single progression. -/

/-
## Known Exceptional Numbers

The first few odd integers not of the form 2^k + p (OEIS A006285):
1, 127, 149, 251, 331, 337, 373, 509, 599, 701, 757, 809, 877, ...
-/

/-  127 is in the exceptional set. -/

/-
## Connection to Covering Congruences

Covering congruences are systems of arithmetic progressions that
cover all integers. They are key to constructing exceptional numbers.
-/

/-- The classic Erdős covering: residues mod 2, 3, 4, 6, 8, 12, 24. -/
def erdosCovering : List (ℕ × ℕ) :=
  [(0, 2), (0, 3), (1, 4), (1, 6), (3, 8), (7, 12), (23, 24)]

/-
## Density Bounds

More precise bounds on the density of the exceptional set.
-/

/-  The exceptional set has positive lower density. -/

/-
## Related Problems

This problem is part of a family about representations n = 2^k + p.
-/

/-- Problem #9: Do infinitely many n have unique representation 2^k + p? -/
def Erdos9Question : Prop :=
  Set.Infinite { n : ℕ | ∃! kp : ℕ × ℕ, kp.1 ≥ 1 ∧ Nat.Prime kp.2 ∧ n = 2^kp.1 + kp.2 }

/-- Problem #10: Can every large even number be written as 2^k + p? -/
def Erdos10Question : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, Even n → n ≥ N →
    ∃ k p : ℕ, k ≥ 1 ∧ Nat.Prime p ∧ n = 2^k + p

/-- Problem #11: Is the representation count bounded?

    r(n) = number of ways to write n = 2^k + p. Is sup_n r(n) < ∞? -/
def Erdos11Question : Prop :=
  ∃ C : ℕ, ∀ n : ℕ,
    (Finset.filter (fun k => @Decidable.decide (∃ p, Nat.Prime p ∧ n = 2^k + p) (Classical.dec _))
      (Finset.range n)).card ≤ C

/-
## Why Chen's Result is Significant

Chen's disproof shows that the exceptional set has rich structure
beyond what Erdős initially suspected.

Possible implications:
1. Multiple "independent" arithmetic progressions in the exceptional set
2. Fractal-like or quasi-random structure
3. Deep connections to the distribution of primes
-/

/-
## Foundational lemmas (axiom-free)

The deep results (Romanoff's theorem, Erdős's covering construction, Chen's
disproof) require analytic number theory beyond current Mathlib and are documented
in the prose above only.  What *is* fully machine-checkable are the elementary
structural facts about the definitions in this file: the exponential lower bound
forcing small odd numbers into the exceptional set, concrete Romanoff witnesses,
the basic range of the density functional, and the covering property of the
explicit Erdős covering system.  All lemmas below are axiom-free
(`propext / Classical.choice / Quot.sound` only). -/

/-- Membership in the exceptional set unfolds to its defining predicate. -/
theorem mem_exceptionalSet_iff {n : ℕ} :
    n ∈ ExceptionalSet ↔ Odd n ∧ ¬ IsRomanoff n := Iff.rfl

/-- **Structural lower bound:** every Romanoff number is at least `4`, since
`2^k ≥ 2` (as `k ≥ 1`) and `p ≥ 2` (as `p` is prime). -/
theorem isRomanoff_four_le {n : ℕ} (h : IsRomanoff n) : 4 ≤ n := by
  obtain ⟨k, p, hk, hp, rfl⟩ := h
  have h2k : 2 ≤ 2 ^ k := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hp2 : 2 ≤ p := hp.two_le
  omega

/-- `1` is not Romanoff (it is below the Romanoff floor `4`). -/
theorem not_isRomanoff_one : ¬ IsRomanoff 1 := fun h => by
  have := isRomanoff_four_le h; omega

/-- `3` is not Romanoff (it is below the Romanoff floor `4`). -/
theorem not_isRomanoff_three : ¬ IsRomanoff 3 := fun h => by
  have := isRomanoff_four_le h; omega

/-- `1` is an exceptional odd integer. -/
theorem one_mem_exceptionalSet : (1 : ℕ) ∈ ExceptionalSet :=
  ⟨odd_one, not_isRomanoff_one⟩

/-- `3` is an exceptional odd integer. -/
theorem three_mem_exceptionalSet : (3 : ℕ) ∈ ExceptionalSet :=
  ⟨by decide, not_isRomanoff_three⟩

/-- Concrete Romanoff witness: `5 = 2^1 + 3`. -/
theorem isRomanoff_five : IsRomanoff 5 := ⟨1, 3, by norm_num, by norm_num, by norm_num⟩

/-- Concrete Romanoff witness: `7 = 2^2 + 3`. -/
theorem isRomanoff_seven : IsRomanoff 7 := ⟨2, 3, by norm_num, by norm_num, by norm_num⟩

/-- Since `5` is Romanoff, it is *not* in the exceptional set. -/
theorem five_not_mem_exceptionalSet : (5 : ℕ) ∉ ExceptionalSet := fun h => h.2 isRomanoff_five

/-- The density functional is nonnegative. -/
theorem density_nonneg (A : Set ℕ) (N : ℕ) : 0 ≤ density A N := by
  unfold density; positivity

/-- The density functional never exceeds `1` (the filtered set sits inside
`range (N+1)`, which has `N+1` elements). -/
theorem density_le_one (A : Set ℕ) (N : ℕ) : density A N ≤ 1 := by
  unfold density
  rw [div_le_one (by positivity)]
  have hcard : (Finset.filter (fun x => @Decidable.decide (x ∈ A) (Classical.dec _))
      (Finset.range (N + 1))).card ≤ (Finset.range (N + 1)).card :=
    Finset.card_filter_le _ _
  rw [Finset.card_range] at hcard
  exact_mod_cast hcard

/-- Every modulus in the explicit Erdős covering system is positive. -/
theorem erdosCovering_moduli_pos : ∀ rm ∈ erdosCovering, 0 < rm.2 := by decide

/-- **The Erdős covering system genuinely covers `ℤ`.** Every integer lies in one
of the residue classes `{0 mod 2, 0 mod 3, 1 mod 4, 1 mod 6, 3 mod 8, 7 mod 12,
23 mod 24}`.  This is the covering-congruence engine behind Erdős's 1950 proof
that the exceptional set contains an infinite arithmetic progression.  Since every
modulus divides `24`, membership depends only on `n % 24`, giving a finite check. -/
theorem erdosCovering_isCoveringSystem : IsCoveringSystem erdosCovering := by
  intro n
  have hcov : n % 2 = 0 ∨ n % 3 = 0 ∨ n % 4 = 1 ∨ n % 6 = 1 ∨ n % 8 = 3 ∨
      n % 12 = 7 ∨ n % 24 = 23 := by omega
  rcases hcov with h | h | h | h | h | h | h
  · exact ⟨(0, 2), by simp [erdosCovering], by norm_num, by exact_mod_cast h⟩
  · exact ⟨(0, 3), by simp [erdosCovering], by norm_num, by exact_mod_cast h⟩
  · exact ⟨(1, 4), by simp [erdosCovering], by norm_num, by exact_mod_cast h⟩
  · exact ⟨(1, 6), by simp [erdosCovering], by norm_num, by exact_mod_cast h⟩
  · exact ⟨(3, 8), by simp [erdosCovering], by norm_num, by exact_mod_cast h⟩
  · exact ⟨(7, 12), by simp [erdosCovering], by norm_num, by exact_mod_cast h⟩
  · exact ⟨(23, 24), by simp [erdosCovering], by norm_num, by exact_mod_cast h⟩

/-- **Bounded characterisation of the Romanoff property.**  The unbounded
existential `∃ k p, k ≥ 1 ∧ Prime p ∧ n = 2^k + p` is equivalent to the
*decidable-flavoured* statement that some exponent `k ≥ 1` with `2^k < n` makes
the complementary residue `n - 2^k` prime.  This eliminates the prime variable
`p` entirely (it is forced to be `n - 2^k`) and bounds the search: since `2^k < n`
forces `k ≤ log₂ n`, membership reduces to checking finitely many exponents. -/
theorem isRomanoff_iff {n : ℕ} :
    IsRomanoff n ↔ ∃ k, 1 ≤ k ∧ 2 ^ k < n ∧ Nat.Prime (n - 2 ^ k) := by
  constructor
  · rintro ⟨k, p, hk, hp, rfl⟩
    exact ⟨k, hk, by have := hp.two_le; omega, by simpa using hp⟩
  · rintro ⟨k, hk, hlt, hp⟩
    exact ⟨k, n - 2 ^ k, hk, hp, by omega⟩

/-- Finite-range refinement of `isRomanoff_iff`: the witness exponent lies in
`Finset.range n`, because `2^k < n` forces `k < 2^k < n`.  This packages
membership as a *bounded* existential, which is the step that makes `IsRomanoff`
decidable. -/
theorem isRomanoff_iff_mem_range {n : ℕ} :
    IsRomanoff n ↔
      ∃ k ∈ Finset.range n, 1 ≤ k ∧ 2 ^ k < n ∧ Nat.Prime (n - 2 ^ k) := by
  rw [isRomanoff_iff]
  constructor
  · rintro ⟨k, hk, hlt, hp⟩
    exact ⟨k, Finset.mem_range.mpr (Nat.lt_two_pow_self.trans hlt), hk, hlt, hp⟩
  · rintro ⟨k, _, hk, hlt, hp⟩
    exact ⟨k, hk, hlt, hp⟩

/-- **`IsRomanoff` is decidable.**  Via `isRomanoff_iff_mem_range` it reduces to a
bounded existential over `Finset.range n` with decidable primality — no
`native_decide`, so the axioms stay clean.  In principle this settles every "`n`
is / is not Romanoff" and hence "`n ∈ ExceptionalSet`" question; `decide`
discharges small `n` directly (e.g. `IsRomanoff 5`).  For the larger A006285
terms below we keep the explicit `interval_cases` refutations, which give the
kernel a short, `2^k`-small reduction (the naive `decide` over `Finset.range n`
would force it to evaluate `2^{n-1}`). -/
instance decidableIsRomanoff (n : ℕ) : Decidable (IsRomanoff n) :=
  decidable_of_iff _ isRomanoff_iff_mem_range.symm

/-- **`127` is exceptional.**  It is the first nontrivial odd integer of OEIS
A006285: for every `k` with `1 ≤ k` and `2^k < 127`, the complement `127 - 2^k`
is composite (`125 = 5³`, `123 = 3·41`, `119 = 7·17`, `111 = 3·37`, `95 = 5·19`,
`63 = 7·9`), so `127` is not of the form `2^k + p`. -/
theorem not_isRomanoff_127 : ¬ IsRomanoff 127 := by
  rw [isRomanoff_iff]
  rintro ⟨k, hk, hlt, hp⟩
  have hk6 : k ≤ 6 := by
    by_contra h
    have h7 : (2 : ℕ) ^ 7 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h7; omega
  interval_cases k <;> norm_num at hp

/-- `127` is an exceptional odd integer (`127 ∈ ExceptionalSet`). -/
theorem oneHundredTwentySeven_mem_exceptionalSet : (127 : ℕ) ∈ ExceptionalSet :=
  ⟨⟨63, by norm_num⟩, not_isRomanoff_127⟩

/-- **`149` is exceptional** (the second nontrivial term of A006285).  For every
`k` with `2^k < 149` the complement is composite (`147 = 3·49`, `145 = 5·29`,
`141 = 3·47`, `133 = 7·19`, `117 = 9·13`, `85 = 5·17`, `21 = 3·7`). -/
theorem not_isRomanoff_149 : ¬ IsRomanoff 149 := by
  rw [isRomanoff_iff]
  rintro ⟨k, hk, hlt, hp⟩
  have hk7 : k ≤ 7 := by
    by_contra h
    have h8 : (2 : ℕ) ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h8; omega
  interval_cases k <;> norm_num at hp

/-- `149` is an exceptional odd integer (`149 ∈ ExceptionalSet`). -/
theorem oneHundredFortyNine_mem_exceptionalSet : (149 : ℕ) ∈ ExceptionalSet :=
  ⟨⟨74, by norm_num⟩, not_isRomanoff_149⟩

/-- **`251` is exceptional** (the third nontrivial term of A006285).  For every
`k` with `2^k < 251` the complement is composite (`249 = 3·83`, `247 = 13·19`,
`243 = 3⁵`, `235 = 5·47`, `219 = 3·73`, `187 = 11·17`, `123 = 3·41`). -/
theorem not_isRomanoff_251 : ¬ IsRomanoff 251 := by
  rw [isRomanoff_iff]
  rintro ⟨k, hk, hlt, hp⟩
  have hk7 : k ≤ 7 := by
    by_contra h
    have h8 : (2 : ℕ) ^ 8 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h8; omega
  interval_cases k <;> norm_num at hp

/-- `251` is an exceptional odd integer (`251 ∈ ExceptionalSet`). -/
theorem twoHundredFiftyOne_mem_exceptionalSet : (251 : ℕ) ∈ ExceptionalSet :=
  ⟨⟨125, by norm_num⟩, not_isRomanoff_251⟩

/-- **`331` is exceptional** (the fourth nontrivial term of A006285).  For every
`k` with `2^k < 331` the complement is composite (`329 = 7·47`, `327 = 3·109`,
`323 = 17·19`, `315 = 5·63`, `299 = 13·23`, `267 = 3·89`, `203 = 7·29`,
`75 = 3·25`). -/
theorem not_isRomanoff_331 : ¬ IsRomanoff 331 := by
  rw [isRomanoff_iff]
  rintro ⟨k, hk, hlt, hp⟩
  have hk8 : k ≤ 8 := by
    by_contra h
    have h9 : (2 : ℕ) ^ 9 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at h9; omega
  interval_cases k <;> norm_num at hp

/-- `331` is an exceptional odd integer (`331 ∈ ExceptionalSet`). -/
theorem threeHundredThirtyOne_mem_exceptionalSet : (331 : ℕ) ∈ ExceptionalSet :=
  ⟨⟨165, by norm_num⟩, not_isRomanoff_331⟩

/-
## The covering-congruence obstruction mechanism (axiom-free)

The A006285 refutations above check each exponent `k` individually.  Erdős's 1950
argument is structural: it groups the exponents into finitely many residue classes
(a covering system of `ℤ`, e.g. `erdosCovering`), and to each class `k ≡ r (mod d)`
attaches a *fixed prime* `p` with `2^d ≡ 1 (mod p)`.  Then `2^k ≡ 2^r (mod p)` for
every `k` in that class, so choosing `n ≡ 2^r (mod p)` forces `p ∣ n - 2^k`, making
`n - 2^k` composite whenever it exceeds `p`.  Running this over a covering system
kills *all* exponents simultaneously, placing an entire arithmetic progression of
`n` into the exceptional set.  The lemmas below formalize this mechanism (one prime
= one "gear"); assembling all gears into a single progression via CRT is the
remaining deep step (Romanoff/Erdős-grade, documented above only). -/

/-- The residue of `2^k` modulo `3` is periodic with period `2`: it is `1` for even
`k` and `2` for odd `k` (the order of `2` mod `3` is `2`).  This is the smallest
"gear" of the covering machine. -/
theorem two_pow_mod_three (k : ℕ) : (2 : ℕ) ^ k % 3 = if k % 2 = 0 then 1 else 2 := by
  induction k with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Nat.mul_mod, ih]
    rcases (by omega : n % 2 = 0 ∨ n % 2 = 1) with h | h
    · rw [if_pos h, if_neg (by omega : ¬ (n + 1) % 2 = 0)]
    · rw [if_neg (by omega : ¬ n % 2 = 0), if_pos (by omega : (n + 1) % 2 = 0)]

/-- **Exponent periodicity of `2` modulo `p`.**  If `2^d ≡ 1 (mod p)` (i.e. the
multiplicative order of `2` mod `p` divides `d`), then `2^k ≡ 2^r (mod p)` whenever
`k ≡ r (mod d)` with `r ≤ k`.  This is the core algebraic fact that lets a single
prime cover a whole residue class of exponents. -/
theorem two_pow_modEq_of_dvd {p d k r : ℕ} (hd : (2 : ℕ) ^ d ≡ 1 [MOD p])
    (hle : r ≤ k) (hdvd : d ∣ (k - r)) : (2 : ℕ) ^ k ≡ 2 ^ r [MOD p] := by
  obtain ⟨t, ht⟩ := hdvd
  have hk : k = r + d * t := by omega
  subst hk
  calc (2 : ℕ) ^ (r + d * t)
      = 2 ^ r * (2 ^ d) ^ t := by rw [pow_add, pow_mul]
    _ ≡ 2 ^ r * 1 ^ t [MOD p] := (Nat.ModEq.refl _).mul (hd.pow t)
    _ = 2 ^ r := by rw [one_pow, mul_one]

/-- **The covering obstruction (general gear).**  Fix a prime `p` and an exponent
period `d` with `2^d ≡ 1 (mod p)`.  For any exponent `k ≡ r (mod d)` and any `n`
with `n ≡ 2^r (mod p)`, the prime `p` divides `n - 2^k`; hence if additionally
`p < n - 2^k` (so the quotient is `> 1`), the complement `n - 2^k` is **composite**.
This is exactly the step by which one residue class of exponents is eliminated in
Erdős's construction. -/
theorem covering_prime_not_prime_sub {p d k r n : ℕ}
    (hp : Nat.Prime p) (hd : (2 : ℕ) ^ d ≡ 1 [MOD p])
    (hle : r ≤ k) (hdvd : d ∣ (k - r)) (hn : n ≡ 2 ^ r [MOD p])
    (hlt : 2 ^ k < n) (hbig : p < n - 2 ^ k) : ¬ Nat.Prime (n - 2 ^ k) := by
  have hper : (2 : ℕ) ^ k ≡ 2 ^ r [MOD p] := two_pow_modEq_of_dvd hd hle hdvd
  have hnk : (2 : ℕ) ^ k ≡ n [MOD p] := hper.trans hn.symm
  have hdvd2 : p ∣ n - 2 ^ k := (Nat.modEq_iff_dvd' hlt.le).mp hnk
  intro hprime
  rcases hprime.eq_one_or_self_of_dvd p hdvd2 with h | h
  · have := hp.two_le; omega
  · omega

/-- **Concrete gear (prime `3`, even exponents).**  If `n ≡ 1 (mod 3)` then for
every *even* exponent `k` with `2^k < n` and `n - 2^k > 3`, the complement `n - 2^k`
is composite (since `2^k ≡ 1 (mod 3)` for even `k`, so `3 ∣ n - 2^k`).  Thus in the
progression `n ≡ 1 (mod 3)` no even exponent can witness a Romanoff representation. -/
theorem not_prime_sub_even_mod_three {n k : ℕ}
    (hn : n % 3 = 1) (hk : Even k) (hlt : 2 ^ k < n) (hbig : 3 < n - 2 ^ k) :
    ¬ Nat.Prime (n - 2 ^ k) := by
  obtain ⟨m, hm⟩ := hk
  refine covering_prime_not_prime_sub (p := 3) (d := 2) (r := 0)
    (by norm_num) (by decide) (Nat.zero_le k) ⟨m, by omega⟩ ?_ hlt hbig
  show n % 3 = 2 ^ 0 % 3
  norm_num [hn]

/-- **Concrete gear (prime `7`, exponents `≡ 0 mod 3`).**  If `n ≡ 1 (mod 7)` then
for every exponent `k` divisible by `3` with `2^k < n` and `n - 2^k > 7`, the
complement `n - 2^k` is composite (the order of `2` mod `7` is `3`, so `2^k ≡ 1
(mod 7)`, giving `7 ∣ n - 2^k`).  A second prime covering a *different* class of
exponents, demonstrating the mechanism is not special to `p = 3`. -/
theorem not_prime_sub_mod_seven {n k : ℕ}
    (hn : n % 7 = 1) (hk : k % 3 = 0) (hlt : 2 ^ k < n) (hbig : 7 < n - 2 ^ k) :
    ¬ Nat.Prime (n - 2 ^ k) := by
  refine covering_prime_not_prime_sub (p := 7) (d := 3) (r := 0)
    (by norm_num) (by decide) (Nat.zero_le k) ⟨k / 3, by omega⟩ ?_ hlt hbig
  show n % 7 = 2 ^ 0 % 7
  norm_num [hn]

/-
## Summary

**Problem Status: SOLVED (Disproved)**

Erdős Problem 16 asked whether the set of odd integers not expressible
as 2^k + p (exceptional set) is an arithmetic progression plus density-0 set.

**Resolution**: Chen (2023) proved the answer is NO.

**Key results**:
- Romanoff (1934): Positive density of odd integers ARE of this form
- Erdős (1950): Exceptional set CONTAINS an arithmetic progression
- Chen (2023): Exceptional set is NOT just one progression + noise

**The exceptional set**:
- Has positive but small density (~0.09)
- Contains arithmetic progressions (by covering congruences)
- Has complex structure beyond any single progression

References:
- Romanoff (1934): Positive density theorem
- Erdős (1950): Covering congruence construction
- Chen (2023): Disproof of the conjecture
- OEIS A006285: The exceptional sequence
-/

end Erdos16
