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

/-  The exceptional set has positive lower density: proved below as
    `exceptionalCount_positive_density` (counting form, `≥ N / 22369620` below
    any horizon `N ≥ 2^52`) and `lowerDensity_exceptionalSet_pos`. -/

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
## Assembling the gears: the full covering obstruction (axiom-free)

The gears above each handle *one* residue class of the exponent `k`.  Erdős's
1950 construction runs a whole **covering system** of the exponent — the six
classes `k ≡ 0 (mod 2)`, `k ≡ 0 (mod 3)`, `k ≡ 1 (mod 4)`, `k ≡ 3 (mod 8)`,
`k ≡ 7 (mod 12)`, `k ≡ 23 (mod 24)` cover every integer — and attaches to each
class a prime `p` whose multiplicative order of `2` equals that modulus:

| exponent class | modulus `d` | prime `p` | `2^d ≡ 1 (mod p)` | needed `n ≡ 2^r (mod p)` |
|----------------|-------------|-----------|-------------------|--------------------------|
| `k ≡ 0 (2)`  | 2  | 3   | `2² = 4 ≡ 1`      | `n ≡ 1 (mod 3)`   |
| `k ≡ 0 (3)`  | 3  | 7   | `2³ = 8 ≡ 1`      | `n ≡ 1 (mod 7)`   |
| `k ≡ 1 (4)`  | 4  | 5   | `2⁴ = 16 ≡ 1`     | `n ≡ 2 (mod 5)`   |
| `k ≡ 3 (8)`  | 8  | 17  | `2⁸ = 256 ≡ 1`    | `n ≡ 8 (mod 17)`  |
| `k ≡ 7 (12)` | 12 | 13  | `2¹² ≡ 1`         | `n ≡ 11 (mod 13)` |
| `k ≡ 23 (24)`| 24 | 241 | `2²⁴ ≡ 1`         | `n ≡ 121 (mod 241)` |

Because the six primes are distinct, the Chinese Remainder Theorem produces an
arithmetic progression `n ≡ a (mod 3·5·7·13·17·241)` meeting all six congruences
at once.  For any such `n`, *every* exponent `k` falls into one covering class,
its prime divides `n - 2^k`, and (once `n - 2^k` exceeds that prime) the
complement is composite — so `n` is not Romanoff.  This is Erdős's theorem that
the exceptional set contains an infinite arithmetic progression, formalized here
as an unconditional obstruction subject to a single explicit size hypothesis.
The order-of-`2` facts (the table's third column) come first. -/

/-- Order gear: `2² ≡ 1 (mod 3)` (order of `2` mod `3` is `2`). -/
theorem two_pow_two_modEq_three : (2 : ℕ) ^ 2 ≡ 1 [MOD 3] := by decide

/-- Order gear: `2³ ≡ 1 (mod 7)` (order of `2` mod `7` is `3`). -/
theorem two_pow_three_modEq_seven : (2 : ℕ) ^ 3 ≡ 1 [MOD 7] := by decide

/-- Order gear: `2⁴ ≡ 1 (mod 5)` (order of `2` mod `5` is `4`). -/
theorem two_pow_four_modEq_five : (2 : ℕ) ^ 4 ≡ 1 [MOD 5] := by decide

/-- Order gear: `2⁸ ≡ 1 (mod 17)` (order of `2` mod `17` is `8`). -/
theorem two_pow_eight_modEq_seventeen : (2 : ℕ) ^ 8 ≡ 1 [MOD 17] := by decide

/-- Order gear: `2¹² ≡ 1 (mod 13)` (order of `2` mod `13` is `12`). -/
theorem two_pow_twelve_modEq_thirteen : (2 : ℕ) ^ 12 ≡ 1 [MOD 13] := by
  norm_num [Nat.ModEq]

/-- Order gear: `2²⁴ ≡ 1 (mod 241)` (order of `2` mod `241` is `24`; this is the
prime that closes the `k ≡ 23 (mod 24)` class). -/
theorem two_pow_twentyfour_modEq_241 : (2 : ℕ) ^ 24 ≡ 1 [MOD 241] := by
  norm_num [Nat.ModEq]

/-- **Erdős's covering obstruction, assembled.**  Suppose `n` simultaneously
satisfies the six congruences from the table above —
`n ≡ 1 (mod 3)`, `n ≡ 1 (mod 7)`, `n ≡ 2 (mod 5)`, `n ≡ 8 (mod 17)`,
`n ≡ 11 (mod 13)`, `n ≡ 121 (mod 241)` — and is large enough that
`n - 2^k > 241` for every exponent `k ≥ 1` with `2^k < n`.  Then `n` is **not
Romanoff**: each exponent `k` lands in one of the six covering classes, the
attached prime divides `n - 2^k`, and the size hypothesis makes the quotient
`> 1`, so `n - 2^k` is composite.  This is the full covering-congruence
mechanism of Erdős (1950) — every one of the (infinitely many) exponents is
killed by a *single* fixed prime — so the entire CRT progression
`n ≡ a (mod 3·5·7·13·17·241)` satisfying the size hypothesis lies in the
exceptional set. -/
theorem covering_obstruction_not_isRomanoff {n : ℕ}
    (h3 : n % 3 = 1) (h7 : n % 7 = 1) (h5 : n % 5 = 2)
    (h17 : n % 17 = 8) (h13 : n % 13 = 11) (h241 : n % 241 = 121)
    (hsize : ∀ k, 1 ≤ k → 2 ^ k < n → 241 < n - 2 ^ k) :
    ¬ IsRomanoff n := by
  rw [isRomanoff_iff]
  rintro ⟨k, hk, hlt, hp⟩
  have hbig : 241 < n - 2 ^ k := hsize k hk hlt
  -- Every exponent falls into one of the six covering classes.
  have hcov : k % 2 = 0 ∨ k % 3 = 0 ∨ k % 4 = 1 ∨ k % 8 = 3 ∨ k % 12 = 7 ∨
      k % 24 = 23 := by omega
  rcases hcov with h | h | h | h | h | h
  · exact covering_prime_not_prime_sub (p := 3) (d := 2) (r := 0)
      (by norm_num) two_pow_two_modEq_three (Nat.zero_le k) (by omega)
      (by show n % 3 = 2 ^ 0 % 3; norm_num [h3]) hlt (by omega) hp
  · exact covering_prime_not_prime_sub (p := 7) (d := 3) (r := 0)
      (by norm_num) two_pow_three_modEq_seven (Nat.zero_le k) (by omega)
      (by show n % 7 = 2 ^ 0 % 7; norm_num [h7]) hlt (by omega) hp
  · exact covering_prime_not_prime_sub (p := 5) (d := 4) (r := 1)
      (by norm_num) two_pow_four_modEq_five hk (by omega)
      (by show n % 5 = 2 ^ 1 % 5; norm_num [h5]) hlt (by omega) hp
  · exact covering_prime_not_prime_sub (p := 17) (d := 8) (r := 3)
      (by norm_num) two_pow_eight_modEq_seventeen (by omega) (by omega)
      (by show n % 17 = 2 ^ 3 % 17; norm_num [h17]) hlt (by omega) hp
  · exact covering_prime_not_prime_sub (p := 13) (d := 12) (r := 7)
      (by norm_num) two_pow_twelve_modEq_thirteen (by omega) (by omega)
      (by show n % 13 = 2 ^ 7 % 13; norm_num [h13]) hlt (by omega) hp
  · exact covering_prime_not_prime_sub (p := 241) (d := 24) (r := 23)
      (by norm_num) two_pow_twentyfour_modEq_241 (by omega) (by omega)
      (by show n % 241 = 2 ^ 23 % 241; norm_num [h241]) hlt (by omega) hp

/-- **The covering progression lies in the exceptional set.**  An odd `n`
meeting the six covering congruences and the size hypothesis of
`covering_obstruction_not_isRomanoff` is a genuine exceptional integer.  This is
the membership form of Erdős's 1950 result: the whole CRT progression (odd
members, large enough) sits inside `ExceptionalSet`. -/
theorem covering_progression_mem_exceptionalSet {n : ℕ} (hodd : Odd n)
    (h3 : n % 3 = 1) (h7 : n % 7 = 1) (h5 : n % 5 = 2)
    (h17 : n % 17 = 8) (h13 : n % 13 = 11) (h241 : n % 241 = 121)
    (hsize : ∀ k, 1 ≤ k → 2 ^ k < n → 241 < n - 2 ^ k) :
    n ∈ ExceptionalSet :=
  ⟨hodd, covering_obstruction_not_isRomanoff h3 h7 h5 h17 h13 h241 hsize⟩

/-!
## Erdős's infinite arithmetic progression: the exceptional set is infinite

`covering_progression_mem_exceptionalSet` places every odd member of the CRT progression
`n ≡ 7629217 (mod 11184810)` that also satisfies the size condition into `ExceptionalSet`.
We now discharge the size condition for *infinitely many* members, yielding Erdős's 1950
conclusion in full: `ExceptionalSet` is **infinite**.

The number `7629217` is the unique residue mod `2M = 2·3·5·7·13·17·241 = 11184810` solving
the six covering congruences together with oddness (verified by `omega` at each use).  The key
observation that discharges the size condition cheaply: if `n` lies in the dyadic window
`[2^m + 242, 2^{m+1})`, then any exponent `k` with `2^k < n` satisfies `k ≤ m`, so
`n - 2^k ≥ n - 2^m ≥ 242 > 241` — no analysis of "the largest power of two below `n`" is
needed.  Since each window has length `2^m - 242 ≥ 2M` for large `m`, the progression meets
every such window, and the windows march off to infinity. -/

/-- **For every bound `B` there is an exceptional integer exceeding `B`.**  Pick `m` with
`2^m` large; the progression member in the window `[2^m + 242, 2^{m+1})` is odd, satisfies the
six covering congruences (being `≡ 7629217 mod 11184810`), and meets the size condition
automatically because every relevant exponent `k` has `2^k ≤ 2^m ≤ n - 242`. -/
theorem exists_exceptional_gt (B : ℕ) : ∃ n, B < n ∧ n ∈ ExceptionalSet := by
  set m : ℕ := B + 11184810 + 243 with hm
  clear_value m
  have hpm : m < 2 ^ m := Nat.lt_two_pow_self
  have hbig : 242 + 11184810 ≤ 2 ^ m := by omega
  have hBm : B < 2 ^ m := by omega
  set L : ℕ := 2 ^ m + 242 with hL
  have hLge : 7629217 ≤ L := by omega
  -- The progression `7629217 + q · 2M` meets the window `[L, L + 2M)`.
  obtain ⟨q, hnL, hnU⟩ :
      ∃ q, L ≤ 7629217 + q * 11184810 ∧ 7629217 + q * 11184810 < L + 11184810 :=
    ⟨(L - 7629217 + 11184810 - 1) / 11184810, by omega, by omega⟩
  set n : ℕ := 7629217 + q * 11184810 with hn
  have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  have hnUB : n < 2 ^ (m + 1) := by omega
  refine ⟨n, by omega, ?_⟩
  refine covering_progression_mem_exceptionalSet (Nat.odd_iff.mpr (by omega))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
  -- Size condition: any `k` with `2^k < n` has `k ≤ m`, so `n - 2^k ≥ 242`.
  intro k _ hkn
  have hk2 : 2 ^ k < 2 ^ (m + 1) := by omega
  have hkm : k ≤ m := by
    by_contra hc
    exact absurd hk2 (not_lt.mpr (Nat.pow_le_pow_right (by norm_num) (not_le.mp hc)))
  have hle : 2 ^ k ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hkm
  omega

/-- **Erdős (1950): the exceptional set is infinite.**  The covering-congruence progression
contributes infinitely many odd integers not of the form `2^k + p`, so
`ExceptionalSet` is infinite.  (Chen (2023) later showed its structure is richer than a
single progression plus a density-`0` set, but infinitude already follows from the covering
construction alone.) -/
theorem exceptionalSet_infinite : ExceptionalSet.Infinite := by
  intro hfin
  obtain ⟨B, hB⟩ := hfin.bddAbove
  obtain ⟨n, hn, hmem⟩ := exists_exceptional_gt B
  exact absurd (hB hmem) (by omega)

/-!
## Erdős (1950), full strength: the exceptional set has positive lower density

`exceptionalSet_infinite` extracts infinitely many exceptional integers from the
covering progression `n ≡ 7629217 (mod 11184810)`, but Erdős's 1950 theorem is
stronger: a *positive proportion* of integers lie in the exceptional set.  We
now prove this by counting progression members below a horizon `N`.

Among `n < N` the progression has `N / 11184810` members `coveringAP q` with
index `q < N / 11184810`.  A member can fail the size hypothesis of
`covering_progression_mem_exceptionalSet` only if it is *trapped* within `241`
of a power of two, and each dyadic window `(2^k, 2^k + 241]` is far shorter
than the common difference `11184810`, so it traps **at most one** member;
the relevant powers of two below `N` number at most `log₂ N + 1`.  Hence at
least `N / 11184810 - (log₂ N + 1)` integers below `N` are exceptional, and
the logarithmic loss is eventually dwarfed by the linear main term: for
`N ≥ 2^52` the count is at least `N / 22369620` — a positive proportion
(`22369620 = 2 · 11184810`).
-/

/-- The `q`-th member of Erdős's covering progression
`7629217 + q · 11184810` (`11184810 = 2·3·5·7·13·17·241`). -/
def coveringAP (q : ℕ) : ℕ := 7629217 + q * 11184810

theorem coveringAP_strictMono : StrictMono coveringAP := by
  intro a b h
  unfold coveringAP
  omega

/-- `n` is *trapped* if it lies within `241` of a smaller power of two `2^k`
(`k ≥ 1`).  Trapped integers are exactly those that can fail the size
hypothesis `241 < n - 2^k` of the covering obstruction. -/
def Trapped (n : ℕ) : Prop := ∃ k, 1 ≤ k ∧ 2 ^ k < n ∧ n - 2 ^ k ≤ 241

/-- Every untrapped member of the covering progression is exceptional: the six
covering congruences and oddness hold identically along the progression, and
untrappedness is precisely the missing size hypothesis. -/
theorem coveringAP_mem_exceptionalSet {q : ℕ} (h : ¬ Trapped (coveringAP q)) :
    coveringAP q ∈ ExceptionalSet := by
  have hq : coveringAP q = 7629217 + q * 11184810 := rfl
  refine covering_progression_mem_exceptionalSet (Nat.odd_iff.mpr (by omega))
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) ?_
  intro k hk hlt
  by_contra hc
  exact h ⟨k, hk, hlt, by omega⟩

open Classical in
/-- In any index range whose progression members stay below `2 ^ m`, at most
`m` indices are trapped: a trapped index pins its member inside a window
`(2^k, 2^k + 241]` with `k < m`, and each such window — being far shorter than
the common difference `11184810` — holds at most one progression member. -/
theorem card_trapped_le {Q m : ℕ} (hQm : ∀ q, q < Q → coveringAP q < 2 ^ m) :
    ((Finset.range Q).filter fun q => Trapped (coveringAP q)).card ≤ m := by
  have hsub : ((Finset.range Q).filter fun q => Trapped (coveringAP q)) ⊆
      (Finset.range m).biUnion fun k => (Finset.range Q).filter fun q =>
        2 ^ k < coveringAP q ∧ coveringAP q - 2 ^ k ≤ 241 := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_range] at hq
    obtain ⟨hqQ, k, hk1, hklt, hkle⟩ := hq
    have hkm : k < m := by
      by_contra hc
      have hle : (2 : ℕ) ^ m ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hc)
      have := hQm q hqQ
      omega
    exact Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hkm,
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hqQ, hklt, hkle⟩⟩
  calc ((Finset.range Q).filter fun q => Trapped (coveringAP q)).card
      ≤ ((Finset.range m).biUnion fun k => (Finset.range Q).filter fun q =>
          2 ^ k < coveringAP q ∧ coveringAP q - 2 ^ k ≤ 241).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ k ∈ Finset.range m, ((Finset.range Q).filter fun q =>
          2 ^ k < coveringAP q ∧ coveringAP q - 2 ^ k ≤ 241).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _k ∈ Finset.range m, 1 := by
        refine Finset.sum_le_sum fun k _ => ?_
        refine Finset.card_le_one.mpr fun a ha b hb => ?_
        simp only [Finset.mem_filter, Finset.mem_range] at ha hb
        have h1 : coveringAP a = 7629217 + a * 11184810 := rfl
        have h2 : coveringAP b = 7629217 + b * 11184810 := rfl
        omega
    _ = m := by simp

open Classical in
/-- The number of exceptional integers below `N`. -/
noncomputable def exceptionalCount (N : ℕ) : ℕ :=
  ((Finset.range N).filter fun n => n ∈ ExceptionalSet).card

/-- **Counting form of Erdős (1950).**  Up to a logarithmic loss, the
exceptional integers below `N` are at least as numerous as the covering
progression members below `N`:
`N / 11184810 ≤ exceptionalCount N + (log₂ N + 1)`. -/
theorem exceptionalCount_lower_bound (N : ℕ) :
    N / 11184810 ≤ exceptionalCount N + (Nat.log 2 N + 1) := by
  classical
  set Q := N / 11184810 with hQdef
  set m := Nat.log 2 N + 1 with hmdef
  -- every progression member with index below `Q` lies below `N` …
  have hmem : ∀ q, q < Q → coveringAP q < N := by
    intro q hq
    have h1 : (q + 1) * 11184810 ≤ Q * 11184810 :=
      Nat.mul_le_mul (Nat.succ_le_of_lt hq) le_rfl
    have h2 : Q * 11184810 ≤ N := Nat.div_mul_le_self N 11184810
    have h3 : coveringAP q = 7629217 + q * 11184810 := rfl
    omega
  -- … hence below the dyadic horizon `2 ^ m`
  have hpow : N < 2 ^ m := hmdef ▸ Nat.lt_pow_succ_log_self (by norm_num) N
  have hmem2 : ∀ q, q < Q → coveringAP q < 2 ^ m :=
    fun q hq => lt_trans (hmem q hq) hpow
  have htrap := card_trapped_le hmem2
  -- the untrapped indices inject into the exceptional integers below `N`
  have hsubset :
      (((Finset.range Q).filter fun q => ¬ Trapped (coveringAP q)).image coveringAP) ⊆
        (Finset.range N).filter fun n => n ∈ ExceptionalSet := by
    intro n hn
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hn ⊢
    obtain ⟨q, ⟨hqQ, hqt⟩, rfl⟩ := hn
    exact ⟨hmem q hqQ, coveringAP_mem_exceptionalSet hqt⟩
  have hcard :
      ((Finset.range Q).filter fun q => ¬ Trapped (coveringAP q)).card ≤
        exceptionalCount N := by
    unfold exceptionalCount
    rw [← Finset.card_image_of_injective _ coveringAP_strictMono.injective]
    exact Finset.card_le_card hsubset
  have hsplit :
      ((Finset.range Q).filter fun q => Trapped (coveringAP q)).card +
        ((Finset.range Q).filter fun q => ¬ Trapped (coveringAP q)).card = Q := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_range]
  omega

/-- **Erdős (1950), positive-proportion form.**  For every `N ≥ 2^52` at least
`N / 22369620` of the integers below `N` are exceptional
(`22369620 = 2 · 11184810`): the exceptional set has positive lower density. -/
theorem exceptionalCount_positive_density {N : ℕ} (hN : 2 ^ 52 ≤ N) :
    N ≤ 22369620 * exceptionalCount N := by
  have h52 : (0 : ℕ) < 2 ^ 52 := by norm_num
  have hN0 : N ≠ 0 := by omega
  set L := Nat.log 2 N with hL
  have hlog52 : 52 ≤ L := (Nat.le_log_iff_pow_le (by norm_num) hN0).mpr hN
  have hpowL : 2 ^ L ≤ N := Nat.pow_log_le_self 2 hN0
  -- the logarithmic loss is dwarfed by the main term: `22369620 · (L + 2) ≤ N`
  have hloss : 22369620 * (L + 2) ≤ N := by
    set j := L - 25 with hjdef
    have hj : 27 ≤ j := by omega
    have hjpow : 2 * j ≤ 2 ^ j := by
      have h1 : j - 1 < 2 ^ (j - 1) := Nat.lt_two_pow_self
      have h2 : 2 ^ (j - 1 + 1) = 2 ^ (j - 1) * 2 := pow_succ 2 (j - 1)
      have h3 : j - 1 + 1 = j := by omega
      rw [h3] at h2
      omega
    have hL2 : L + 2 ≤ 2 ^ j := by omega
    have hsplit : (2 : ℕ) ^ 25 * 2 ^ j = 2 ^ L := by
      rw [← pow_add]
      congr 1
      omega
    have hmul : 22369620 * (L + 2) ≤ 2 ^ 25 * 2 ^ j :=
      Nat.mul_le_mul (by norm_num) hL2
    omega
  have hcount := exceptionalCount_lower_bound N
  have hdiv : 11184810 * (N / 11184810) + N % 11184810 = N := Nat.div_add_mod N 11184810
  have hmod : N % 11184810 < 11184810 := Nat.mod_lt _ (by norm_num)
  omega

open Classical in
/-- **The exceptional set has positive lower density** (the bound announced in
the Density Bounds section above): for every horizon `N` with `2^52 ≤ N + 1`,
`density ExceptionalSet N ≥ 1 / 22369620`.  Since the bound holds for *all*
sufficiently large `N`, every asymptotic density notion of `ExceptionalSet`
(lower or upper) is at least `1 / 22369620 > 0` — Erdős's 1950 theorem at full
positive-proportion strength. -/
theorem density_exceptionalSet_ge {N : ℕ} (hN : 2 ^ 52 ≤ N + 1) :
    (22369620 : ℝ)⁻¹ ≤ density ExceptionalSet N := by
  have hcount : (N + 1 : ℕ) ≤ 22369620 * exceptionalCount (N + 1) :=
    exceptionalCount_positive_density hN
  have hde : density ExceptionalSet N =
      (exceptionalCount (N + 1) : ℝ) / ((N : ℝ) + 1) := by
    unfold density exceptionalCount
    norm_num [decide_eq_true_eq, Finset.filter_congr_decidable]
  have hcast : ((N : ℝ) + 1) ≤ 22369620 * (exceptionalCount (N + 1) : ℝ) := by
    exact_mod_cast hcount
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [hde, le_div_iff₀ hpos]
  have hkey : (22369620 : ℝ)⁻¹ * ((N : ℝ) + 1) ≤
      (22369620 : ℝ)⁻¹ * (22369620 * (exceptionalCount (N + 1) : ℝ)) :=
    mul_le_mul_of_nonneg_left hcast (by norm_num)
  have hcancel : (22369620 : ℝ)⁻¹ * (22369620 * (exceptionalCount (N + 1) : ℝ)) =
      (exceptionalCount (N + 1) : ℝ) := by
    rw [← mul_assoc, inv_mul_cancel₀ (by norm_num), one_mul]
  linarith

/-- The `lowerDensity` functional of this file (an `⨅`-of-`⨆`) is positive on
the exceptional set.  `density_exceptionalSet_ge` bounds the density from below
at *every* sufficiently large horizon, so this inf-of-sup inherits the bound
`1 / 22369620`. -/
theorem lowerDensity_exceptionalSet_pos : 0 < lowerDensity ExceptionalSet := by
  have hc : (0 : ℝ) < (22369620 : ℝ)⁻¹ := by norm_num
  refine lt_of_lt_of_le hc ?_
  unfold lowerDensity
  refine le_ciInf fun N => ?_
  have hbdd : BddAbove
      (Set.range fun M : ℕ => ⨆ (_ : M ≥ N), density ExceptionalSet M) := by
    refine ⟨1, ?_⟩
    rintro x ⟨M, rfl⟩
    by_cases h : M ≥ N
    · show (⨆ (_ : M ≥ N), density ExceptionalSet M) ≤ 1
      rw [ciSup_pos h]
      exact density_le_one _ _
    · haveI : IsEmpty (M ≥ N) := ⟨h⟩
      show (⨆ (_ : M ≥ N), density ExceptionalSet M) ≤ 1
      rw [iSup_of_empty', Real.sSup_empty]
      norm_num
  refine le_trans ?_ (le_ciSup hbdd (max N (2 ^ 52)))
  show (22369620 : ℝ)⁻¹ ≤
    ⨆ (_ : max N (2 ^ 52) ≥ N), density ExceptionalSet (max N (2 ^ 52))
  rw [ciSup_pos (le_max_left N (2 ^ 52))]
  exact density_exceptionalSet_ge
    (le_trans (le_max_right _ _) (Nat.le_succ _))

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

**Formalized here (axiom-free)**: Erdős (1950) at full strength — the covering
progression puts the exceptional set at positive lower density
(`exceptionalCount_positive_density`: at least `N / 22369620` members below
every horizon `N ≥ 2^52`; `lowerDensity_exceptionalSet_pos`), strengthening
`exceptionalSet_infinite`.

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
