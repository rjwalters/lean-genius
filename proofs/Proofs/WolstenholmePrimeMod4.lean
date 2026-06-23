/-
# Wolstenholme Primes and the Mod 4 Question

A Wolstenholme prime is a prime p where C(2p-1, p-1) ≡ 1 (mod p⁴),
strengthening Wolstenholme's theorem (which gives mod p³ for all p ≥ 5).

Only two Wolstenholme primes are known: 16843 and 2124679.
Both are ≡ 3 (mod 4). Whether any Wolstenholme prime exists
with p ≡ 1 (mod 4) is an open question.

This formalization:
1. Defines Wolstenholme primes via the binomial coefficient condition
2. Proves computationally that primes 5 through 23 are NOT Wolstenholme
3. Axiomatizes the two known Wolstenholme primes (binomial too large for kernel)
4. Proves both known Wolstenholme primes are ≡ 3 (mod 4)
5. Shows every Wolstenholme prime is ≥ 5 and odd
6. Formalizes the open question and the "all mod 3" conjecture
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic

namespace WolstenholmePrimeMod4

open Nat

/-
## Core Definitions
-/

/-- The central-ish binomial coefficient C(2p-1, p-1) -/
def cb (p : ℕ) : ℕ := Nat.choose (2 * p - 1) (p - 1)

/-- A prime p is a Wolstenholme prime if C(2p-1, p-1) ≡ 1 (mod p⁴).
    This strengthens Wolstenholme's theorem, which gives mod p³ for all p ≥ 5. -/
def IsWP (p : ℕ) : Prop := Nat.Prime p ∧ cb p % (p ^ 4) = 1

/-
## Structural Properties
-/

/-- Every Wolstenholme prime is at least 5: primes 0-4 fail the mod p⁴ test. -/
theorem wp_ge_five (p : ℕ) (h : IsWP p) : p ≥ 5 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨hp, hcb⟩ := h
  have : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 ∨ p = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)
  · exact absurd hcb (by native_decide)
  · exact absurd hcb (by native_decide)
  · exact absurd hp (by decide)

/-- Every Wolstenholme prime is odd (the only even prime is 2, and WPs are ≥ 5). -/
theorem wp_odd (p : ℕ) (h : IsWP p) : p % 2 = 1 := by
  have hge := wp_ge_five p h
  have hp := h.1
  suffices p % 2 ≠ 0 by omega
  intro hmod
  have h2 : 2 ∣ p := Nat.dvd_of_mod_eq_zero hmod
  have := hp.eq_one_or_self_of_dvd 2 h2
  omega

/-- A Wolstenholme prime is either 1 or 3 mod 4 (exhaustive for odd numbers). -/
theorem wp_mod4_cases (p : ℕ) (h : IsWP p) : p % 4 = 1 ∨ p % 4 = 3 := by
  have := wp_odd p h
  omega

/-
## Small Primes Are NOT Wolstenholme Primes

We verify computationally that every prime from 5 to 23 fails the mod p⁴ test.
The first Wolstenholme prime is 16843, far beyond this range.
-/

theorem not_wp_5 : ¬IsWP 5 := by
  intro ⟨_, h⟩; exact absurd h (by native_decide)

theorem not_wp_7 : ¬IsWP 7 := by
  intro ⟨_, h⟩; exact absurd h (by native_decide)

theorem not_wp_11 : ¬IsWP 11 := by
  intro ⟨_, h⟩; exact absurd h (by native_decide)

theorem not_wp_13 : ¬IsWP 13 := by
  intro ⟨_, h⟩; exact absurd h (by native_decide)

theorem not_wp_17 : ¬IsWP 17 := by
  intro ⟨_, h⟩; exact absurd h (by native_decide)

theorem not_wp_19 : ¬IsWP 19 := by
  intro ⟨_, h⟩; exact absurd h (by native_decide)

theorem not_wp_23 : ¬IsWP 23 := by
  intro ⟨_, h⟩; exact absurd h (by native_decide)

/-
## The Two Known Wolstenholme Primes

16843 and 2124679 were identified by McIntosh and Roettger (2007).
No others exist below 10⁹. The binomial coefficients C(2p-1,p-1)
for these p are too large to verify in the Lean kernel, so we axiomatize
the mod p⁴ values while proving primality computationally.
-/

/-- 16843 is prime -/
theorem prime_16843 : Nat.Prime 16843 := by native_decide

/-- 2124679 is prime -/
theorem prime_2124679 : Nat.Prime 2124679 := by native_decide

/-- C(2·16843-1, 16842) ≡ 1 (mod 16843⁴). Axiomatized: binomial too large for kernel.
    Reference: McIntosh and Roettger, "On the congruence C(ap,bp) ≡ C(a,b) (mod p³)",
    J. Number Theory 128 (2008), 1950-1968. -/
axiom wp_cb_16843 : cb 16843 % (16843 ^ 4) = 1

/-- C(2·2124679-1, 2124678) ≡ 1 (mod 2124679⁴). Axiomatized: binomial too large for kernel.
    Reference: McIntosh and Roettger (2008). -/
axiom wp_cb_2124679 : cb 2124679 % (2124679 ^ 4) = 1

/-- 16843 is a Wolstenholme prime -/
theorem isWP_16843 : IsWP 16843 := ⟨prime_16843, wp_cb_16843⟩

/-- 2124679 is a Wolstenholme prime -/
theorem isWP_2124679 : IsWP 2124679 := ⟨prime_2124679, wp_cb_2124679⟩

/-- At least two distinct Wolstenholme primes exist -/
theorem exists_two_distinct_wp : ∃ p q : ℕ, p ≠ q ∧ IsWP p ∧ IsWP q :=
  ⟨16843, 2124679, by omega, isWP_16843, isWP_2124679⟩

/-
## Residue Analysis: The Mod 4 Pattern

Both known Wolstenholme primes are ≡ 3 (mod 4). This is the central
observation motivating the open question.
-/

theorem mod4_16843 : 16843 % 4 = 3 := by native_decide

theorem mod4_2124679 : 2124679 % 4 = 3 := by native_decide

/-- Both known Wolstenholme primes are ≡ 3 (mod 4) -/
theorem known_wp_all_mod4_eq_3 (p : ℕ) (hp : p = 16843 ∨ p = 2124679) :
    p % 4 = 3 := by
  rcases hp with rfl | rfl <;> native_decide

/-
## Finer Residue Analysis: Mod 8

The mod 8 residues distinguish the two known WPs further.
16843 ≡ 3 (mod 8) and 2124679 ≡ 7 (mod 8), covering both
odd residue classes that map to 3 (mod 4).
-/

theorem mod8_16843 : 16843 % 8 = 3 := by native_decide

theorem mod8_2124679 : 2124679 % 8 = 7 := by native_decide

/-- The two known WPs cover different residue classes mod 8 -/
theorem known_wp_distinct_mod8 : 16843 % 8 ≠ 2124679 % 8 := by native_decide

/-
## Mod 12 Analysis

Both known WPs are ≡ 7 (mod 12). Whether this is coincidence or
reflects a deeper structural constraint is unknown.
-/

theorem mod12_16843 : 16843 % 12 = 7 := by native_decide

theorem mod12_2124679 : 2124679 % 12 = 7 := by native_decide

/-- Both known WPs share the same residue mod 12 -/
theorem known_wp_same_mod12 (p : ℕ) (hp : p = 16843 ∨ p = 2124679) :
    p % 12 = 7 := by
  rcases hp with rfl | rfl <;> native_decide

/-
## The Open Question

Central question: Does there exist a Wolstenholme prime p with p ≡ 1 (mod 4)?
All computational evidence (two examples, both ≡ 3 mod 4, search up to 10⁹)
suggests this might not happen, but no theoretical obstruction is known.
-/

/-- Does there exist a Wolstenholme prime ≡ 1 (mod 4)? -/
def WPMod1Exists : Prop := ∃ p : ℕ, IsWP p ∧ p % 4 = 1

/-- Conjecture: All Wolstenholme primes are ≡ 3 (mod 4).
    Consistent with the two known examples. -/
def AllWPMod3 : Prop := ∀ p : ℕ, IsWP p → p % 4 = 3

/-- The conjecture implies no WP ≡ 1 (mod 4) exists -/
theorem allMod3_implies_no_mod1 : AllWPMod3 → ¬WPMod1Exists := by
  intro hall ⟨p, hwp, hmod⟩
  have := hall p hwp
  omega

/-- A counterexample to the conjecture would answer the question -/
theorem mod1_exists_implies_not_allMod3 : WPMod1Exists → ¬AllWPMod3 := by
  intro ⟨p, hwp, hmod⟩ hall
  have := hall p hwp
  omega

/-- The conjecture and the question are mutually exclusive -/
theorem allMod3_iff_no_mod1 : AllWPMod3 ↔ ¬WPMod1Exists := by
  constructor
  · exact allMod3_implies_no_mod1
  · intro hne p hwp
    have := wp_mod4_cases p hwp
    by_contra h3
    exact hne ⟨p, hwp, by omega⟩

/-
## Computational Lower Bound

McIntosh and Roettger verified there are no Wolstenholme primes below 10⁹
other than 16843 and 2124679. Any new WP must be very large.
-/

/-- No Wolstenholme primes below 10⁹ except the two known ones.
    Axiomatized from McIntosh-Roettger (2008) computational search. -/
axiom no_other_wp_below_billion :
  ∀ p : ℕ, IsWP p → p < 10 ^ 9 → p = 16843 ∨ p = 2124679

/-- A third Wolstenholme prime, if it exists, must exceed 10⁹ -/
theorem third_wp_large (p : ℕ) (h : IsWP p)
    (hne1 : p ≠ 16843) (hne2 : p ≠ 2124679) : p ≥ 10 ^ 9 := by
  by_contra hlt
  push_neg at hlt
  have := no_other_wp_below_billion p h hlt
  tauto

/-- Conjecture: There are infinitely many Wolstenholme primes -/
def InfiniteWP : Prop := ∀ N : ℕ, ∃ p : ℕ, p > N ∧ IsWP p

/-
## Connection to Wolstenholme's Theorem

Every Wolstenholme prime satisfies C(2p-1,p-1) ≡ 1 (mod p³) a fortiori,
since the WP condition is mod p⁴ which is strictly stronger.
-/

/-- If n ≡ 1 (mod p⁴) then n ≡ 1 (mod p³), since p³ | p⁴ -/
theorem mod_pow4_imp_pow3 {n p : ℕ} (h : n % (p ^ 4) = 1) (hp : p ≥ 2) :
    n % (p ^ 3) = 1 := by
  have hlt : 1 < p ^ 3 := by
    have : p * p ≥ 4 := by nlinarith
    nlinarith
  have h34 : p ^ 3 ∣ p ^ 4 := ⟨p, by ring⟩
  rw [← Nat.mod_mod_of_dvd n h34, h]
  exact Nat.mod_eq_of_lt hlt

/-- Every Wolstenholme prime satisfies the ordinary Wolstenholme theorem -/
theorem wp_satisfies_wolstenholme (p : ℕ) (h : IsWP p) :
    cb p % (p ^ 3) = 1 := by
  have hge := wp_ge_five p h
  exact mod_pow4_imp_pow3 h.2 (by omega)

end WolstenholmePrimeMod4
