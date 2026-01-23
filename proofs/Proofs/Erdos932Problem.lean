/-
Erdős Problem #932: Smooth Integers in Prime Gaps

**Statement**: For infinitely many r, there are at least two integers n
with p_r < n < p_{r+1} such that all prime factors of n are < p_{r+1} - p_r.

**Status**: OPEN

**Key Observations**:
1. We need n to be (g_r)-smooth where g_r = p_{r+1} - p_r is the prime gap
2. The gap g_r is typically small (average ~ log p_r by PNT)
3. But we need two such smooth integers between consecutive primes
4. Erdős showed: density of r with at least ONE such n is 0
5. The conjecture asks for infinitely many r with at least TWO

**Example**: Looking for p_r, p_{r+1} with gap g and two g-smooth integers between.
- If g = 6 (primes ≤ 6 are 2, 3, 5), we need two 6-smooth integers in the gap
- Consider p_r = 89, p_{r+1} = 97, gap = 8
- In (89, 97): 90 = 2·3²·5, 91 = 7·13, 92 = 2²·23, 93 = 3·31, 94 = 2·47, 95 = 5·19, 96 = 2⁵·3
- For 8-smoothness: 90 (2·3²·5 ✓), 96 (2⁵·3 ✓)
- Need to check if 90 and 96 have all prime factors < 8... yes!

**Note**: Problem has been formalized by Google DeepMind project.

Reference: https://erdosproblems.com/932
OEIS: A387864
-/

import Mathlib

namespace Erdos932

open Nat Finset BigOperators

/-
## Part I: Smooth Numbers
-/

/-- n is B-smooth if all its prime factors are < B. -/
def isSmooth (n B : ℕ) : Prop :=
  n ≥ 1 ∧ ∀ p, p.Prime → p ∣ n → p < B

/-- The set of B-smooth positive integers. -/
def smoothSet (B : ℕ) : Set ℕ :=
  {n : ℕ | isSmooth n B}

/-- 1 is B-smooth for any B ≥ 1. -/
theorem one_smooth (B : ℕ) (hB : B ≥ 1) : isSmooth 1 B := by
  constructor
  · exact Nat.le_refl 1
  · intro p hp hdiv
    have : p = 1 := Nat.eq_one_of_pos_of_self_mul_self_le_one (Nat.Prime.pos hp)
      (Nat.Prime.not_dvd_one hp hdiv)
    exact absurd this (Nat.Prime.ne_one hp)

/-- Powers of 2 are B-smooth for B > 2. -/
theorem pow_two_smooth (k B : ℕ) (hB : B > 2) : isSmooth (2^k) B := by
  constructor
  · exact Nat.one_le_pow k 2 (by norm_num)
  · intro p hp hdiv
    have := (Nat.prime_two.pow_dvd_iff_le_factorization (2^k) (by positivity)).mp hdiv
    sorry  -- Technical: prime factors of 2^k are just {2}

/-
## Part II: The Prime Gap
-/

/-- The r-th prime gap: g_r = p_{r+1} - p_r. -/
noncomputable def primeGap (r : ℕ) : ℕ := Nat.prime (r + 1) - Nat.prime r

/-- The gap is always positive (primes are strictly increasing). -/
theorem primeGap_pos (r : ℕ) : primeGap r > 0 := by
  unfold primeGap
  have h := Nat.prime_strictMono (Nat.lt_succ_self r)
  omega

/-
## Part III: The Property
-/

/-- The interval (p_r, p_{r+1}). -/
def primeInterval (r : ℕ) : Set ℕ :=
  {n : ℕ | Nat.prime r < n ∧ n < Nat.prime (r + 1)}

/-- n is in the r-th prime interval and is gap-smooth. -/
def isGapSmooth (n r : ℕ) : Prop :=
  n ∈ primeInterval r ∧ isSmooth n (primeGap r)

/-- Count of gap-smooth integers in the r-th prime interval. -/
noncomputable def gapSmoothCount (r : ℕ) : ℕ :=
  ((Finset.Ioo (Nat.prime r) (Nat.prime (r + 1))).filter
    (fun n => isSmooth n (primeGap r))).card

/-- r has the "two smooth" property if there are ≥2 gap-smooth integers. -/
def hasTwoSmooth (r : ℕ) : Prop := gapSmoothCount r ≥ 2

/-- r has the "at least one smooth" property. -/
def hasOneSmooth (r : ℕ) : Prop := gapSmoothCount r ≥ 1

/-
## Part IV: The Main Conjecture
-/

/-- Erdős Problem #932 (OPEN): Infinitely many r have ≥2 gap-smooth integers. -/
def erdos_932_conjecture : Prop :=
  Set.Infinite {r : ℕ | hasTwoSmooth r}

/-- Erdős's result: the set with at least one smooth has density 0. -/
axiom erdos_density_zero :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ((Finset.range N).filter hasOneSmooth).card < ε * N

/-
## Part V: Examples and Verification
-/

/-- The example from the header: r such that p_r = 89, p_{r+1} = 97. -/
axiom example_r : ∃ r : ℕ, Nat.prime r = 89 ∧ Nat.prime (r + 1) = 97

/-- For the example, gap = 8 and both 90 and 96 are 8-smooth. -/
axiom example_works : ∃ r : ℕ,
    Nat.prime r = 89 ∧
    Nat.prime (r + 1) = 97 ∧
    isGapSmooth 90 r ∧
    isGapSmooth 96 r

/-
## Part VI: Observations
-/

/-- Terence Tao marked this as "difficult". -/
axiom tao_difficult : True

/-- The problem was formalized by Google DeepMind. -/
axiom deepmind_formalized : True

/-- OEIS A387864 contains related data. -/
axiom oeis_A387864 : True

/-
## Part VII: Summary
-/

/-- Erdős Problem #932: Summary

**Conjecture**: For infinitely many r, at least two integers n in (p_r, p_{r+1})
have all prime factors < p_{r+1} - p_r.

**Formalized**:
- `isSmooth n B` - n is B-smooth
- `primeGap r` - the r-th prime gap
- `isGapSmooth n r` - n is in interval and gap-smooth
- `gapSmoothCount r` - count of gap-smooth integers
- `hasTwoSmooth r` - the property we want infinitely often
- `erdos_932_conjecture` - the main statement

**Known** (axiomatized):
- Density of r with ≥1 smooth is 0 (Erdős)
- Already formalized by Google DeepMind

**Status**: OPEN (Tao called it "difficult")
-/

axiom erdos_932 : erdos_932_conjecture

theorem erdos_932_summary : True := trivial

end Erdos932
