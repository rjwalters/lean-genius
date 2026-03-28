/-
Erdős Problem #932: Smooth Numbers in Prime Gaps

Source: https://erdosproblems.com/932
Status: OPEN

Statement:
Let p_k denote the k-th prime. For infinitely many r, there are at least two
integers p_r < n < p_{r+1} all of whose prime factors are < p_{r+1} - p_r.

In other words, the gap between consecutive primes p_r and p_{r+1} contains
at least two numbers that are "smooth" relative to the gap size.

Known Results:
- Erdős proved: The density of r such that at least ONE such n exists is 0.
- This means such r are rare, but Erdős conjectured infinitely many exist.

Key Insight:
A number n is called B-smooth if all its prime factors are ≤ B. The problem
asks: for infinitely many prime gaps [p_r, p_{r+1}], does the gap contain
at least two numbers that are (gap-size)-smooth?

The density-zero result for the "at least one" variant shows that prime gaps
large enough to contain smooth numbers (relative to their size) are sparse.

OEIS: A387864

References:
- Formal Conjectures Project (Google DeepMind)
- Original Erdős problem collection
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

open Nat Finset

attribute [local instance] Classical.propDecidable

namespace Erdos932

/- ## Part I: Basic Definitions -/

/--
**The n-th Prime**

The n-th prime number in the sequence 2, 3, 5, 7, 11, ...
Using Mathlib's `Nat.nth Nat.Prime`.
-/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- nthPrime 0 = 2 -/
theorem nthPrime_zero : nthPrime 0 = 2 := by
  unfold nthPrime; exact Nat.nth_prime_zero_eq_two

/-- nthPrime 1 = 3 -/
theorem nthPrime_one : nthPrime 1 = 3 := by
  unfold nthPrime; exact Nat.nth_prime_one_eq_three

/-- The n-th prime is prime. -/
theorem nthPrime_prime (n : ℕ) : (nthPrime n).Prime := by
  unfold nthPrime; exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

/-- The sequence of primes is strictly increasing. -/
theorem nthPrime_strictMono : StrictMono nthPrime := by
  intro a b hab; unfold nthPrime
  exact Nat.nth_strictMono Nat.infinite_setOf_prime hab

/- ## Part II: Prime Gap -/

/--
**Prime Gap**

The gap between the n-th and (n+1)-th prime: g_n = p_{n+1} - p_n
-/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-- The first prime gap: p_1 - p_0 = 3 - 2 = 1. -/
theorem primeGap_zero : primeGap 0 = 1 := by
  unfold primeGap nthPrime
  simp [Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]

/-- Prime gaps are positive. -/
theorem primeGap_pos (n : ℕ) : primeGap n > 0 :=
  Nat.sub_pos_of_lt (nthPrime_strictMono (Nat.lt_succ_self n))

/- ## Part III: Smooth Numbers -/

/-- Maximum of a list of natural numbers via foldr. Returns 0 for empty list. -/
private def listMax (l : List ℕ) : ℕ := l.foldr max 0

private lemma listMax_le {l : List ℕ} {B : ℕ} (h : ∀ x ∈ l, x ≤ B) :
    listMax l ≤ B := by
  induction l with
  | nil => simp [listMax, List.foldr]
  | cons hd tl ih =>
    simp only [listMax, List.foldr]
    apply max_le
    · exact h hd (by simp)
    · exact ih (fun x hx => h x (by simp [hx]))

/--
**Maximum Prime Factor**

The largest prime dividing n, or 0 if n ≤ 1.
-/
noncomputable def maxPrimeFactor (n : ℕ) : ℕ :=
  if _ : n > 1 then listMax n.primeFactorsList else 0

/-- 1 has no prime factors, so maxPrimeFactor 1 = 0. -/
theorem maxPrimeFactor_one : maxPrimeFactor 1 = 0 := by
  simp [maxPrimeFactor]

/-- For prime p, maxPrimeFactor p = p. -/
theorem maxPrimeFactor_prime (p : ℕ) (hp : p.Prime) : maxPrimeFactor p = p := by
  unfold maxPrimeFactor
  rw [dif_pos hp.one_lt, Nat.primeFactorsList_prime hp]
  simp [listMax, List.foldr]

/-- maxPrimeFactor(ab) = max(maxPrimeFactor(a), maxPrimeFactor(b)) for coprime a, b > 1. -/
private lemma listMax_append (l₁ l₂ : List ℕ) :
    listMax (l₁ ++ l₂) = max (listMax l₁) (listMax l₂) := by
  induction l₁ with
  | nil => simp [listMax, List.foldr]
  | cons hd tl ih =>
    simp only [listMax, List.foldr, List.cons_append] at *
    rw [ih]; omega

private lemma listMax_perm {l₁ l₂ : List ℕ} (h : l₁.Perm l₂) :
    listMax l₁ = listMax l₂ := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp [listMax, List.foldr, ih]
  | swap x y l => simp [listMax, List.foldr]; omega
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

theorem maxPrimeFactor_mul (a b : ℕ) (ha : a > 1) (hb : b > 1) (_hcop : Nat.Coprime a b) :
    maxPrimeFactor (a * b) = max (maxPrimeFactor a) (maxPrimeFactor b) := by
  unfold maxPrimeFactor
  rw [dif_pos (by omega : a * b > 1), dif_pos ha, dif_pos hb]
  have hperm := Nat.perm_primeFactorsList_mul (by omega : a ≠ 0) (by omega : b ≠ 0)
  rw [listMax_perm hperm, listMax_append]

/--
**B-Smooth Number**

A positive integer n is B-smooth if all its prime factors are ≤ B.
Equivalently, maxPrimeFactor n ≤ B (with the convention that 1 is B-smooth for any B).
-/
def isSmooth (B n : ℕ) : Prop := maxPrimeFactor n ≤ B

/-- 1 is B-smooth for any B. -/
theorem one_isSmooth (B : ℕ) : isSmooth B 1 := by
  simp [isSmooth, maxPrimeFactor_one]

/-- Powers of primes ≤ B are B-smooth. -/
theorem prime_power_isSmooth (p k B : ℕ) (hp : p.Prime) (hpB : p ≤ B) (hk : k > 0) :
    isSmooth B (p ^ k) := by
  unfold isSmooth maxPrimeFactor
  rw [dif_pos (one_lt_pow (by omega : k ≠ 0) hp.one_lt)]
  apply listMax_le
  intro q hq
  have hqp : q.Prime := Nat.prime_of_mem_primeFactorsList hq
  have hqd : q ∣ p ^ k := Nat.dvd_of_mem_primeFactorsList hq
  have hqdp : q ∣ p := hqp.dvd_of_dvd_pow hqd
  have : q = p := (hp.eq_one_or_self_of_dvd q hqdp).resolve_left hqp.one_lt.ne'
  omega

/- ## Part IV: Smooth Numbers in Prime Gap -/

/--
**The Open Interval Between Consecutive Primes**

The integers strictly between p_r and p_{r+1}.
-/
noncomputable def primesGapInterval (r : ℕ) : Finset ℕ :=
  Finset.Ioo (nthPrime r) (nthPrime (r + 1))

/-- The gap interval is nonempty iff the prime gap is > 1. -/
theorem primesGapInterval_nonempty_iff (r : ℕ) :
    (primesGapInterval r).Nonempty ↔ primeGap r > 1 := by
  simp only [primesGapInterval, primeGap]
  constructor
  · intro ⟨x, hx⟩
    simp only [Finset.mem_Ioo] at hx
    omega
  · intro h
    have hlt : nthPrime r < nthPrime (r + 1) :=
      nthPrime_strictMono (Nat.lt_succ_self r)
    exact ⟨nthPrime r + 1, Finset.mem_Ioo.mpr ⟨by omega, by omega⟩⟩

/--
**Smooth Numbers in Gap**

The set of numbers in the prime gap (p_r, p_{r+1}) that are smooth
relative to the gap size (i.e., all prime factors < p_{r+1} - p_r).
-/
noncomputable def smoothInGap (r : ℕ) : Finset ℕ :=
  (primesGapInterval r).filter (fun n => maxPrimeFactor n < primeGap r)

/--
**Count of Smooth Numbers in Gap**

How many numbers in the gap are smooth relative to the gap size.
-/
noncomputable def smoothCount (r : ℕ) : ℕ := (smoothInGap r).card

/- ## Part V: The Main Conjecture (OPEN) -/

/--
**Erdős Problem #932 (OPEN)**

For infinitely many r, there are at least TWO integers n in (p_r, p_{r+1})
such that all prime factors of n are smaller than p_{r+1} - p_r.

Formally: { r : ℕ | smoothCount r ≥ 2 } is infinite.
-/
def erdos932Condition (r : ℕ) : Prop := smoothCount r ≥ 2

axiom erdos_932 : { r : ℕ | erdos932Condition r }.Infinite

/-- Alternative formulation using the formal-conjectures style. -/
theorem erdos_932_alt :
    { r : ℕ | 2 ≤ (Finset.Ioo (nthPrime r) (nthPrime (r + 1)) |>.filter
      (fun m => maxPrimeFactor m < nthPrime (r + 1) - nthPrime r)).card }.Infinite := by
  convert erdos_932 using 1

/- ## Part VI: The Density-Zero Result (SOLVED) -/

/--
**Natural Density**

A set S ⊆ ℕ has natural density d if
  lim_{N→∞} |{ n ∈ S : n ≤ N }| / N = d
-/
noncomputable def HasDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Filter.Tendsto
    (fun N : ℕ => ((Finset.filter (· ∈ S) (Finset.range (N + 1))).card : ℝ) / (↑N + 1))
    Filter.atTop
    (nhds d)

/--
**Erdős's Result (SOLVED)**

The density of r such that at least ONE n in (p_r, p_{r+1}) is smooth
relative to the gap size is 0.

This shows that such prime gaps are rare.
-/
def erdos932WeakCondition (r : ℕ) : Prop := smoothCount r ≥ 1

axiom erdos_932_density_zero :
    HasDensity { r : ℕ | erdos932WeakCondition r } 0

/-- Alternative formulation. -/
theorem erdos_932_variants_one_le :
    HasDensity { r : ℕ | 1 ≤ (Finset.Ioo (nthPrime r) (nthPrime (r + 1)) |>.filter
      (fun m => maxPrimeFactor m < nthPrime (r + 1) - nthPrime r)).card } 0 := by
  convert erdos_932_density_zero using 1

/- ## Part VII: Examples and Analysis -/

/-
**Example Analysis**

For small primes, let's see what the gaps look like:
- p_0 = 2, p_1 = 3, gap = 1: Interval (2,3) is empty
- p_1 = 3, p_2 = 5, gap = 2: Interval (3,5) = {4}. Is 4 smooth? maxPrimeFactor(4) = 2 < 2? No.
- p_2 = 5, p_3 = 7, gap = 2: Interval (5,7) = {6}. maxPrimeFactor(6) = 3 < 2? No.
- p_3 = 7, p_4 = 11, gap = 4: Interval (7,11) = {8,9,10}.
  - 8 = 2³: maxPrimeFactor = 2 < 4? Yes, smooth!
  - 9 = 3²: maxPrimeFactor = 3 < 4? Yes, smooth!
  - 10 = 2·5: maxPrimeFactor = 5 < 4? No.
  So smoothCount(3) = 2, satisfying the condition!
-/

/-- For r = 3 (gap from 7 to 11), there are 2 smooth numbers. -/
axiom example_r3 : smoothCount 3 = 2

/-- This confirms r = 3 satisfies the Erdős condition. -/
theorem example_satisfies : erdos932Condition 3 := by
  unfold erdos932Condition; have := example_r3; omega

/- ## Part VIII: Why This Is Hard -/

/-
**The Difficulty**

The challenge is proving INFINITELY MANY r exist with smoothCount r ≥ 2.

Erdős's density-zero result shows that even finding ONE smooth number in
most gaps is impossible. The smooth numbers must satisfy:
  p_r < n < p_{r+1}  and  maxPrimeFactor(n) < p_{r+1} - p_r

For n to be smooth with bound B = primeGap(r), we need:
- n is in a short interval (the prime gap)
- n has only small prime factors (< B)

Large prime gaps tend to have larger B, but they're also rare. The
interplay between gap size and smooth number distribution is subtle.
-/

/- ## Part IX: Connection to Smooth Number Distribution -/

/-
**Smooth Number Counting Function**

Ψ(x, y) = |{ n ≤ x : n is y-smooth }|

The distribution of smooth numbers is well-studied:
- Ψ(x, y) ≈ x · ρ(log x / log y) where ρ is the Dickman function
- When y = x^(1/u), roughly x^(1-ε) numbers ≤ x are y-smooth

The problem asks about smooth numbers in a specific short interval.
-/

/-- Ψ(x, y) counts y-smooth numbers up to x. -/
noncomputable def smoothCountUpTo (x y : ℕ) : ℕ :=
  (Finset.Icc 1 x).filter (isSmooth y) |>.card

/-- Smooth numbers become rarer as the smoothness bound decreases. -/
theorem smoothCountUpTo_mono (x y₁ y₂ : ℕ) (h : y₁ ≤ y₂) :
    smoothCountUpTo x y₁ ≤ smoothCountUpTo x y₂ := by
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, le_trans hn.2 h⟩

/- ## Part X: Summary -/

/-
**Erdős Problem #932: Summary**

**Question:** For infinitely many r, are there at least 2 integers in (p_r, p_{r+1})
whose prime factors are all smaller than the gap p_{r+1} - p_r?

**Status:** OPEN

**Known:**
- Density of r with at least 1 such integer is 0 (Erdős, SOLVED)
- r = 3 (gap 7 to 11) works: 8 = 2³ and 9 = 3² are both 4-smooth

**Key Challenge:**
Proving infinitely many such gaps exist despite their density being zero.
-/
theorem erdos_932_summary :
    HasDensity { r : ℕ | smoothCount r ≥ 1 } 0 ∧
    smoothCount 3 ≥ 2 :=
  ⟨erdos_932_density_zero, by have := example_r3; omega⟩

end Erdos932
