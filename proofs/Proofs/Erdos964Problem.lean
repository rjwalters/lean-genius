/-
Erdős Problem #964: Ratios of Consecutive Divisor Function Values

Source: https://erdosproblems.com/964
Status: SOLVED (Eberhard 2025)

Statement:
Let τ(n) count the number of divisors of n. Is the sequence
  τ(n+1)/τ(n)
everywhere dense in (0, ∞)?

Answer: YES - Eberhard (2025) proved this unconditionally

Background:
- τ(n) = |{d : d | n}| is the divisor counting function
- The question asks: for any r > 0 and ε > 0, does there exist n with
  |τ(n+1)/τ(n) - r| < ε?
- Even stronger: ALL positive rationals appear as τ(n+1)/τ(n)

Historical:
- This follows from the prime k-tuple conjecture
- Eberhard (2025) proved it unconditionally
- Related to Problem #946

Tags: number-theory, divisor-function, density
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Divisors
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.Order.Basic

open Set Real
open scoped Topology

namespace Erdos964

/-
## Part I: The Divisor Function
-/

/--
**Divisor counting function τ(n):**
The number of positive divisors of n.
-/
def tau (n : ℕ) : ℕ :=
  (Nat.divisors n).card

/--
**Basic properties:**
τ(1) = 1, τ(p) = 2 for prime p, τ(p^k) = k+1
-/
theorem tau_one : tau 1 = 1 := by
  simp [tau, Nat.divisors]

theorem tau_prime (p : ℕ) (hp : Nat.Prime p) : tau p = 2 := by
  simp [tau, Nat.divisors_prime hp]

theorem tau_prime_power (p k : ℕ) (hp : Nat.Prime p) :
    tau (p ^ k) = k + 1 := by
  simp [tau, Nat.divisors_prime_pow hp, Finset.card_map]

/--
**Multiplicativity:**
τ is multiplicative: τ(mn) = τ(m)τ(n) when gcd(m,n) = 1.
-/
theorem tau_multiplicative (m n : ℕ) (h : Nat.Coprime m n) :
    tau (m * n) = tau m * tau n := by
  simp only [tau, h.divisors_mul, Finset.card_product]

/-
## Part II: Ratios of Consecutive Values
-/

/--
**Divisor ratio:**
The ratio τ(n+1)/τ(n) for consecutive integers.
-/
noncomputable def divisorRatio (n : ℕ) : ℝ :=
  if h : tau n ≠ 0 then (tau (n + 1) : ℝ) / (tau n : ℝ) else 0

/--
**Set of all ratios:**
The set {τ(n+1)/τ(n) : n ≥ 1}.
-/
noncomputable def ratioSet : Set ℝ :=
  {r : ℝ | ∃ n : ℕ, n ≥ 1 ∧ divisorRatio n = r}

/-
## Part III: The Erdős Conjecture
-/

/--
**Everywhere dense:**
A set S ⊆ ℝ is everywhere dense in (0, ∞) if its closure contains (0, ∞).
-/
def isDenseInPositives (S : Set ℝ) : Prop :=
  ∀ r : ℝ, r > 0 → ∀ ε > 0, ∃ s ∈ S, |s - r| < ε

/--
**The Erdős conjecture:**
Is {τ(n+1)/τ(n) : n ≥ 1} dense in (0, ∞)?
-/
def ErdosConjecture964 : Prop :=
  isDenseInPositives ratioSet

/-
## Part IV: Eberhard's Theorem
-/

/--
**Eberhard's theorem (2025):**
All positive rationals appear as τ(n+1)/τ(n).
-/
axiom eberhard_theorem :
    ∀ p q : ℕ, p ≥ 1 → q ≥ 1 → ∃ n : ℕ, n ≥ 1 ∧ tau (n + 1) * q = tau n * p

/--
**Corollary: Rationals are in the ratio set:**
-/
theorem rationals_in_ratio_set (p q : ℕ) (hp : p ≥ 1) (hq : q ≥ 1) :
    (p : ℝ) / q ∈ ratioSet := by
  obtain ⟨n, hn, heq⟩ := eberhard_theorem p q hp hq
  refine ⟨n, hn, ?_⟩
  have htau_ne : tau n ≠ 0 := by
    unfold tau
    exact ne_of_gt (Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩⟩)
  simp only [divisorRatio, htau_ne, ne_eq, not_false_eq_true, dite_true]
  rw [div_eq_div_iff (Nat.cast_ne_zero.mpr htau_ne) (Nat.cast_ne_zero.mpr (by omega : q ≠ 0))]
  exact_mod_cast heq.trans (mul_comm (tau n) p)

/--
**Rationals are dense in (0, ∞):**
-/
theorem rationals_dense_in_positives :
    isDenseInPositives {r : ℝ | ∃ p q : ℕ, p ≥ 1 ∧ q ≥ 1 ∧ r = (p : ℝ) / q} := by
  intro r hr ε hε
  -- Find q large enough that 1/q < ε, and p = ⌈r*q⌉
  obtain ⟨q, hq⟩ := exists_nat_gt (max (1 / ε) 1)
  have hq_pos : (0 : ℝ) < ↑q := by
    calc (0 : ℝ) < 1 := one_pos
      _ ≤ max (1 / ε) 1 := le_max_right _ _
      _ < ↑q := hq
  have hq_ge : q ≥ 1 := by
    have : q ≠ 0 := by exact_mod_cast hq_pos.ne'
    omega
  set p := Nat.ceil (r * ↑q)
  have hrq_pos : r * ↑q > 0 := mul_pos hr hq_pos
  have hp_ge : p ≥ 1 := by
    have := Nat.ceil_pos.mpr hrq_pos
    omega
  -- The approximation ⌈r*q⌉/q is within 1/q of r
  have hceil_ge : r * ↑q ≤ ↑p := Nat.le_ceil _
  have hceil_lt : (↑p : ℝ) < r * ↑q + 1 := Nat.ceil_lt_add_one (le_of_lt hrq_pos)
  -- 1/q < ε since q > 1/ε
  have h_inv_lt : 1 / (↑q : ℝ) < ε := by
    rw [div_lt_iff hq_pos, mul_comm ε ↑q]
    exact (div_lt_iff hε).mp (lt_of_le_of_lt (le_max_left _ _) hq)
  use ↑p / ↑q
  refine ⟨⟨p, q, hp_ge, hq_ge, rfl⟩, ?_⟩
  -- |p/q - r| = p/q - r (since p/q ≥ r) and p/q - r < 1/q < ε
  have h_nonneg : (↑p : ℝ) / ↑q - r ≥ 0 := by
    rw [sub_nonneg, le_div_iff hq_pos]
    exact hceil_ge
  rw [abs_of_nonneg h_nonneg]
  calc (↑p : ℝ) / ↑q - r
      < (r * ↑q + 1) / ↑q - r := by
        exact sub_lt_sub_right ((div_lt_div_right hq_pos).mpr hceil_lt) r
    _ = 1 / ↑q := by field_simp; ring
    _ < ε := h_inv_lt

/--
**Main theorem: The conjecture is TRUE**
-/
theorem erdos_964_true : ErdosConjecture964 := by
  intro r hr ε hε
  -- Since rationals are dense and contained in ratioSet
  obtain ⟨s, ⟨p, q, hp, hq, hs⟩, hdist⟩ := rationals_dense_in_positives r hr ε hε
  use s
  constructor
  · rw [hs]
    exact rationals_in_ratio_set p q hp hq
  · exact hdist

/-
## Part V: Examples and Special Cases
-/

/--
**Example: τ(2)/τ(1) = 2:**
τ(2) = 2, τ(1) = 1, so ratio = 2.
-/
example : divisorRatio 1 = 2 := by
  have h1 : tau 1 ≠ 0 := by native_decide
  have h2 : tau 1 = 1 := by native_decide
  have h3 : tau 2 = 2 := by native_decide
  simp only [divisorRatio, show (1 : ℕ) + 1 = 2 from rfl, h1, h2, h3,
    ne_eq, not_false_eq_true, dite_true, Nat.cast_ofNat, Nat.cast_one]
  norm_num

/--
**Example: τ(3)/τ(2) = 1:**
τ(3) = 2, τ(2) = 2, so ratio = 1.
-/
example : divisorRatio 2 = 1 := by
  have h1 : tau 2 ≠ 0 := by native_decide
  have h2 : tau 2 = 2 := by native_decide
  have h3 : tau 3 = 2 := by native_decide
  simp only [divisorRatio, show (2 : ℕ) + 1 = 3 from rfl, h1, h2, h3,
    ne_eq, not_false_eq_true, dite_true, Nat.cast_ofNat]
  norm_num

/--
**Example: τ(4)/τ(3) = 3/2:**
τ(4) = 3, τ(3) = 2, so ratio = 3/2.
-/
example : divisorRatio 3 = 3/2 := by
  have h1 : tau 3 ≠ 0 := by native_decide
  have h2 : tau 3 = 2 := by native_decide
  have h3 : tau 4 = 3 := by native_decide
  simp only [divisorRatio, show (3 : ℕ) + 1 = 4 from rfl, h1, h2, h3,
    ne_eq, not_false_eq_true, dite_true, Nat.cast_ofNat]
  norm_num

/--
**Small ratios:**
τ(n+1)/τ(n) can be arbitrarily small.
-/
/--
**Large ratios:**
τ(n+1)/τ(n) can be arbitrarily large.
-/
/-
## Part VI: Connection to Prime k-Tuple Conjecture
-/

/--
**Prime k-tuple conjecture:**
For any admissible k-tuple (h₁, ..., hₖ), there exist infinitely many n
such that n + h₁, ..., n + hₖ are all prime.
-/
def PrimeKTupleConjecture : Prop :=
  ∀ k : ℕ, ∀ h : Fin k → ℕ,
    (∀ p : ℕ, Nat.Prime p → ∃ i, (h i : ℤ) % p ≠ 0) →
    ∃ᶠ n in Filter.atTop, ∀ i, Nat.Prime (n + h i)

/--
**The conjecture implies density:**
Under the prime k-tuple conjecture, density follows easily.
-/
/--
**Eberhard's unconditional proof:**
Eberhard proved the density result without assuming any unproved conjectures.
-/
/-
## Part VII: Stronger Results
-/

/--
**All positive rationals appear:**
This is stronger than just density.
-/
def AllRationalsAppear : Prop :=
  ∀ p q : ℕ, p ≥ 1 → q ≥ 1 →
    ∃ n : ℕ, n ≥ 1 ∧ divisorRatio n = (p : ℝ) / q

/--
**Eberhard's strong result:**
-/
theorem eberhard_strong : AllRationalsAppear := by
  intro p q hp hq
  obtain ⟨n, hn, heq⟩ := eberhard_theorem p q hp hq
  refine ⟨n, hn, ?_⟩
  have htau_ne : tau n ≠ 0 := by
    unfold tau
    exact ne_of_gt (Finset.card_pos.mpr ⟨1, Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩⟩)
  simp only [divisorRatio, htau_ne, ne_eq, not_false_eq_true, dite_true]
  rw [div_eq_div_iff (Nat.cast_ne_zero.mpr htau_ne) (Nat.cast_ne_zero.mpr (by omega : q ≠ 0))]
  exact_mod_cast heq.trans (mul_comm (tau n) p)

/--
**Related: Problem #946:**
Problem 946 asks related questions about divisor function values.
-/

/-
## Part VIII: Statistics of the Ratio
-/

/--
**Average ratio:**
The average value of τ(n+1)/τ(n) over n ≤ N.
-/
noncomputable def averageRatio (N : ℕ) : ℝ :=
  (∑ n ∈ Finset.range N, divisorRatio (n + 1)) / N

/--
**The average is 1:**
On average, τ(n+1) ≈ τ(n).
-/
/--
**Distribution of log ratios:**
log(τ(n+1)/τ(n)) has a limiting distribution.
-/
/-
## Part IX: Summary

**Erdős Problem #964: SOLVED**

**Question:** Is {τ(n+1)/τ(n) : n ≥ 1} dense in (0, ∞)?

**Answer:** YES (Eberhard 2025)

**Even stronger:** ALL positive rationals appear as τ(n+1)/τ(n).

**Key insight:** By carefully choosing n, we can make consecutive
integers have any prescribed ratio of divisor counts.

**Related:** Problem #946, prime k-tuple conjecture
-/

/--
**Main result: Erdős #964 is SOLVED**
-/
theorem erdos_964 : ErdosConjecture964 := erdos_964_true

/--
**The answer:**
-/
theorem erdos_964_answer :
    ∀ r : ℝ, r > 0 → ∀ ε > 0, ∃ n : ℕ, n ≥ 1 ∧ |divisorRatio n - r| < ε :=
  erdos_964

end Erdos964
