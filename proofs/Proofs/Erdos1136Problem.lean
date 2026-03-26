/-
Erdős Problem #1136: Sum-Free Sets Avoiding Powers of Two

Source: https://erdosproblems.com/1136
Status: SOLVED (Müller, 2011)

Statement:
Does there exist A ⊂ ℕ with lower density > 1/3 such that
a + b ≠ 2^k for any a, b ∈ A and k ≥ 0?

Answer: YES — Müller constructed such a set with density 1/2,
which is optimal.

Construction:
A = {n ∈ ℕ : n ≡ 3·2^i (mod 2^{i+2}) for some i ≥ 0}

This set has density 1/2 and no two elements sum to a power of 2.
Müller also proved that 1/2 is the maximum achievable density.

History:
- Erdős (1987): Posed at DMV conference in Berlin
- Trivial: Multiples of 3 give density 1/3
- Müller (2011): Achieved density 1/2, proved optimal

Reference: [Mu11] Müller, J.
Tags: number-theory, density, additive-combinatorics, sum-free-sets
-/

import Mathlib

open Finset Filter

namespace Erdos1136

-- ## Part I: Core Definitions

/-- A set A ⊂ ℕ avoids power-of-two sums if no two elements sum to 2^k. -/
def AvoidsPowerOfTwoSums (A : Set ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ A → b ∈ A → ∀ k : ℕ, a + b ≠ 2 ^ k

/-- The lower (asymptotic) density of a set A ⊂ ℕ:
    d̲(A) = liminf_{N→∞} |A ∩ {0,...,N-1}| / N. -/
noncomputable def lowerDensity (A : Set ℕ) : ℝ :=
  Filter.liminf (fun N : ℕ => ((Finset.range N).filter (· ∈ A)).card / (N : ℝ)) atTop

-- ## Part II: Properties of the Avoidance Condition

/-- The empty set trivially avoids power-of-two sums. -/
theorem avoids_empty : AvoidsPowerOfTwoSums ∅ :=
  fun _ _ ha => absurd ha (Set.not_mem_empty _)

/-- Avoidance is monotone: subsets of avoiding sets also avoid. -/
theorem avoids_mono {A B : Set ℕ} (h : A ⊆ B) (hB : AvoidsPowerOfTwoSums B) :
    AvoidsPowerOfTwoSums A :=
  fun a b ha hb k => hB a b (h ha) (h hb) k

/-- 3 does not divide any power of 2. -/
theorem not_three_dvd_two_pow (k : ℕ) : ¬(3 ∣ 2 ^ k) := by
  intro h
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by decide)
  have h3 : (3 : ℕ) ∣ Nat.gcd (2 ^ k) 3 := Nat.dvd_gcd h dvd_rfl
  rw [hcop] at h3
  exact absurd h3 (by decide)

-- ## Part III: Trivial Bound (Multiples of 3)

/-- Multiples of 3 avoid power-of-two sums. -/
theorem multiples_of_3_avoid (a b k : ℕ) (ha : 3 ∣ a) (hb : 3 ∣ b) :
    a + b ≠ 2 ^ k := by
  intro h
  exact not_three_dvd_two_pow k (h ▸ dvd_add ha hb)

/-- The set of multiples of 3 avoids power-of-two sums. -/
theorem multiples_of_3_set_avoids :
    AvoidsPowerOfTwoSums {n : ℕ | 3 ∣ n} :=
  fun a b ha hb k => multiples_of_3_avoid a b k ha hb

/-- The set of multiples of 3 has lower density 1/3. -/
axiom multiples_of_3_density :
    lowerDensity {n : ℕ | 3 ∣ n} = 1 / 3

-- ## Part IV: Müller's Construction

/-- **Müller's Set**: n ∈ M iff n ≡ 3·2^i (mod 2^{i+2}) for some i ≥ 0. -/
def MullerSet : Set ℕ :=
  {n : ℕ | ∃ i : ℕ, n % (2 ^ (i + 2)) = 3 * 2 ^ i}

/-- 0 is not in the Müller set. -/
theorem zero_not_mem_muller : (0 : ℕ) ∉ MullerSet := by
  intro ⟨i, hi⟩
  simp at hi
  have : 0 < 3 * 2 ^ i := by positivity
  omega

/-- 3 is in the Müller set: 3 mod 4 = 3 = 3·2^0. -/
theorem three_mem_muller : (3 : ℕ) ∈ MullerSet :=
  ⟨0, by norm_num⟩

-- ## Part IV-A: Proof that Müller's Set Avoids Power-of-Two Sums
--
-- Strategy: If a ∈ MullerSet (witnessed by i) and b ∈ MullerSet
-- (witnessed by j), with i ≤ j, and a + b = 2^k, then:
-- 1. k ≥ i+2 (since a ≥ 3·2^i > 2^(i+1) ≥ 2^k when k ≤ i+1)
-- 2. Working mod 2^(i+2): b ≡ 2^i (mod 2^(i+2))
-- 3. But j = i requires b ≡ 3·2^i, j = i+1 gives b ≡ 2^(i+1),
--    j ≥ i+2 gives b ≡ 0, all contradicting b ≡ 2^i.

/-- Key modular computation: if a + b = 2^k, a ≡ 3·2^i (mod 2^(i+2)),
    and k ≥ i+2, then b ≡ 2^i (mod 2^(i+2)).

    Proof: 2^(i+2) | 2^k, so (a+b) mod 2^(i+2) = 0.
    By Nat.add_mod, (3·2^i + b mod 2^(i+2)) mod 2^(i+2) = 0.
    The sum lies in (0, 2·2^(i+2)), so it must equal 2^(i+2) = 4·2^i.
    Hence b mod 2^(i+2) = 4·2^i - 3·2^i = 2^i. -/
private lemma b_mod_eq_pow_i {a b k i : ℕ} (hab : a + b = 2 ^ k)
    (ha : a % (2 ^ (i + 2)) = 3 * 2 ^ i) (hk : i + 2 ≤ k) :
    b % (2 ^ (i + 2)) = 2 ^ i := by
  set m := 2 ^ (i + 2) with hm_def
  have hm_pos : 0 < m := by positivity
  have hm_eq : m = 4 * 2 ^ i := by rw [hm_def]; ring
  -- (a + b) % m = 0 since m | 2^k
  have hdvd : m ∣ (a + b) := by rw [hab]; exact Nat.pow_dvd_pow 2 hk
  obtain ⟨c_ab, hc_ab⟩ := hdvd
  have hab_mod : (a + b) % m = 0 := by rw [hc_ab]; exact Nat.mul_mod_right m c_ab
  -- Rewrite: (3 * 2^i + b % m) % m = 0
  rw [Nat.add_mod, ha] at hab_mod
  set r := b % m with hr_def
  have hr_lt : r < m := Nat.mod_lt b hm_pos
  -- Extract divisibility: m | (3 * 2^i + r)
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hab_mod
  -- Bounds: 0 < 3*2^i + r < 2*m
  have hsum_pos : 0 < 3 * 2 ^ i + r := by positivity
  have hsum_lt : 3 * 2 ^ i + r < 2 * m := by rw [hm_eq]; omega
  -- q must be 1: only multiple of m in (0, 2m) is m
  have hq_pos : 0 < q := by
    rcases q with _ | q'; · simp [mul_zero] at hq; omega; · exact Nat.succ_pos _
  have hq_le : q ≤ 1 := by nlinarith [hm_pos]
  have hq1 : q = 1 := by omega
  -- 3 * 2^i + r = m * 1 = 4 * 2^i, so r = 2^i
  rw [hq1, mul_one] at hq; omega

/-- When b is witnessed by j = i+1 in MullerSet, b mod 2^(i+2) = 2^(i+1). -/
private lemma muller_mod_down {b i : ℕ}
    (hb : b % (2 ^ (i + 1 + 2)) = 3 * 2 ^ (i + 1)) :
    b % (2 ^ (i + 2)) = 2 ^ (i + 1) := by
  set m := 2 ^ (i + 2) with hm_def
  have hm_pos : 0 < m := by positivity
  -- 2^(i+2) | 2^(i+3), so b % m = (b % 2^(i+3)) % m
  have hdvd : m ∣ 2 ^ (i + 1 + 2) := by rw [hm_def]; exact Nat.pow_dvd_pow 2 (by omega)
  rw [← Nat.mod_mod_of_dvd b hdvd, hb]
  -- Goal: (3 * 2^(i+1)) % m = 2^(i+1)
  -- 3 * 2^(i+1) = m + 2^(i+1) since m = 2^(i+2) = 2 * 2^(i+1)
  have h3eq : 3 * 2 ^ (i + 1) = m + 2 ^ (i + 1) := by rw [hm_def]; ring
  have hlt : 2 ^ (i + 1) < m := by rw [hm_def]; exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [h3eq, Nat.add_mod, Nat.mod_self, zero_add,
      Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]

/-- When b is witnessed by j ≥ i+2 in MullerSet, b mod 2^(i+2) = 0. -/
private lemma muller_mod_zero {b i j : ℕ} (hjge : i + 2 ≤ j)
    (hb : b % (2 ^ (j + 2)) = 3 * 2 ^ j) :
    b % (2 ^ (i + 2)) = 0 := by
  have hdvd_outer : 2 ^ (i + 2) ∣ 2 ^ (j + 2) := Nat.pow_dvd_pow 2 (by omega)
  rw [← Nat.mod_mod_of_dvd b hdvd_outer, hb]
  -- Goal: (3 * 2^j) % 2^(i+2) = 0
  -- 2^(i+2) | 2^j (since j ≥ i+2), so 2^(i+2) | 3*2^j
  have hdvd_val : 2 ^ (i + 2) ∣ 3 * 2 ^ j :=
    dvd_mul_of_dvd_right (Nat.pow_dvd_pow 2 hjge) 3
  obtain ⟨c, hc⟩ := hdvd_val
  rw [hc, Nat.mul_mod_right]

/-- Core: no a, b with the MullerSet witnesses i ≤ j can sum to a power of 2.

    For a+b=2^k with a≡3·2^i (mod 2^(i+2)):
    - k≥i+2 is forced (otherwise a>2^k)
    - Then b≡2^i (mod 2^(i+2))
    - But b∈MullerSet witnessed by j gives j=i→3·2^i, j=i+1→2^(i+1), j≥i+2→0,
      all contradicting 2^i. -/
private lemma muller_avoids_ordered {a b i j k : ℕ} (hij : i ≤ j)
    (hai : a % (2 ^ (i + 2)) = 3 * 2 ^ i)
    (hbj : b % (2 ^ (j + 2)) = 3 * 2 ^ j)
    (hab : a + b = 2 ^ k) : False := by
  -- k must be ≥ i+2, otherwise a ≥ 3·2^i > 2^(i+1) ≥ 2^k
  have hk : i + 2 ≤ k := by
    by_contra hlt
    push_neg at hlt
    have ha_ge : 3 * 2 ^ i ≤ a := hai ▸ Nat.mod_le a _
    have hpow : 2 ^ k ≤ 2 ^ (i + 1) := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega)
    have h21 : 2 ^ (i + 1) = 2 * 2 ^ i := by ring
    omega
  -- Compute b % 2^(i+2) = 2^i
  have hbmod := b_mod_eq_pow_i hab hai hk
  -- Case split on j
  rcases eq_or_ne j i with rfl | hne_i
  · -- j = i: hbj gives b % 2^(i+2) = 3*2^i, contradicting hbmod = 2^i
    rw [hbmod] at hbj; omega
  · rcases eq_or_ne j (i + 1) with rfl | hne_i1
    · -- j = i+1: muller_mod_down gives b % 2^(i+2) = 2^(i+1), contradicting 2^i
      have hbmod2 := muller_mod_down hbj
      rw [hbmod] at hbmod2
      -- hbmod2 : 2^i = 2^(i+1), but 2^i < 2^(i+1)
      have hlt_pow : 2 ^ i < 2 ^ (i + 1) := by
        calc 2 ^ i < 2 ^ i * 2 := by omega
          _ = 2 ^ (i + 1) := by ring
      omega
    · -- j ≥ i+2: muller_mod_zero gives b % 2^(i+2) = 0, contradicting 2^i > 0
      have hjge : i + 2 ≤ j := by omega
      have := muller_mod_zero hjge hbj
      rw [hbmod] at this
      exact absurd this (by positivity)

/-- **Müller's Set avoids power-of-two sums (PROVED).**

    The proof uses modular arithmetic: for any a, b ∈ MullerSet with witnesses
    i ≤ j, if a+b = 2^k then b mod 2^(i+2) must equal both 2^i (from the sum
    constraint) and one of {3·2^i, 2^(i+1), 0} (from b's MullerSet membership),
    which is always a contradiction. -/
theorem muller_avoids : AvoidsPowerOfTwoSums MullerSet := by
  intro a b ⟨i, hai⟩ ⟨j, hbj⟩ k hab
  rcases le_total i j with h | h
  · exact muller_avoids_ordered h hai hbj hab
  · exact muller_avoids_ordered h hbj hai (by omega)

-- ## Part IV-B: Density Axioms

/-- **Müller's density result (Müller 2011):**
    The Müller set has lower density exactly 1/2. Left as axiom since
    Mathlib lacks asymptotic density infrastructure. -/
axiom muller_density : lowerDensity MullerSet = 1 / 2

/-- **Optimality (Müller 2011):**
    Any set avoiding power-of-two sums has lower density at most 1/2. -/
axiom muller_optimality (A : Set ℕ) :
    AvoidsPowerOfTwoSums A → lowerDensity A ≤ 1 / 2

-- ## Part V: Main Result

/-- **Erdős Problem #1136: SOLVED**

    There exists A ⊂ ℕ with lower density > 1/3 such that
    a + b ≠ 2^k for any a, b ∈ A and k ≥ 0.

    In fact, the maximum achievable density is exactly 1/2. -/
theorem erdos_1136 :
    ∃ A : Set ℕ, AvoidsPowerOfTwoSums A ∧ lowerDensity A > 1 / 3 :=
  ⟨MullerSet, muller_avoids, by linarith [muller_density]⟩

/-- The optimal density is exactly 1/2: achieved by Müller's set and
    no set can do better. -/
theorem erdos_1136_optimal :
    (∃ A : Set ℕ, AvoidsPowerOfTwoSums A ∧ lowerDensity A = 1 / 2) ∧
    (∀ A : Set ℕ, AvoidsPowerOfTwoSums A → lowerDensity A ≤ 1 / 2) :=
  ⟨⟨MullerSet, muller_avoids, muller_density⟩, muller_optimality⟩

-- ## Part VI: Consequences

/-- The Müller set strictly improves on the multiples-of-3 construction. -/
theorem muller_beats_trivial :
    lowerDensity MullerSet > lowerDensity {n : ℕ | 3 ∣ n} := by
  rw [muller_density, multiples_of_3_density]; norm_num

/-- The density improvement from trivial to optimal is exactly 1/6. -/
theorem density_gap :
    lowerDensity MullerSet - lowerDensity {n : ℕ | 3 ∣ n} = 1 / 6 := by
  rw [muller_density, multiples_of_3_density]; ring

/-- Every prime p with p ∤ 2 gives a set of multiples avoiding power-of-two
    sums, since p ∤ 2^k for any k. -/
theorem odd_prime_multiples_avoid (p : ℕ) (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (a b k : ℕ) (ha : p ∣ a) (hb : p ∣ b) : a + b ≠ 2 ^ k := by
  intro h
  have hcop : Nat.Coprime (2 ^ k) p := by
    apply Nat.Coprime.pow_left
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr (fun h2p => hp2 (Nat.dvd_antisymm h2p
      (hp.dvd_of_dvd_pow (dvd_pow_self 2 (Nat.Prime.pos hp).ne' ▸ h2p.symm ▸
        dvd_refl (2 ^ 1)))))
  have hdvd : p ∣ Nat.gcd (2 ^ k) p := Nat.dvd_gcd (h ▸ dvd_add ha hb) dvd_rfl
  rw [hcop] at hdvd
  exact absurd hdvd (Nat.Prime.not_dvd_one hp)

/-
## Summary

**Problem Status: SOLVED (Müller 2011)**

Erdős Problem #1136 asked whether there exists A ⊂ ℕ with lower density > 1/3
such that no two elements sum to a power of 2.

**Answer: YES** — Müller achieved density 1/2, which is optimal.

**Proved Theorems**:
- avoids_empty: Empty set avoids (trivial)
- avoids_mono: Avoidance is monotone under subsets
- not_three_dvd_two_pow: 3 ∤ 2^k via coprimality
- multiples_of_3_avoid: 3|a ∧ 3|b → a+b ≠ 2^k
- multiples_of_3_set_avoids: {n : 3|n} avoids power-of-two sums
- zero_not_mem_muller: 0 ∉ MullerSet
- three_mem_muller: 3 ∈ MullerSet
- **muller_avoids: MullerSet avoids power-of-two sums (NEW — proved via mod arithmetic)**
- erdos_1136: Problem SOLVED (density > 1/3 exists)
- erdos_1136_optimal: Optimal density is exactly 1/2
- muller_beats_trivial: Müller set beats multiples-of-3
- density_gap: Gap is exactly 1/6
- odd_prime_multiples_avoid: General result for odd primes

**Axioms (3 → 3, but conjunctive axiom split — avoidance half now proved)**:
- multiples_of_3_density: Density of {3|n} is 1/3 (analysis)
- muller_density: Müller set has density 1/2 (was half of muller_construction)
- muller_optimality: No avoiding set has density > 1/2 (deep combinatorics)

**Key change**: The old `muller_construction` axiom bundled avoidance + density.
Now avoidance is PROVED via modular arithmetic, density remains axiomatized.

References:
- Müller, J. (2011). Sum-free sets avoiding powers of two.
- Erdős, P. (1987). Problem posed at DMV conference, Berlin.
-/

end Erdos1136
