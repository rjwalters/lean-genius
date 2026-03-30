/-
Erdős Problem #1100: Coprime Consecutive Divisors

Source: https://erdosproblems.com/1100
Status: OPEN

Statement:
Let 1 = d₁ < d₂ < ... < d_τ(n) = n be the divisors of n.
Define τ⊥(n) = count of i where gcd(dᵢ, dᵢ₊₁) = 1.

Questions:
1. Does τ⊥(n)/ω(n) → ∞ for almost all n?
2. Is τ⊥(n) < exp((log n)^o(1)) for all n?
3. For squarefree n with ω(n) = k, what is g(k) = max τ⊥(n)?

Known Results:
- τ⊥(n) ≥ ω(n) trivially (with equality for infinitely many n)
- Erdős-Hall: max_{n<x} τ⊥(n) > exp((log log x)^(2-ε))
- Erdős-Simonovits: (√2 + o(1))^k < g(k) < (2-c)^k for some c > 0

References:
- Erdős, Hall (1978): "On some unconventional problems on the divisors of integers"
- Erdős (1981): Compilation [Er81h]
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Real Nat Finset

namespace Erdos1100

/-
## Part I: Divisor Functions
-/

/--
**Divisors of n (sorted):**
The list of divisors of n in increasing order: 1 = d₁ < d₂ < ... < d_τ(n) = n.
-/
noncomputable def divisorList (n : ℕ) : List ℕ :=
  (Finset.filter (· ∣ n) (Finset.range (n + 1))).sort (· ≤ ·)

/--
**τ(n): Number of divisors**
-/
def tau (n : ℕ) : ℕ := (Finset.filter (· ∣ n) (Finset.range (n + 1))).card

/--
**ω(n): Number of distinct prime divisors**
-/
def omega (n : ℕ) : ℕ := n.primeFactors.card

/-
## Part II: Coprime Consecutive Divisors
-/

/--
**τ⊥(n): Count of coprime consecutive divisor pairs**
Count the number of indices i where gcd(dᵢ, dᵢ₊₁) = 1.
-/
noncomputable def tauPerp (n : ℕ) : ℕ :=
  let divs := divisorList n
  (List.range (divs.length - 1)).filter
    (fun i => Nat.gcd (divs.getD i 0) (divs.getD (i + 1) 0) = 1)
  |>.length

/--
**Basic property: τ⊥(n) ≥ ω(n)**
At minimum, consecutive prime powers contribute coprime pairs.
-/
theorem tau_perp_lower_bound (n : ℕ) (hn : n > 0) : tauPerp n ≥ omega n := by sorry

/--
**Helper: divisors of a prime p are exactly {1, p}.**
-/
private lemma divisors_of_prime (p : ℕ) (hp : Nat.Prime p) :
    Finset.filter (· ∣ p) (Finset.range (p + 1)) = {1, p} := by
  ext d
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨_, hd_dvd⟩
    exact hp.eq_one_or_self_of_dvd d hd_dvd
  · rintro (rfl | rfl)
    · exact ⟨by omega, one_dvd p⟩
    · exact ⟨by omega, dvd_refl p⟩

/--
**Helper: divisorList of a prime is [1, p].**
-/
private lemma divisorList_prime (p : ℕ) (hp : Nat.Prime p) :
    divisorList p = [1, p] := by
  unfold divisorList
  rw [divisors_of_prime p hp]
  -- Goal: ({1, p} : Finset ℕ).sort (· ≤ ·) = [1, p]
  -- Characterize by length, membership, sorted, nodup
  set L := ({1, p} : Finset ℕ).sort (· ≤ ·) with hL_def
  have hlen : L.length = 2 := by
    rw [hL_def, Finset.length_sort]
    rw [Finset.card_insert_of_not_mem (show (1 : ℕ) ∉ ({p} : Finset ℕ) by simp [hp.one_lt.ne'])]
    simp
  obtain ⟨a, b, hab_eq⟩ := List.length_eq_two.mp hlen
  have hmem : ∀ x, x ∈ L ↔ x ∈ ({1, p} : Finset ℕ) := fun x => Finset.mem_sort _
  have hsorted := Finset.sort_sorted (· ≤ ·) ({1, p} : Finset ℕ)
  rw [hab_eq] at hsorted
  -- a ≤ b from sorted
  have hle : a ≤ b := List.pairwise_cons.mp hsorted |>.1 b (List.mem_cons_self b [])
  -- a, b ∈ {1, p}
  have ha : a = 1 ∨ a = p := by
    simpa using (hmem a).mp (hab_eq ▸ List.mem_cons_self a [b])
  have hb : b = 1 ∨ b = p := by
    simpa using (hmem b).mp (hab_eq ▸ List.mem_cons.mpr (Or.inr (List.mem_cons_self b [])))
  -- a ≠ b (1 and p both in L, so if a = b then 1 = p, contradicting p > 1)
  have hne : a ≠ b := by
    intro heq; subst heq
    have h1L : (1 : ℕ) ∈ L := (hmem 1).mpr (by simp)
    have hpL : p ∈ L := (hmem p).mpr (by simp)
    rw [hab_eq] at h1L hpL; simp at h1L hpL; omega
  rw [hab_eq]
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hne
  · rfl
  · omega
  · exact absurd rfl hne

/--
**Helper: τ⊥(p) = 1 for any prime p.**
For prime p, divisors are [1, p] and gcd(1, p) = 1.
-/
private lemma tauPerp_prime (p : ℕ) (hp : Nat.Prime p) :
    tauPerp p = 1 := by
  unfold tauPerp
  rw [divisorList_prime p hp]
  -- divs = [1, p], length = 2, range (2-1) = range 1 = [0]
  -- filter: gcd(getD [1,p] 0 0)(getD [1,p] 1 0) = gcd 1 p = 1 ✓
  simp [List.getD, List.get?, Nat.gcd_one_left]

/--
**Helper: ω(p) = 1 for any prime p.**
-/
private lemma omega_prime (p : ℕ) (hp : Nat.Prime p) :
    omega p = 1 := by
  unfold omega
  rw [hp.primeFactors_eq]
  simp

/--
**Equality achieved infinitely often:**
There exist infinitely many n with τ⊥(n) = ω(n).
Proof: For any prime p, τ⊥(p) = 1 = ω(p), and there are infinitely many primes.
-/
theorem tau_perp_equality_infinitely_often :
    ∀ N : ℕ, ∃ n : ℕ, n > N ∧ tauPerp n = omega n := by
  intro N
  obtain ⟨p, hp_gt, hp_prime⟩ := Nat.exists_infinite_primes (N + 1)
  exact ⟨p, by omega, by rw [tauPerp_prime p hp_prime, omega_prime p hp_prime]⟩

/-
## Part III: Question 1 - Almost All Growth
-/

/--
**Question 1 (OPEN):**
Does τ⊥(n)/ω(n) → ∞ for almost all n?

"Almost all" means the set of exceptions has density 0.
-/
def question1_almost_all_growth : Prop :=
  ∀ M : ℝ, M > 0 →
    -- The density of n with τ⊥(n)/ω(n) < M tends to 0
    ∀ ε > 0, ∃ X : ℕ, ∀ x : ℕ, x ≥ X →
      (Finset.filter
        (fun n => (tauPerp n : ℝ) / (omega n) < M ∧ omega n > 0)
        (Finset.range x)).card / (x : ℝ) < ε

/--
**Status of Question 1: OPEN**
-/
theorem question1_open : True := trivial

/-
## Part IV: Question 2 - Upper Bound
-/

/--
**Question 2 (OPEN):**
Is τ⊥(n) < exp((log n)^o(1)) for all n?

This asks if τ⊥(n) grows slower than any fixed power of log n.
-/
def question2_upper_bound : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    (tauPerp n : ℝ) < exp ((log n)^ε)

/--
**Erdős-Hall lower bound on the maximum:**
For all ε > 0 and sufficiently large x:
  max_{n<x} τ⊥(n) > exp((log log x)^(2-ε))
-/
theorem erdos_hall_max_lower_bound :
    ∀ ε > 0, ∃ X : ℕ, ∀ x : ℕ, x ≥ X →
      ∃ n : ℕ, n < x ∧ (tauPerp n : ℝ) > exp ((log (log x))^(2 - ε)) := by sorry

/--
**Status of Question 2: OPEN**
-/
theorem question2_open : True := trivial

/-
## Part V: Question 3 - Growth of g(k)
-/

/--
**g(k): Maximum τ⊥ among squarefree n with exactly k prime factors**
-/
noncomputable def g (k : ℕ) : ℕ :=
  sSup { tauPerp n | n : ℕ, Squarefree n ∧ omega n = k }

/--
**Erdős-Simonovits bounds on g(k):**
(√2 + o(1))^k < g(k) < (2-c)^k for some constant c > 0.
-/
theorem erdos_simonovits_bounds :
    ∃ c : ℝ, c > 0 ∧
      -- Lower bound
      (∀ ε > 0, ∃ K : ℕ, ∀ k : ℕ, k ≥ K →
        (g k : ℝ) > (Real.sqrt 2 - ε)^k) ∧
      -- Upper bound
      (∃ K : ℕ, ∀ k : ℕ, k ≥ K →
        (g k : ℝ) < (2 - c)^k) := by sorry

/--
**The growth rate of g(k):**
The base of exponential growth is between √2 ≈ 1.414 and 2-c < 2.
The lower bound is asymptotic: for any ε > 0, g(k) ≥ (√2 - ε)^k eventually.
-/
theorem g_exponential_growth :
    ∃ β : ℝ, β < 2 ∧
      -- Asymptotic lower bound approaching √2
      (∀ ε > 0, ∃ K : ℕ, ∀ k : ℕ, k ≥ K →
        (Real.sqrt 2 - ε)^k ≤ (g k : ℝ)) ∧
      -- Eventual upper bound
      (∃ K : ℕ, ∀ k : ℕ, k ≥ K →
        (g k : ℝ) ≤ β^k) := by
  obtain ⟨c, hc, hlower, hupper⟩ := erdos_simonovits_bounds
  refine ⟨2 - c, by linarith, ?_, ?_⟩
  · intro ε hε
    obtain ⟨K, hK⟩ := hlower ε hε
    exact ⟨K, fun k hk => le_of_lt (hK k hk)⟩
  · obtain ⟨K, hK⟩ := hupper
    exact ⟨K, fun k hk => le_of_lt (hK k hk)⟩

/-
## Part VI: Examples
-/

/--
**Example: n = 6**
Divisors: 1, 2, 3, 6
- gcd(1,2) = 1 ✓
- gcd(2,3) = 1 ✓
- gcd(3,6) = 3 ✗
τ⊥(6) = 2, ω(6) = 2
-/
example : omega 6 = 2 := by native_decide

/--
**Example: n = 12**
Divisors: 1, 2, 3, 4, 6, 12
- gcd(1,2) = 1 ✓
- gcd(2,3) = 1 ✓
- gcd(3,4) = 1 ✓
- gcd(4,6) = 2 ✗
- gcd(6,12) = 6 ✗
τ⊥(12) = 3, ω(12) = 2
-/
example : omega 12 = 2 := by native_decide

/-
## Part VII: Why This Problem Is Hard
-/

/--
**Structural Insight:**
The coprime consecutive divisors depend delicately on the factorization of n.
For n = p₁^a₁ · ... · p_k^a_k:
- Consecutive divisors differ by multiplying/dividing by primes
- Coprimality requires the consecutive divisors to share no common prime
- This creates intricate combinatorial constraints

The exponential bounds on g(k) show the structure is neither trivial nor chaotic.
-/
theorem structural_insight : True := trivial

/-
## Part VIII: Summary
-/

/--
**Erdős Problem #1100: Status**

**Definition:**
τ⊥(n) = number of coprime consecutive divisor pairs of n.

**Questions:**
1. τ⊥(n)/ω(n) → ∞ for almost all n? **OPEN**
2. τ⊥(n) < exp((log n)^o(1)) for all n? **OPEN**
3. Growth rate of g(k) = max τ⊥(n) for squarefree n with ω(n) = k?
   **Partially known:** (√2)^k < g(k) < (2-c)^k

**Key Results:**
- τ⊥(n) ≥ ω(n) (trivial lower bound)
- max_{n<x} τ⊥(n) > exp((log log x)^(2-ε)) [Erdős-Hall]
- Erdős-Simonovits bounds on g(k)
-/
theorem erdos_1100_summary :
    -- τ⊥(n) ≥ ω(n)
    (∀ n : ℕ, n > 0 → tauPerp n ≥ omega n) ∧
    -- Equality for infinitely many n
    (∀ N : ℕ, ∃ n : ℕ, n > N ∧ tauPerp n = omega n) ∧
    -- Erdős-Hall lower bound on max
    (∀ ε > 0, ∃ X : ℕ, ∀ x : ℕ, x ≥ X →
      ∃ n : ℕ, n < x ∧ (tauPerp n : ℝ) > exp ((log (log x))^(2 - ε))) := by
  constructor
  · exact tau_perp_lower_bound
  constructor
  · exact tau_perp_equality_infinitely_often
  · exact erdos_hall_max_lower_bound

end Erdos1100
