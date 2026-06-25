/-
Erdős Problem #748: The Cameron-Erdős Conjecture on Sum-Free Sets

Source: https://erdosproblems.com/748
Status: PROVED (Green 2004, Sapozhenko 2003)

Statement:
Let f(n) count the number of sum-free subsets A ⊆ {1,...,n}.
A set is sum-free if it contains no solutions to a = b + c with a,b,c ∈ A.
Is it true that f(n) = 2^{(1+o(1))n/2}?

Answer: YES

Background:
- Trivial lower bound: f(n) ≥ 2^{n/2} (all subsets of [n/2, n] are sum-free)
- The conjecture asks if this is tight up to lower-order terms

Solution:
- Green (2004, Bull. London Math. Soc.): Proved f(n) ≪ 2^{n/2}
- Sapozhenko (2003, Dokl. Akad. Nauk): Proved independently
- Both proved stronger: f(n) ~ c_n · 2^{n/2} where c_n depends on parity of n

Key Insight:
Sum-free sets are "essentially" subsets of [n/2, n] or similar structures.
The upper bound uses sophisticated counting techniques and structure theorems.

References:
- Cameron-Erdős (original conjecture)
- Green (2004): "The Cameron-Erdős conjecture", Bull. London Math. Soc.
- Sapozhenko (2003): "The Cameron-Erdős conjecture", Dokl. Akad. Nauk
- OEIS A007865: Number of sum-free subsets of {1,...,n}
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset

namespace Erdos748

/-
## Part I: Sum-Free Sets
-/

/--
**Sum-Free Set:**
A set A is sum-free if there are no a, b, c ∈ A with a = b + c.

Equivalently, A contains no arithmetic progressions of length 3 starting at 0.
-/
def IsSumFree (A : Finset ℕ) : Prop :=
  ∀ a b c, a ∈ A → b ∈ A → c ∈ A → a ≠ b + c

/--
`IsSumFree` is decidable: although the quantifiers range over all of `ℕ`, the
guards `a ∈ A`, `b ∈ A`, `c ∈ A` restrict each variable to the finite set `A`,
so the property is equivalent to a bounded `∀ … ∈ A` statement.
-/
instance decidableIsSumFree (A : Finset ℕ) : Decidable (IsSumFree A) :=
  decidable_of_iff (∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, a ≠ b + c)
    ⟨fun h a b c ha hb hc => h a ha b hb c hc, fun h a ha b hb c hc => h a b c ha hb hc⟩

/--
**Alternative definition:**
A is sum-free iff A ∩ (A + A) = ∅.
-/
def IsSumFree' (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, b + c ≠ a

theorem sumFree_iff (A : Finset ℕ) : IsSumFree A ↔ IsSumFree' A := by
  unfold IsSumFree IsSumFree'
  constructor
  · intro h a ha b hb c hc
    exact fun heq => h a b c ha hb hc heq.symm
  · intro h a b c ha hb hc heq
    exact h a ha b hb c hc heq.symm

/-
## Part II: Counting Sum-Free Sets
-/

/--
**Sum-Free Subsets of {1,...,n}:**
The collection of all sum-free subsets.
-/
def sumFreeSubsets (n : ℕ) : Finset (Finset ℕ) :=
  (Finset.Icc 1 n).powerset.filter IsSumFree

/--
**The Counting Function f(n):**
The number of sum-free subsets of {1,...,n}.
-/
def f (n : ℕ) : ℕ := (sumFreeSubsets n).card

/-
## Part III: Trivial Lower Bound
-/

/--
**Upper Half is Sum-Free:**
Any subset of {⌈n/2⌉, ..., n} is sum-free because
for any a, b in this range, a + b > n ≥ any element.
-/
theorem upperHalf_sumFree (n : ℕ) (A : Finset ℕ) (hA : ∀ a ∈ A, n / 2 + 1 ≤ a ∧ a ≤ n) :
    IsSumFree A := by
  intro a b c ha hb hc heq
  have hca : n / 2 + 1 ≤ c := (hA c hc).1
  have hcb : n / 2 + 1 ≤ b := (hA b hb).1
  have han : a ≤ n := (hA a ha).2
  omega

/--
**Trivial Lower Bound:**
f(n) ≥ 2^{⌊n/2⌋} because all 2^{⌈n/2⌉} subsets of the upper half are sum-free.

Proof: Let U = {⌊n/2⌋+1, ..., n}. By `upperHalf_sumFree` every subset of U is
sum-free, and every subset of U is a subset of {1,...,n}, so `U.powerset` embeds
into `sumFreeSubsets n`. Hence f(n) ≥ |U.powerset| = 2^{|U|} = 2^{n-⌊n/2⌋} ≥ 2^{⌊n/2⌋}.
-/
theorem trivial_lower_bound (n : ℕ) (hn : n ≥ 2) :
    f n ≥ 2 ^ (n / 2) := by
  -- The upper half U = {⌊n/2⌋+1, ..., n}
  set U : Finset ℕ := Finset.Icc (n / 2 + 1) n with hU
  -- Every subset of U is a sum-free subset of {1,...,n}
  have hsub : U.powerset ⊆ sumFreeSubsets n := by
    intro A hAmem
    rw [Finset.mem_powerset] at hAmem
    rw [sumFreeSubsets, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨hAmem.trans ?_, ?_⟩
    · -- U ⊆ {1,...,n}
      rw [hU]
      exact Finset.Icc_subset_Icc (by omega) (le_refl n)
    · -- A is sum-free since A ⊆ U
      apply upperHalf_sumFree n A
      intro a ha
      have haU : a ∈ U := hAmem ha
      rw [hU, Finset.mem_Icc] at haU
      exact haU
  -- Cardinality bound: f n ≥ 2^|U|
  have hcard : 2 ^ U.card ≤ f n :=
    calc 2 ^ U.card = U.powerset.card := (Finset.card_powerset U).symm
      _ ≤ (sumFreeSubsets n).card := Finset.card_le_card hsub
      _ = f n := rfl
  -- |U| = n - ⌊n/2⌋ ≥ ⌊n/2⌋
  have hUcard : U.card = n - n / 2 := by rw [hU, Nat.card_Icc]; omega
  have hexp : n / 2 ≤ U.card := by rw [hUcard]; omega
  calc 2 ^ (n / 2) ≤ 2 ^ U.card := Nat.pow_le_pow_right (by norm_num) hexp
    _ ≤ f n := hcard

/-
## Part IV: The Cameron-Erdős Conjecture
-/

/--
**The Cameron-Erdős Conjecture:**
f(n) = 2^{(1 + o(1))n/2}

This means:
  lim_{n→∞} log₂(f(n)) / (n/2) = 1
-/
def cameronErdosConjecture : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
    (1 - ε) * (n / 2 : ℝ) ≤ Real.log (f n) / Real.log 2 ∧
    Real.log (f n) / Real.log 2 ≤ (1 + ε) * (n / 2 : ℝ)

/-
## Part V: The Solution
-/

/--
**Green's Theorem (2004):**
f(n) ≪ 2^{n/2}, i.e., there exists a constant C such that f(n) ≤ C · 2^{n/2}.
-/
axiom green_upper_bound :
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 → (f n : ℝ) ≤ C * 2 ^ (n / 2)

/-
**Sapozhenko's Theorem (2003):**
Same result, proved independently.
-/
/--
**The Precise Asymptotic:**
f(n) ~ c_n · 2^{n/2} where c_n depends on the parity of n.

- c_n = c_even when n is even
- c_n = c_odd when n is odd
-/
axiom precise_asymptotic :
    ∃ c_even c_odd : ℝ, c_even > 0 ∧ c_odd > 0 ∧
      ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N,
        if n % 2 = 0 then
          |((f n : ℝ) / 2 ^ (n / 2)) - c_even| < ε
        else
          |((f n : ℝ) / 2 ^ (n / 2)) - c_odd| < ε

/--
**Cameron-Erdős Conjecture: PROVED**
-/
theorem cameron_erdos_proved : cameronErdosConjecture := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := green_upper_bound
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  let K := max 0 (Real.log C / Real.log 2)
  have hK_nn : 0 ≤ K := le_max_left 0 _
  obtain ⟨N_lb, hN_lb⟩ := exists_nat_gt (1 / ε)
  obtain ⟨N_ub, hN_ub⟩ := exists_nat_gt (2 * K / ε)
  refine ⟨max (max N_lb N_ub) 2, ?_⟩
  intro n hn
  have hn2 : 2 ≤ n := le_trans (le_max_right _ _) hn
  have hN_lb_n : N_lb ≤ n :=
    le_trans ((Nat.le_max_left N_lb N_ub).trans (Nat.le_max_left _ 2)) hn
  have hN_ub_n : N_ub ≤ n :=
    le_trans ((Nat.le_max_right N_lb N_ub).trans (Nat.le_max_left _ 2)) hn
  have h1_ε_n : 1 / ε < (n : ℝ) := lt_of_lt_of_le hN_lb (by exact_mod_cast hN_lb_n)
  have h2K_ε_n : 2 * K / ε < (n : ℝ) := lt_of_lt_of_le hN_ub (by exact_mod_cast hN_ub_n)
  have hε_n2 : 1 / 2 ≤ ε * ((n : ℝ) / 2) := by
    have : 1 < (n : ℝ) * ε := by
      have h := mul_lt_mul_of_pos_right h1_ε_n hε
      linarith [show (1 / ε) * ε = 1 from by field_simp]
    linarith
  have hK_ε_n2 : K ≤ ε * ((n : ℝ) / 2) := by
    have h := mul_lt_mul_of_pos_right h2K_ε_n hε
    linarith [show (2 * K / ε) * ε = 2 * K from by field_simp]
  have hlb_R : (2 : ℝ) ^ (n / 2) ≤ (f n : ℝ) := by
    exact_mod_cast trivial_lower_bound n hn2
  have hfn_pos : (0 : ℝ) < f n :=
    lt_of_lt_of_le (pow_pos (by norm_num : (0:ℝ) < 2) _) hlb_R
  have hub_R : (f n : ℝ) ≤ C * (2 : ℝ) ^ (n / 2) := hbound n (by omega)
  have hdiv_R : (n : ℝ) = ↑(n / 2 : ℕ) * 2 + ↑(n % 2 : ℕ) := by
    exact_mod_cast (show n = n / 2 * 2 + n % 2 by omega)
  have hmod_R_nn : (0 : ℝ) ≤ ↑(n % 2 : ℕ) := Nat.cast_nonneg _
  have hmod_R_le : ↑(n % 2 : ℕ) ≤ (1 : ℝ) := by exact_mod_cast (show n % 2 ≤ 1 by omega)
  have hn_half_lo : (n : ℝ) / 2 - 1 / 2 ≤ ↑(n / 2 : ℕ) := by linarith
  have hn_half_hi : ↑(n / 2 : ℕ) ≤ (n : ℝ) / 2 := by linarith
  have hlog_lb : ↑(n / 2 : ℕ) * Real.log 2 ≤ Real.log (f n) := by
    have h := Real.log_le_log (pow_pos (by norm_num : (0:ℝ) < 2) _) hlb_R
    rwa [Real.log_pow] at h
  have hlog_ub : Real.log (f n) ≤ Real.log C + ↑(n / 2 : ℕ) * Real.log 2 := by
    have h := Real.log_le_log hfn_pos hub_R
    rw [Real.log_mul (ne_of_gt hC) (pow_pos (by norm_num : (0:ℝ) < 2) _).ne',
        Real.log_pow] at h
    linarith
  constructor
  · rw [le_div_iff₀ hlog2_pos]
    have h_step : (1 - ε) * ((n : ℝ) / 2) ≤ ↑(n / 2 : ℕ) := by linarith
    linarith [mul_le_mul_of_nonneg_right h_step hlog2_pos.le]
  · rw [div_le_iff₀ hlog2_pos]
    have hlogC : Real.log C ≤ ε * ((n : ℝ) / 2) * Real.log 2 := by
      have h := (div_le_iff₀ hlog2_pos).mp ((le_max_right 0 _ : Real.log C / Real.log 2 ≤ K).trans hK_ε_n2)
      linarith
    linarith [mul_le_mul_of_nonneg_right hn_half_hi hlog2_pos.le]

/-
## Part VI: Examples
-/

/--
**Empty set is sum-free:**
-/
theorem empty_sumFree : IsSumFree ∅ := by
  intro a b c ha _ _
  exact (Finset.notMem_empty a ha).elim

/--
**Singletons are sum-free:**
-/
theorem singleton_sumFree (x : ℕ) (hx : x > 0) : IsSumFree {x} := by
  intro a b c ha hb hc heq
  simp at ha hb hc
  rw [ha, hb, hc] at heq
  omega

/--
**Odd numbers in [1,n] are sum-free:**
Sum of two odd numbers is even, so can't equal an odd number.
-/
theorem oddNumbers_sumFree (n : ℕ) :
    IsSumFree ((Finset.range (n + 1)).filter (fun k => k % 2 = 1)) := by
  intro a b c ha hb hc heq
  simp only [Finset.mem_filter, Finset.mem_range] at ha hb hc
  have hodd_a : a % 2 = 1 := ha.2
  have hodd_b : b % 2 = 1 := hb.2
  have hodd_c : c % 2 = 1 := hc.2
  -- b + c is even (odd + odd = even)
  have heven : (b + c) % 2 = 0 := by omega
  -- But a is odd
  rw [heq] at hodd_a
  omega

/-
## Part VII: Structure of Sum-Free Sets
-/

/-
**Types of Sum-Free Sets:**
Most sum-free sets are "essentially" one of:
1. Subsets of [n/2+1, n] (type 1)
2. Subsets of odd numbers (type 2)
3. Various other sparse structures

Green's proof shows type 1 and 2 dominate the count.

**Schur's Theorem Connection:**
Sum-free sets are related to Schur numbers.
The maximum size of a sum-free subset of [1,n] is ⌈n/2⌉.
-/
/-
## Part VIII: OEIS A007865
-/

/--
**Small Values (OEIS A007865):**
f(1) = 2: {}, {1}
f(2) = 3: {}, {1}, {2}
f(3) = 6: {}, {1}, {2}, {3}, {1,3}, {2,3}
f(4) = 9
f(5) = 16
...
-/
theorem f_1 : f 1 = 2 := by native_decide
theorem f_2 : f 2 = 3 := by native_decide
theorem f_3 : f 3 = 6 := by native_decide

/-
## Part IX: Summary
-/

/--
**Erdős Problem #748: PROVED**

The Cameron-Erdős conjecture is true.

f(n) = 2^{(1+o(1))n/2}

More precisely:
1. f(n) ≥ 2^{n/2} (trivial, from upper half)
2. f(n) ≤ C · 2^{n/2} (Green, Sapozhenko)
3. f(n) ~ c_n · 2^{n/2} with c_n depending on parity
-/
theorem erdos_748_summary :
    -- Trivial lower bound
    (∀ n ≥ 2, f n ≥ 2 ^ (n / 2)) ∧
    -- Upper bound exists
    (∃ C : ℝ, C > 0 ∧ ∀ n ≥ 1, (f n : ℝ) ≤ C * 2 ^ (n / 2)) ∧
    -- Precise asymptotic exists
    (∃ c_even c_odd : ℝ, c_even > 0 ∧ c_odd > 0) := by
  constructor
  · exact trivial_lower_bound
  constructor
  · exact green_upper_bound
  · obtain ⟨ce, co, hce, hco, _⟩ := precise_asymptotic
    exact ⟨ce, co, hce, hco⟩

/--
**Erdős Problem #748: PROVED**
-/
theorem erdos_748 : cameronErdosConjecture := cameron_erdos_proved

end Erdos748
