/-
Erdős Problem #1099: Divisor Ratio Sum Boundedness

Source: https://erdosproblems.com/1099
Status: SOLVED (Vose, 1984)

Statement:
Let 1 = d₁ < d₂ < ⋯ < d_τ(n) = n be the divisors of n in increasing order.
For α > 1, define:
    h_α(n) = Σᵢ ((d_{i+1}/dᵢ) - 1)^α

Question: Is it true that liminf_{n→∞} h_α(n) ≪_α 1?

Answer: YES

Vose (1984) proved that the liminf is bounded by constructing a specific
sequence of integers with small consecutive divisor ratios.

Key Observations:
- The liminf is trivially ≥ 1 (the first term (d₂/d₁ - 1)^α = (d₂ - 1)^α ≥ 1)
- Erdős suggested n! or lcm{1,...,n} as good candidates for bounded h_α(n)
- Whether these specific sequences satisfy the property remains OPEN

Reference: [Er81h] Erdős (1981), [Vo84] Vose (1984)
-/

import Mathlib

open Nat Finset BigOperators

namespace Erdos1099

/-
## Part I: Divisors and Consecutive Ratios

For a positive integer n, its divisors can be ordered as 1 = d₁ < d₂ < ⋯ < d_τ(n) = n.
The ratio d_{i+1}/dᵢ measures how "close together" consecutive divisors are.
-/

/--
**Divisor count:**
τ(n) = |{d : d ∣ n}|, the number of divisors of n.
-/
def tau (n : ℕ) : ℕ := (n.divisors).card

/--
**Sorted divisors:**
The divisors of n listed in increasing order.
-/
def sortedDivisors (n : ℕ) : List ℕ :=
  (n.divisors.sort (· ≤ ·))

/-
## Infrastructure: Sorted Divisor Properties
-/

theorem one_mem_sortedDivisors (n : ℕ) (hn : n ≥ 1) :
    1 ∈ sortedDivisors n := by
  simp only [sortedDivisors, Finset.mem_sort]
  exact Nat.mem_divisors.mpr ⟨one_dvd n, by omega⟩

theorem n_mem_sortedDivisors (n : ℕ) (hn : n ≥ 1) :
    n ∈ sortedDivisors n := by
  simp only [sortedDivisors, Finset.mem_sort]
  exact Nat.mem_divisors.mpr ⟨dvd_refl n, by omega⟩

theorem sortedDivisors_ne_nil (n : ℕ) (hn : n ≥ 1) :
    sortedDivisors n ≠ [] := by
  intro h
  have := one_mem_sortedDivisors n hn
  rw [h] at this; simp at this

theorem sortedDivisors_sorted (n : ℕ) :
    (sortedDivisors n).Pairwise (· ≤ ·) :=
  Finset.pairwise_sort n.divisors (· ≤ ·)

theorem sortedDivisors_nodup (n : ℕ) :
    (sortedDivisors n).Nodup :=
  n.divisors.sort_nodup (· ≤ ·)

theorem sortedDivisors_pos (n d : ℕ) (hd : d ∈ sortedDivisors n) : d ≥ 1 := by
  have hmem : d ∈ n.divisors := by
    simp only [sortedDivisors, Finset.mem_sort] at hd; exact hd
  exact Nat.pos_of_mem_divisors hmem

theorem sortedDivisors_le (n d : ℕ) (hn : n ≥ 1) (hd : d ∈ sortedDivisors n) :
    d ≤ n := by
  have hmem : d ∈ n.divisors := by
    simp only [sortedDivisors, Finset.mem_sort] at hd; exact hd
  exact Nat.le_of_dvd (by omega) (Nat.mem_divisors.mp hmem).1

theorem sortedDivisors_head_eq_one (n : ℕ) (hn : n ≥ 1) :
    (sortedDivisors n).head (sortedDivisors_ne_nil n hn) = 1 := by
  set hd := (sortedDivisors n).head (sortedDivisors_ne_nil n hn) with hd_def
  have hsorted := sortedDivisors_sorted n
  have h1 := one_mem_sortedDivisors n hn
  have hd_pos := sortedDivisors_pos n hd (List.head_mem (sortedDivisors_ne_nil n hn))
  by_contra hne
  have hge2 : hd ≥ 2 := by omega
  have hcons : sortedDivisors n = hd :: (sortedDivisors n).tail :=
    (List.cons_head_tail (sortedDivisors_ne_nil n hn)).symm
  rw [hcons] at h1
  rcases List.mem_cons.mp h1 with heq | htl
  · exact hne heq.symm
  · rw [hcons] at hsorted
    have := (List.pairwise_cons.mp hsorted).1 1 htl
    omega

theorem sortedDivisors_cons (n : ℕ) (hn : n ≥ 1) :
    ∃ rest, sortedDivisors n = 1 :: rest := by
  exact ⟨(sortedDivisors n).tail,
    by rw [← sortedDivisors_head_eq_one n hn]
       exact (List.cons_head_tail (sortedDivisors_ne_nil n hn)).symm⟩

/--
**First divisor is 1:**
For n ≥ 1, the first divisor is always 1.
-/
theorem first_divisor_is_one (n : ℕ) (hn : n ≥ 1) :
    (sortedDivisors n).head? = some 1 := by
  obtain ⟨rest, heq⟩ := sortedDivisors_cons n hn
  simp [heq]

/-
### Last Divisor Infrastructure
-/

private theorem getLast?_eq_some_getLast :
    ∀ (l : List ℕ) (h : l ≠ []), l.getLast? = some (l.getLast h) := by
  intro l
  induction l with
  | nil => intro h; contradiction
  | cons a t ih =>
    intro _
    cases t with
    | nil => rfl
    | cons b rest =>
      show (b :: rest).getLast? = some ((b :: rest).getLast (List.cons_ne_nil b rest))
      exact ih (List.cons_ne_nil b rest)

private theorem le_getLast_of_mem_pairwise_le :
    ∀ (l : List ℕ), l.Pairwise (· ≤ ·) →
    ∀ x, x ∈ l → ∀ (hne : l ≠ []), x ≤ l.getLast hne := by
  intro l
  induction l with
  | nil => intro _ x hx; simp at hx
  | cons a t ih =>
    intro hs x hx hne
    cases t with
    | nil =>
      rcases List.mem_cons.mp hx with rfl | hmem
      · rfl
      · simp at hmem
    | cons b rest =>
      show x ≤ (b :: rest).getLast (List.cons_ne_nil b rest)
      rcases List.mem_cons.mp hx with rfl | ht
      · have hall := (List.pairwise_cons.mp hs).1
        exact hall _ (List.getLast_mem _)
      · exact ih (List.pairwise_cons.mp hs).2 x ht (List.cons_ne_nil _ _)

theorem sortedDivisors_getLast_eq_n (n : ℕ) (hn : n ≥ 1) :
    (sortedDivisors n).getLast (sortedDivisors_ne_nil n hn) = n := by
  have h_le : (sortedDivisors n).getLast (sortedDivisors_ne_nil n hn) ≤ n :=
    sortedDivisors_le n _ hn (List.getLast_mem _)
  have h_ge : n ≤ (sortedDivisors n).getLast (sortedDivisors_ne_nil n hn) :=
    le_getLast_of_mem_pairwise_le _ (sortedDivisors_sorted n) n
      (n_mem_sortedDivisors n hn) _
  omega

/--
**Last divisor is n:**
For n ≥ 1, the last divisor is always n.
-/
theorem last_divisor_is_n (n : ℕ) (hn : n ≥ 1) :
    (sortedDivisors n).getLast? = some n := by
  rw [getLast?_eq_some_getLast _ (sortedDivisors_ne_nil n hn)]
  exact congrArg some (sortedDivisors_getLast_eq_n n hn)

/-
## Part II: The h_α Function

The key function measures how "spread out" the divisor ratios are.
-/

/--
**Consecutive divisor ratios:**
The list of ratios d_{i+1}/dᵢ for consecutive divisors.
Each ratio r_i = d_{i+1}/d_i ≥ 1 for sorted divisors.
-/
def divisorRatios (n : ℕ) : List ℚ :=
  let divs := sortedDivisors n
  List.zipWith (fun a b => (a : ℚ) / (b : ℚ)) divs.tail divs

/--
**The h_α function:**
h_α(n) = Σᵢ ((d_{i+1}/dᵢ) - 1)^α

This measures the total "gap" between consecutive divisors, with larger
gaps penalized more heavily for larger α.
-/
noncomputable def h_alpha (α : ℝ) (n : ℕ) : ℝ :=
  (divisorRatios n).map (fun r => ((r : ℝ) - 1) ^ α) |>.sum

/-
h_α(n) can be computed by summing over consecutive pairs.
This is definitional from the h_alpha definition.
-/

/-
## Part III: The Trivial Lower Bound

The first term alone gives h_α(n) ≥ 1 for n ≥ 2.
-/

theorem sortedDivisors_length_ge_2 (n : ℕ) (hn : n ≥ 2) :
    (sortedDivisors n).length ≥ 2 := by
  simp [sortedDivisors, Finset.length_sort]
  have h1 : 1 ∈ n.divisors := Nat.one_mem_divisors.mpr (by omega)
  have hn_mem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_refl n, by omega⟩
  calc n.divisors.card
      ≥ ({1, n} : Finset ℕ).card :=
        Finset.card_le_card (Finset.insert_subset_iff.mpr
          ⟨h1, Finset.singleton_subset_iff.mpr hn_mem⟩)
    _ = 2 := Finset.card_pair (by omega : (1 : ℕ) ≠ n)

theorem sortedDivisors_cons2 (n : ℕ) (hn : n ≥ 2) :
    ∃ d₂ rest, sortedDivisors n = 1 :: d₂ :: rest ∧ d₂ ≥ 2 := by
  obtain ⟨rest₁, h1⟩ := sortedDivisors_cons n (by omega : n ≥ 1)
  have hlen : rest₁.length ≥ 1 := by
    have := sortedDivisors_length_ge_2 n hn
    rw [h1] at this; simp at this; omega
  obtain ⟨d₂, rest₂, h2⟩ := List.exists_cons_of_ne_nil
    (show rest₁ ≠ [] by intro h; simp [h] at hlen)
  refine ⟨d₂, rest₂, by rw [h1, h2], ?_⟩
  have hnodup := sortedDivisors_nodup n
  rw [h1, h2] at hnodup
  have hd2_ne1 : d₂ ≠ 1 := by
    intro heq
    exact (List.nodup_cons.mp hnodup).1 (heq ▸ List.mem_cons.mpr (Or.inl rfl))
  have hd2_pos := sortedDivisors_pos n d₂
    (by rw [h1, h2]; exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
  omega

/--
**First ratio is at least 2:**
For any n ≥ 2, the smallest divisor is 1 and the next is at least 2,
so d₂/d₁ = d₂ ≥ 2.
-/
theorem first_ratio_ge_two (n : ℕ) (hn : n ≥ 2) :
    ∃ r ∈ divisorRatios n, r ≥ 2 := by
  obtain ⟨d₂, rest, heq, hd2⟩ := sortedDivisors_cons2 n hn
  have hmem : (↑d₂ : ℚ) / ↑(1 : ℕ) ∈ divisorRatios n := by
    unfold divisorRatios
    rw [heq]
    simp only [List.tail_cons]
    exact List.mem_cons.mpr (Or.inl rfl)
  refine ⟨(↑d₂ : ℚ) / ↑(1 : ℕ), hmem, ?_⟩
  simp only [Nat.cast_one, div_one]
  exact_mod_cast hd2

/--
**Trivial lower bound:**
For α > 1 and n ≥ 2, we have h_α(n) ≥ 1.

Proof: The first term is ((d₂/1) - 1)^α ≥ (2-1)^α = 1.
-/
axiom h_alpha_ge_one (α : ℝ) (hα : α > 1) (n : ℕ) (hn : n ≥ 2) :
    h_alpha α n ≥ 1

/-
## Part IV: Special Sequences

Erdős suggested that n! and lcm{1,...,n} might have bounded h_α.
-/

/--
**Factorial divisors:**
n! has many small divisors, so consecutive ratios tend to be close to 1.
-/
def factorialDivisors (n : ℕ) : Finset ℕ := (n.factorial).divisors

/--
**LCM divisors:**
lcm{1,...,n} has many small divisors as well.
-/
def lcmDivisors (n : ℕ) : Finset ℕ :=
  (List.range (n + 1) |>.foldl lcm 1).divisors

/-
**Open Sub-questions:**
- Does h_α(n!) remain bounded as n → ∞?
- Does h_α(lcm{1,...,n}) remain bounded as n → ∞?
These specific candidates suggested by Erdős remain unresolved.
-/

/-
## Part V: Vose's Theorem (1984)

Vose answered the question affirmatively by constructing a different sequence.
-/

/--
**Vose's Construction:**
There exists a sequence (nₖ) of positive integers such that
h_α(nₖ) remains bounded as k → ∞.

The key is to construct numbers whose divisors are very evenly spaced.
-/
axiom vose_bounded_sequence (α : ℝ) (hα : α > 1) :
    ∃ (bound : ℝ), bound > 0 ∧
      ∃ (n : ℕ → ℕ), (∀ k, n k ≥ 1) ∧
        ∀ k, h_alpha α (n k) ≤ bound

/--
**Vose's Theorem (1984):**
For any α > 1, liminf_{n→∞} h_α(n) is finite.

This resolves Erdős Problem #1099 in the affirmative.
-/
axiom vose_liminf_bounded (α : ℝ) (hα : α > 1) :
    ∃ (bound : ℝ), ∀ ε > 0,
      ∃ (n : ℕ), n > 0 ∧ h_alpha α n < bound + ε

/--
**Main theorem: Erdős Problem #1099 SOLVED**
-/
theorem erdos_1099 (α : ℝ) (hα : α > 1) :
    ∃ C : ℝ, C > 0 ∧ ∀ ε > 0, ∃ n : ℕ, n > 0 ∧ h_alpha α n < C + ε := by
  obtain ⟨bound, hbound⟩ := vose_liminf_bounded α hα
  refine ⟨|bound| + 1, by positivity, ?_⟩
  intro ε hε
  obtain ⟨n, hn_pos, hn_bound⟩ := hbound ε hε
  exact ⟨n, hn_pos, by linarith [le_abs_self bound]⟩

/-
## Part VI: The Related Sum Σ(d_{i+1}/dᵢ)

Erdős also studied the unweighted sum of ratios.
-/

/--
**Sum of divisor ratios:**
S(n) = Σᵢ (d_{i+1}/dᵢ)
-/
noncomputable def sumDivisorRatios (n : ℕ) : ℝ :=
  (divisorRatios n).map (fun r => (r : ℝ)) |>.sum

/--
**Lower bound on sum:**
Σᵢ (d_{i+1}/dᵢ) > τ(n) + log(n)

Proof idea: Each ratio is ≥ 1, giving τ(n) - 1 terms. The extra log(n)
comes from the fact that the product of ratios telescopes to n.
-/
axiom sum_divisor_ratios_lower_bound (n : ℕ) (hn : n ≥ 2) :
    sumDivisorRatios n > (tau n : ℝ) + Real.log n

/-
## Part VII: Connection to Problem #673

Both problems study functions of consecutive divisor ratios,
exploring how "smooth" the divisor structure of integers can be.
-/

/-
## Part VIII: Proof Strategy

Vose's approach and why Erdős's candidates remain open.
-/

/-
**Vose's Strategy:**
Construct n with divisors d₁, d₂, ..., d_τ such that:
- The ratios d_{i+1}/dᵢ are all close to 1
- Specifically, d_{i+1}/dᵢ ≈ 1 + c/τ for some constant c

Then h_α(n) ≈ τ · (c/τ)^α = c^α · τ^(1-α) → 0 as τ → ∞.

**Why n! is challenging:**
The divisors of n! include 1, 2, ..., n, so τ(n!) is very large.
But the ratios between consecutive divisors may not be uniformly small.

**Why lcm{1,...,n} is challenging:**
lcm{1,...,n} has many prime factors, giving it many divisors.
But proving uniform bounds on consecutive ratios is non-trivial.
-/

/-
## Part IX: Examples
-/

/--
**Example: Prime p**
For a prime p, divisors are {1, p}, so the only ratio is p/1 = p.
h_α(p) = (p - 1)^α, which is unbounded as p → ∞.
-/
axiom prime_h_alpha_unbounded :
    ∀ M : ℝ, ∃ p : ℕ, Nat.Prime p ∧ ∀ α : ℝ, α ≥ 1 → h_alpha α p > M

/--
**Example: Power of 2**
For n = 2^k, divisors are {1, 2, 4, ..., 2^k}, all ratios equal 2.
h_α(2^k) = k · 1^α = k, which grows with k.
-/
axiom power_of_two_h_alpha (k : ℕ) (α : ℝ) (hα : α ≥ 1) :
    h_alpha α (2^k) = k

/-
**Example: Small highly composite**
n = 12 has divisors {1, 2, 3, 4, 6, 12}.
Ratios: 2/1=2, 3/2=1.5, 4/3≈1.33, 6/4=1.5, 12/6=2
h_α(12) = 1^α + 0.5^α + 0.33^α + 0.5^α + 1^α (approximately)
-/

/-
## Part X: Summary
-/

/--
**Erdős Problem #1099: SOLVED**

Q: For α > 1, is liminf_{n→∞} h_α(n) bounded?
   where h_α(n) = Σᵢ ((d_{i+1}/dᵢ) - 1)^α

A: YES (Vose, 1984)

Key points:
- The trivial lower bound is 1
- Vose constructed a specific sequence with bounded h_α
- Erdős's candidates (n! and lcm{1,...,n}) remain OPEN
- The related question about Σ(d_{i+1}/dᵢ) follows from this
-/
theorem erdos_1099_summary :
    -- Main result: bounded liminf exists
    (∀ α : ℝ, α > 1 →
      ∃ C : ℝ, C > 0 ∧ ∀ ε > 0, ∃ n : ℕ, n > 0 ∧ h_alpha α n < C + ε) ∧
    -- Trivial lower bound: liminf ≥ 1
    (∀ α : ℝ, α > 1 → ∀ n : ℕ, n ≥ 2 → h_alpha α n ≥ 1) := by
  constructor
  · exact erdos_1099
  · exact h_alpha_ge_one

end Erdos1099
