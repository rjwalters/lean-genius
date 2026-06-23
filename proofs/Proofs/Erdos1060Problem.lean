/-
Erdős Problem #1060: Counting Solutions to k·σ(k) = n

Source: https://erdosproblems.com/1060
Status: OPEN (Problem B11 in Guy's collection)

Statement:
Let f(n) count the number of solutions to k·σ(k) = n, where σ(k) is the
sum of divisors of k.

Questions:
1. Is f(n) ≤ n^{o(1/log log n)}?
2. Perhaps even f(n) ≤ (log n)^{O(1)}?

Note: σ(k) is the sum of all divisors of k. For example:
- σ(1) = 1, so 1·σ(1) = 1
- σ(6) = 1+2+3+6 = 12, so 6·σ(6) = 72
- σ(p) = p+1 for prime p, so p·σ(p) = p(p+1)

Tags: Number theory, Divisor functions, Counting solutions
-/

import Mathlib

open Nat Finset

namespace Erdos1060

/-
## Part I: The Sum of Divisors Function
-/

/--
Sum of divisors function σ(k) = sum of all divisors of k.
-/
abbrev sigma (k : ℕ) : ℕ := (Nat.divisors k).sum id

/--
σ(1) = 1
-/
theorem sigma_one : sigma 1 = 1 := by native_decide

/--
For prime p, σ(p) = p + 1
-/
theorem sigma_prime (p : ℕ) (hp : p.Prime) : sigma p = p + 1 := by
  unfold sigma
  rw [Nat.Prime.divisors hp]
  have h1p : (1 : ℕ) ∉ ({p} : Finset ℕ) := by
    rw [Finset.mem_singleton]; exact hp.one_lt.ne
  rw [Finset.sum_insert h1p, Finset.sum_singleton]
  simp only [id]; omega

/--
σ is multiplicative on coprime arguments.
-/
theorem sigma_mul_coprime (m n : ℕ) (hmn : m.Coprime n) (_hm : m ≠ 0) (_hn : n ≠ 0) :
    sigma (m * n) = sigma m * sigma n := by
  -- Bridge to Mathlib's ArithmeticFunction.sigma 1, which is proved multiplicative
  have bridge : ∀ k : ℕ, sigma k = (ArithmeticFunction.sigma 1) k := by
    intro k; simp only [sigma, ArithmeticFunction.sigma_apply, pow_one, id]
  rw [bridge, bridge, bridge]
  exact ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime hmn

/-
## Part II: The Product k·σ(k)
-/

/--
The product function g(k) = k · σ(k).
-/
def g (k : ℕ) : ℕ := k * sigma k

/--
g(1) = 1
-/
theorem g_one : g 1 = 1 := by
  simp [g, sigma_one]

/--
For prime p, g(p) = p(p+1).
-/
theorem g_prime (p : ℕ) (hp : p.Prime) : g p = p * (p + 1) := by
  simp [g, sigma_prime p hp]

/-
## Part III: The Counting Function f(n)
-/

/--
The set of k such that k·σ(k) = n.
-/
def solutionSet (n : ℕ) : Set ℕ := {k : ℕ | g k = n}

/--
f(n) = number of solutions to k·σ(k) = n.

Note: We need to show this is finite for n > 0 to define f(n) properly.
-/
noncomputable def f (n : ℕ) : ℕ := (solutionSet n).ncard

/-- σ(k) ≥ 1 for k > 0, since k ∈ divisors(k). -/
theorem sigma_pos (k : ℕ) (hk : 0 < k) : 1 ≤ sigma k := by
  unfold sigma
  have : k ∈ k.divisors := Nat.mem_divisors.mpr ⟨dvd_refl k, hk.ne'⟩
  calc 1 ≤ id k := hk
    _ ≤ k.divisors.sum id := Finset.single_le_sum (fun _ _ => Nat.zero_le _) this

/-- σ(k) ≥ k for k > 0, since k divides k and contributes k to the sum. -/
theorem sigma_ge_self (k : ℕ) (hk : 0 < k) : k ≤ sigma k := by
  unfold sigma
  have : k ∈ k.divisors := Nat.mem_divisors.mpr ⟨dvd_refl k, hk.ne'⟩
  calc k = id k := rfl
    _ ≤ k.divisors.sum id := Finset.single_le_sum (fun _ _ => Nat.zero_le _) this

/-- k ≤ g(k) for k > 0, since g(k) = k · σ(k) ≥ k · 1 = k. -/
theorem k_le_g (k : ℕ) (hk : 0 < k) : k ≤ g k := by
  unfold g
  calc k = k * 1 := (mul_one k).symm
    _ ≤ k * sigma k := Nat.mul_le_mul_left k (sigma_pos k hk)

/-- g(k) ≥ k² for k > 0, since g(k) = k · σ(k) ≥ k · k. -/
theorem g_ge_sq (k : ℕ) (hk : 0 < k) : k * k ≤ g k := by
  unfold g
  exact Nat.mul_le_mul_left k (sigma_ge_self k hk)

/--
The solution set is finite for any n > 0.
Proof: k·σ(k) ≥ k·1 = k (since 1 | k for k > 0), so k ≤ n.
-/
theorem solutionSet_finite (n : ℕ) (hn : n > 0) : (solutionSet n).Finite := by
  refine Set.Finite.subset (Set.finite_Icc 1 n) ?_
  intro k hk
  simp only [solutionSet, Set.mem_setOf_eq] at hk
  simp only [Set.mem_Icc]
  constructor
  · -- k ≥ 1: if k = 0, then g(k) = 0 ≠ n (since n > 0)
    by_contra h
    push_neg at h
    interval_cases k
    simp [g, sigma] at hk
    omega
  · -- k ≤ n: since k·σ(k) ≥ k (as σ(k) ≥ 1 for k > 0)
    have hk_pos : 0 < k := by
      by_contra h; push_neg at h; interval_cases k; simp [g, sigma] at hk; omega
    calc k ≤ g k := k_le_g k hk_pos
      _ = n := hk

/--
Alternative definition using Finset for finite n.
-/
noncomputable def f' (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k => g k = n)).card

/--
f and f' agree for n > 0.
-/
theorem f_eq_f' (n : ℕ) (hn : n > 0) : f n = f' n := by
  unfold f f'
  -- Key: solutionSet n = ↑((Icc 1 n).filter (fun k => g k = n)) as sets
  have h_eq : solutionSet n = ↑((Finset.Icc 1 n).filter (fun k => g k = n)) := by
    ext k
    simp only [solutionSet, Set.mem_setOf_eq, Finset.coe_filter, Set.mem_setOf_eq,
               Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · intro hk
      refine ⟨⟨?_, ?_⟩, hk⟩
      · -- k ≥ 1: if k = 0 then g 0 = 0 ≠ n since n > 0
        by_contra hle; push_neg at hle; interval_cases k; simp [g] at hk; omega
      · -- k ≤ n: since k ≤ g(k) = n
        have hk_pos : 0 < k := by
          by_contra hle; push_neg at hle; interval_cases k; simp [g] at hk; omega
        linarith [k_le_g k hk_pos]
    · exact fun ⟨_, hk⟩ => hk
  rw [h_eq, Set.ncard_coe_finset]

/-
## Part IV: Basic Values
-/

/--
f(1) = 1: The only solution to k·σ(k) = 1 is k = 1.
-/
theorem f_of_one : f 1 = 1 := by
  unfold f
  have h_eq : solutionSet 1 = {1} := by
    ext k
    simp only [solutionSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hk
      unfold g at hk
      have : k ≤ 1 := by
        calc k ≤ k * sigma k := le_mul_of_one_le_right (Nat.zero_le _)
                (by rcases k with _ | k
                    · simp [sigma] at hk
                    · exact sigma_pos (k + 1) (by omega))
          _ = 1 := hk
      interval_cases k
      · simp [g, sigma] at hk
      · rfl
    · intro hk; subst hk; native_decide
  rw [h_eq, Set.ncard_singleton]

/--
f(0) = 1: The only solution to k·σ(k) = 0 is k = 0 (g(0) = 0·σ(0) = 0).
For k > 0, σ(k) ≥ 1, so g(k) = k·σ(k) ≥ k > 0.
-/
theorem f_of_zero : f 0 = 1 := by
  unfold f
  have h_eq : solutionSet 0 = {0} := by
    ext k
    simp only [solutionSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hk
      by_contra hne
      have hk_pos : 0 < k := Nat.pos_of_ne_zero hne
      have : 0 < g k := lt_of_lt_of_le hk_pos (k_le_g k hk_pos)
      omega
    · intro hk; subst hk; simp [g, sigma]
  rw [h_eq, Set.ncard_singleton]

/-
## Part V: Trivial Upper Bound
-/

/--
**Trivial Upper Bound:** f(n) ≤ n for n > 0.

Since every solution k to g(k) = n satisfies 1 ≤ k ≤ n, there are at most n solutions.
The open conjectures (Part VI) ask for dramatically better bounds.
-/
theorem f_le_n (n : ℕ) (hn : n > 0) : f n ≤ n := by
  rw [f_eq_f' n hn]
  unfold f'
  calc ((Finset.Icc 1 n).filter (fun k => g k = n)).card
      ≤ (Finset.Icc 1 n).card := Finset.card_filter_le _ _
    _ = n := by rw [Nat.card_Icc]; omega

/--
g is positive for positive inputs: g(k) > 0 when k > 0.
-/
theorem g_pos (k : ℕ) (hk : 0 < k) : 0 < g k := by
  unfold g
  exact Nat.mul_pos hk (sigma_pos k hk)

/--
g is strictly greater than k for k ≥ 2, since σ(k) ≥ k + 1 (both 1 and k divide k).
-/
theorem g_gt_k (k : ℕ) (hk : k ≥ 2) : g k > k := by
  unfold g
  -- σ(k) ≥ k + 1 since {1, k} ⊆ divisors(k) and 1 ≠ k
  have h1 : 1 ∈ k.divisors := Nat.mem_divisors.mpr ⟨one_dvd k, by omega⟩
  have hk_div : k ∈ k.divisors := Nat.mem_divisors.mpr ⟨dvd_refl k, by omega⟩
  have hne : (1 : ℕ) ≠ k := by omega
  have h_sub : {1, k} ⊆ k.divisors := by
    intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
  have h_sum : sigma k ≥ k + 1 := by
    unfold sigma
    calc k.divisors.sum id
        ≥ ({1, k} : Finset ℕ).sum id :=
          Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => Nat.zero_le _)
      _ = 1 + k := by rw [Finset.sum_pair hne]; simp [id]
      _ = k + 1 := by ring
  calc k * sigma k ≥ k * (k + 1) := Nat.mul_le_mul_left k h_sum
    _ = k * k + k := by ring
    _ > k := by nlinarith

/-
## Part VI: Upper Bound Conjectures (OPEN)
-/

/--
**Weak Conjecture:**
f(n) ≤ n^{o(1/log log n)} as n → ∞.

This means: For any ε > 0, there exists N such that for all n > N,
f(n) ≤ n^{ε/log log n}.
-/
/--
**Strong Conjecture:**
f(n) ≤ (log n)^C for some constant C.

This is a much stronger bound - polynomial in log n rather than
a slow power of n.
-/
/-
## Part VII: OEIS Connection
-/

/--
OEIS A327153 contains values related to this problem.
The sequence of n for which f(n) > 0 (i.e., k·σ(k) = n has a solution).
-/
def oeis_A327153 : Set ℕ := {n : ℕ | f n > 0}

/--
Membership in A327153 for positive n.

Note: For n = 0, f(0) = 1 > 0 (via k = 0), but no k > 0 satisfies g(k) = 0,
so the k > 0 condition requires n > 0.
-/
theorem mem_A327153_iff (n : ℕ) (hn : n > 0) :
    n ∈ oeis_A327153 ↔ ∃ k > 0, g k = n := by
  -- Use show to keep f n visible for rewriting
  show f n > 0 ↔ ∃ k > 0, g k = n
  rw [f_eq_f' n hn]
  simp only [f', Finset.card_pos, Finset.Nonempty]
  constructor
  · rintro ⟨k, hk⟩
    rw [Finset.mem_filter, Finset.mem_Icc] at hk
    exact ⟨k, hk.1.1, hk.2⟩
  · rintro ⟨k, hk_pos, hgk⟩
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr
      ⟨hk_pos, hgk ▸ k_le_g k hk_pos⟩, hgk⟩⟩

/-
## Part VIII: Examples and Computations
-/

/--
n = 1: k = 1 is the only solution (1·σ(1) = 1·1 = 1).
-/
example : g 1 = 1 := g_one

/--
n = 6: k = 2 gives 2·σ(2) = 2·3 = 6.
-/
example : g 2 = 6 := by
  simp [g, sigma]
  native_decide

/--
n = 12: k = 3 gives 3·σ(3) = 3·4 = 12.
-/
example : g 3 = 12 := by
  simp [g, sigma]
  native_decide

/--
n = 72: k = 6 gives 6·σ(6) = 6·12 = 72.
-/
example : g 6 = 72 := by
  simp [g, sigma]
  native_decide

/--
For prime p: g(p) = p(p+1).
Examples:
- g(2) = 6, g(3) = 12, g(5) = 30, g(7) = 56
-/
example : g 5 = 30 := by simp [g, sigma]; native_decide
example : g 7 = 56 := by simp [g, sigma]; native_decide

/-
## Part IX: The Square Root Bound
-/

/--
Every solution k to g(k) = n satisfies k ≤ √n.
Since σ(k) ≥ k, we have g(k) = k·σ(k) ≥ k², so k ≤ √n.
This improves the trivial bound k ≤ n from solutionSet_finite.
-/
theorem solution_le_sqrt (n k : ℕ) (hk_pos : 0 < k) (hk : g k = n) :
    k ≤ Nat.sqrt n := by
  rw [Nat.le_sqrt]
  calc k * k ≤ g k := g_ge_sq k hk_pos
    _ = n := hk

/--
f(n) ≤ √n for n > 0.
This is a concrete, proved upper bound on the counting function,
in contrast to the axiomatized conjectures f(n) ≤ n^{o(1/log log n)}
and f(n) ≤ (log n)^{O(1)}.
-/
theorem f_le_sqrt (n : ℕ) (hn : n > 0) : f n ≤ Nat.sqrt n := by
  rw [f_eq_f' n hn]; unfold f'
  calc ((Finset.Icc 1 n).filter (fun k => g k = n)).card
    ≤ (Finset.Icc 1 (Nat.sqrt n)).card := by
        apply Finset.card_le_card
        intro k hk
        rw [Finset.mem_filter, Finset.mem_Icc] at hk
        rw [Finset.mem_Icc]
        exact ⟨hk.1.1, solution_le_sqrt n k hk.1.1 hk.2⟩
    _ ≤ Nat.sqrt n := by
        simp only [Finset.card_Icc]; omega

end Erdos1060
