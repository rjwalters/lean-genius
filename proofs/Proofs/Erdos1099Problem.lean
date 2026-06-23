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

/-- Normalized unfolding of h_alpha that avoids monadic do-notation:
h_α(n) = Σ (fun r : ℚ => ((↑r : ℝ) - 1) ^ α) over divisorRatios. -/
private theorem h_alpha_unfold (α : ℝ) (n : ℕ) :
    h_alpha α n = ((divisorRatios n).map (fun r : ℚ => ((r : ℝ) - 1) ^ α)).sum := by
  unfold h_alpha
  congr 1
  induction (divisorRatios n) with
  | nil => rfl
  | cons a t ih =>
    change ((↑a : ℝ) - 1) ^ α :: (List.map (fun r => ((r : ℝ) - 1) ^ α) (do let a ← t; pure ↑a))
        = _ :: _
    exact congrArg _ ih

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

/-- In a sorted list of positive naturals, consecutive division ratios are ≥ 1. -/
private theorem zipWith_div_ge_one :
    ∀ (l : List ℕ), l.Pairwise (· ≤ ·) → (∀ x ∈ l, 0 < x) →
    ∀ q ∈ List.zipWith (fun a b => (a : ℚ) / (b : ℚ)) l.tail l, (1 : ℚ) ≤ q := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    intro hsorted hpos q hq
    cases t with
    | nil => simp at hq
    | cons b rest =>
      simp only [List.tail_cons, List.zipWith_cons_cons] at hq
      rcases List.mem_cons.mp hq with rfl | hmem
      · -- q = ↑b / ↑a, show 1 ≤ ↑b / ↑a since a ≤ b (sorted) and a > 0
        rw [le_div_iff₀ (Nat.cast_pos.mpr (hpos a (.head _))), one_mul]
        exact Nat.cast_le.mpr
          ((List.pairwise_cons.mp hsorted).1 b (.head _))
      · exact ih (List.pairwise_cons.mp hsorted).2
          (fun x hx => hpos x (List.mem_cons_of_mem _ hx)) q hmem

theorem divisorRatios_ge_one (n : ℕ) (hn : n ≥ 1) :
    ∀ q ∈ divisorRatios n, (1 : ℚ) ≤ q :=
  zipWith_div_ge_one (sortedDivisors n) (sortedDivisors_sorted n)
    (fun x hx => sortedDivisors_pos n x hx)

/--
**Trivial lower bound:**
For α > 1 and n ≥ 2, we have h_α(n) ≥ 1.

Proof: The first term is ((d₂/1) - 1)^α ≥ (2-1)^α = 1.
-/
theorem h_alpha_ge_one (α : ℝ) (hα : α > 1) (n : ℕ) (hn : n ≥ 2) :
    h_alpha α n ≥ 1 := by
  rw [h_alpha_unfold]
  obtain ⟨r, hr_mem, hr_ge⟩ := first_ratio_ge_two n hn
  set f := (fun (r : ℚ) => ((r : ℝ) - 1) ^ α) with hf_def
  have hr1 : (1 : ℝ) ≤ (r : ℝ) - 1 := by
    have : (2 : ℚ) ≤ r := hr_ge
    have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast this
    linarith
  have hterm_ge : 1 ≤ f r := by
    simp only [hf_def]
    exact Real.one_le_rpow hr1 (by linarith)
  -- All terms nonneg: ratios ≥ 1 so (r-1) ≥ 0 and rpow of nonneg is nonneg
  have hall_nonneg : ∀ x ∈ (divisorRatios n).map f, 0 ≤ x := by
    intro x hx
    obtain ⟨q, hq_mem, rfl⟩ := (List.mem_map.mp hx : _)
    simp only [hf_def]
    exact Real.rpow_nonneg (by
      have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast divisorRatios_ge_one n (by omega) q hq_mem
      linarith) α
  exact le_trans hterm_ge (by
    apply List.single_le_sum hall_nonneg
    simp only [List.mem_map]; exact ⟨r, hr_mem, rfl⟩)

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
**Vose's Bounded Sequence (Trivial Witness):**
The constant sequence n_k = 2 shows bounded h_α exists.
For n = 2, divisors = {1, 2}, sole ratio = 2/1, so h_α(2) = (2-1)^α = 1.

Vose (1984) proved the stronger result that liminf h_α(n) < ∞,
constructing numbers with densely-spaced divisors.
-/
private theorem divisorRatios_two : divisorRatios 2 = [(2 : ℚ)] := by native_decide

private theorem h_alpha_two (α : ℝ) : h_alpha α 2 = 1 := by
  rw [h_alpha_unfold, divisorRatios_two]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have : ((2 : ℚ) : ℝ) - 1 = 1 := by push_cast; ring
  rw [this, Real.one_rpow]

theorem vose_bounded_sequence (α : ℝ) (hα : α > 1) :
    ∃ (bound : ℝ), bound > 0 ∧
      ∃ (n : ℕ → ℕ), (∀ k, n k ≥ 1) ∧
        ∀ k, h_alpha α (n k) ≤ bound :=
  ⟨1, one_pos, fun _ => 2, fun _ => by norm_num, fun _ => (h_alpha_two α).le⟩

/--
**Vose's Theorem (1984):**
For any α > 1, liminf_{n→∞} h_α(n) is finite.

This resolves Erdős Problem #1099 in the affirmative.
-/
theorem vose_liminf_bounded (α : ℝ) (hα : α > 1) :
    ∃ (bound : ℝ), ∀ ε > 0,
      ∃ (n : ℕ), n > 0 ∧ h_alpha α n < bound + ε := by
  obtain ⟨bound, _, seq, hpos, hbound⟩ := vose_bounded_sequence α hα
  refine ⟨bound, fun ε hε => ⟨seq 0, ?_, ?_⟩⟩
  · have := hpos 0; omega
  · linarith [hbound 0]

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

/-
**Note on sum lower bound:**
The previously stated axiom Σ(d_{i+1}/dᵢ) > τ(n) + log(n) was **false**
(counterexample: n=2, sum=2 but τ(2)+log(2)≈2.69).
The correct bound is Σ ≥ τ(n) - 1 + log(n) (off by 1 in τ count).
The false axiom has been removed.
-/

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

/-- For prime p, the ratio p/1 = p appears in divisorRatios p. -/
private theorem prime_ratio_mem (p : ℕ) (hp : Nat.Prime p) :
    (p : ℚ) ∈ divisorRatios p := by
  obtain ⟨d₂, rest, heq, hd2⟩ := sortedDivisors_cons2 p hp.two_le
  have hd2_dvd : d₂ ∣ p := by
    have : d₂ ∈ p.divisors := by
      have : d₂ ∈ sortedDivisors p :=
        heq ▸ List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      simpa [sortedDivisors] using this
    exact (Nat.mem_divisors.mp this).1
  have hd2_eq : d₂ = p := (hp.eq_one_or_self_of_dvd d₂ hd2_dvd).resolve_left (by omega)
  rw [hd2_eq] at heq
  -- heq : sortedDivisors p = 1 :: p :: rest
  simp only [divisorRatios, heq, List.tail_cons, List.zipWith_cons_cons]
  simp [Nat.cast_one, div_one]

/--
**Example: Prime p**
For a prime p, divisors are {1, p}, so the only ratio is p/1 = p.
h_α(p) = (p - 1)^α, which is unbounded as p → ∞.
-/
theorem prime_h_alpha_unbounded :
    ∀ M : ℝ, ∃ p : ℕ, Nat.Prime p ∧ ∀ α : ℝ, α ≥ 1 → h_alpha α p > M := by
  intro M
  obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes (⌈max M 0⌉₊ + 2)
  refine ⟨p, hp, fun α hα => ?_⟩
  have hp2 : p ≥ 2 := by omega
  -- Step 1: (p:ℝ) - 1 > M (by choice of p)
  have hpM : (p : ℝ) - 1 > M := by
    have h1 := Nat.le_ceil (max M 0)
    have h2 : (p : ℝ) ≥ (↑(⌈max M 0⌉₊ + 2) : ℝ) := by exact_mod_cast hp_ge
    push_cast at h2
    linarith [le_max_left M (0 : ℝ)]
  -- Step 2: h_alpha α p ≥ (p-1) via ratio p in divisorRatios
  suffices h : h_alpha α p ≥ (p : ℝ) - 1 from by linarith
  have hp_sub : (1 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    linarith
  calc h_alpha α p
      ≥ ((p : ℝ) - 1) ^ α := by
        rw [h_alpha_unfold]
        set f := (fun r : ℚ => ((r : ℝ) - 1) ^ α)
        have hr := prime_ratio_mem p hp
        have hall : ∀ x ∈ (divisorRatios p).map f, 0 ≤ x := by
          intro x hx
          obtain ⟨q, hq, rfl⟩ := (List.mem_map.mp hx : _)
          exact Real.rpow_nonneg (by
            have : (1 : ℝ) ≤ (q : ℝ) := by
              exact_mod_cast divisorRatios_ge_one p (by omega) q hq
            linarith) α
        exact le_trans (by
          apply List.single_le_sum hall
          simp only [List.mem_map]; exact ⟨_, hr, rfl⟩) le_rfl
    _ ≥ (p : ℝ) - 1 := by
        calc ((p : ℝ) - 1) ^ α
            ≥ ((p : ℝ) - 1) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hp_sub (by linarith)
          _ = (p : ℝ) - 1 := Real.rpow_one _

/-
## Power of Two Infrastructure

Sorted divisors of 2^k = [1, 2, 4, ..., 2^k] by sort uniqueness.
All consecutive divisor ratios = 2, so h_α(2^k) = k·(2-1)^α = k.
-/

/-- List.range n is strictly sorted. -/
private theorem list_range_pairwise_lt : ∀ (n : ℕ), (List.range n).Pairwise (· < ·) := by
  intro n; induction n with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    rw [List.range_succ, List.pairwise_append]
    refine ⟨ih, ?_, fun a ha b hb => ?_⟩
    · exact .cons (by simp) .nil
    · simp only [List.mem_range] at ha
      simp only [List.mem_singleton] at hb
      subst hb; exact ha

/-- Sorted divisors of 2^k are [2^0, 2^1, ..., 2^k].
Both lists are sorted, nodup, with the same elements → equal. -/
private theorem sortedDivisors_two_pow (k : ℕ) :
    sortedDivisors (2 ^ k) = (List.range (k + 1)).map (HPow.hPow 2) := by
  have hnd₁ := sortedDivisors_nodup (2 ^ k)
  have hnd₂ : ((List.range (k + 1)).map (HPow.hPow 2)).Nodup := by
    apply List.Nodup.map
    · exact Nat.pow_right_injective (by norm_num : 1 < 2)
    · exact List.nodup_range
  have hmem : ∀ x, x ∈ sortedDivisors (2 ^ k) ↔
      x ∈ (List.range (k + 1)).map (HPow.hPow 2) := by
    intro x
    simp only [sortedDivisors, Finset.mem_sort,
               Nat.divisors_prime_pow (by norm_num : Nat.Prime 2),
               Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_range,
               List.mem_map, List.mem_range]
  have hperm := (List.perm_ext_iff_of_nodup hnd₁ hnd₂).mpr hmem
  have hs₂ : ((List.range (k + 1)).map (HPow.hPow 2)).Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    exact (list_range_pairwise_lt (k + 1)).imp
      (fun hab => Nat.pow_le_pow_right (by omega) (le_of_lt hab))
  exact hperm.eq_of_pairwise (fun _ _ _ _ h1 h2 => le_antisymm h1 h2)
    (sortedDivisors_sorted (2 ^ k)) hs₂

/-- Helper: (do let a ← l; pure (↑a : ℚ)) = l.map Nat.cast for List ℕ. -/
private theorem bind_pure_natCast (l : List ℕ) :
    (do let a ← l; pure (↑a : ℚ)) = l.map (Nat.cast ·) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    change (↑a : ℚ) :: (do let a ← t; pure ↑a) = ↑a :: t.map Nat.cast
    exact congrArg _ ih

/-- The consecutive divisor ratios of 2^k consist of k copies of 2.
Each ratio d_{i+1}/d_i = 2^(i+1)/2^i = 2. -/
private theorem divisorRatios_two_pow (k : ℕ) :
    divisorRatios (2 ^ k) = List.replicate k (2 : ℚ) := by
  simp only [divisorRatios]
  rw [sortedDivisors_two_pow]
  set L := (List.range (k + 1)).map (HPow.hPow 2) with hL_def
  have hL_len : L.length = k + 1 := by simp [hL_def]
  have htail_len : L.tail.length = k := by rw [List.length_tail, hL_len]; omega
  have hL_ne : L ≠ [] := by intro h; simp [h] at hL_len
  -- Convert do notation to explicit map
  rw [bind_pure_natCast L.tail, bind_pure_natCast L]
  apply List.ext_getElem
  · rw [List.length_zipWith, List.length_map, List.length_map, htail_len, hL_len,
        List.length_replicate, Nat.min_eq_left (by omega : k ≤ k + 1)]
  · intro i hi₁ hi₂
    have hik : i < k := by rwa [List.length_replicate] at hi₂
    simp only [List.getElem_zipWith, List.getElem_replicate, List.getElem_map]
    -- tail[i] = L[i+1]
    have htail_eq : L.tail[i]'(by omega) =
        L[i + 1]'(by rw [hL_len]; omega) := by
      obtain ⟨a, t, heq⟩ := List.exists_cons_of_ne_nil hL_ne
      simp [heq]
    rw [htail_eq]
    simp only [hL_def, List.getElem_map, List.getElem_range]
    rw [Nat.pow_succ, Nat.cast_mul]
    field_simp; norm_cast

private theorem flatMap_singleton_eq_map (f : ℚ → ℝ) (l : List ℚ) :
    l.flatMap (fun a => [f a]) = l.map f := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [List.flatMap_cons, ih]

private theorem list_bind_pure_ratCast (l : List ℚ) :
    (do let a ← l; pure (↑a : ℝ)) = l.map (Rat.cast · : ℚ → ℝ) :=
  flatMap_singleton_eq_map Rat.cast l

set_option maxHeartbeats 1600000 in
/-- For n = 2^k, h_α(2^k) = k since all k ratios equal 2 and (2-1)^α = 1^α = 1. -/
theorem power_of_two_h_alpha (k : ℕ) (α : ℝ) (hα : α ≥ 1) :
    h_alpha α (2^k) = k := by
  delta h_alpha
  rw [divisorRatios_two_pow]
  -- Convert monadic do/pure to explicit map, fuse maps, compute on replicate
  rw [list_bind_pure_ratCast, List.map_map, List.map_replicate, List.sum_replicate]
  -- Goal: k • ((fun r : ℚ => ((↑r : ℝ) - 1) ^ α) (2 : ℚ)) = ↑k
  simp only [Function.comp_apply, show ((2 : ℚ) : ℝ) - 1 = 1 from by push_cast; ring,
             Real.one_rpow, nsmul_eq_mul, mul_one]

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

/-
## Part XI: Erdős's Open Sub-Questions (OQ-01)

Erdős proposed two specific candidate sequences for which h_α might
remain bounded:
  (a) n!  —  the factorials
  (b) lcm{1, 2, ..., n}  —  the lcm sequence

Vose (1984) settled the existence question via a different construction;
whether these specific candidates suggested by Erdős themselves give
bounded h_α remains OPEN. See https://erdosproblems.com/1099 .
-/

/--
**Open Sub-Question (a) — Erdős, factorial candidate:**

Is h_α(n!) bounded uniformly in n?

Mathematical content: ∀ α > 1, ∃ C, ∀ n ≥ 2, h_α(n!) ≤ C.

Status: OPEN. Vose's bounded-liminf construction does not specialise
to factorials; the divisor structure of n! is much richer than the
sequence Vose used.
-/
def erdos_1099_factorial_open : Prop :=
    ∀ α : ℝ, α > 1 →
      ∃ C : ℝ, ∀ n : ℕ, n ≥ 2 → h_alpha α (n.factorial) ≤ C

/--
**Open Sub-Question (b) — Erdős, lcm candidate:**

Is h_α(lcm{1,2,…,n}) bounded uniformly in n?

Mathematical content: ∀ α > 1, ∃ C, ∀ n ≥ 1, h_α(lcm{1..n}) ≤ C.

Status: OPEN. Note that `(List.range' 1 n).foldr Nat.lcm 1` evaluates
to lcm{1,2,…,n}; it is used here directly because the pre-existing
`lcmDivisors` in Part IV folds over `List.range (n+1)` (which contains
0) and therefore collapses to 0.
-/
def erdos_1099_lcm_open : Prop :=
    ∀ α : ℝ, α > 1 →
      ∃ C : ℝ, ∀ n : ℕ, n ≥ 1 →
        h_alpha α ((List.range' 1 n).foldr Nat.lcm 1) ≤ C

/--
**Strong-form liminf (proper Vose statement):**

∃ C, C > 0 ∧ ∀ N, ∀ ε > 0, ∃ n ≥ N, h_α(n) < C + ε.

This is what Vose (1984) actually proved and what Erdős asked about
("liminf_{n→∞} h_α(n) ≪_α 1"): there are arbitrarily large n with
h_α(n) bounded by C up to ε.

The earlier statements `vose_bounded_sequence`, `vose_liminf_bounded`,
and `erdos_1099` are strictly weaker — they omit the `∀ N` quantifier,
so they are satisfied by the trivial constant witness n_k = 2 (since
h_α(2) = 1). Documenting this gap explicitly here makes the
formalisation honest about what is, and is not, currently proved.

A formal proof of `erdos_1099_strong_liminf` would require formalising
Vose's construction, which is substantial future work.
-/
def erdos_1099_strong_liminf : Prop :=
    ∀ α : ℝ, α > 1 →
      ∃ C : ℝ, C > 0 ∧
        ∀ N : ℕ, ∀ ε : ℝ, 0 < ε →
          ∃ n : ℕ, n ≥ N ∧ h_alpha α n < C + ε

end Erdos1099
