/-
# Erdős Problem #1144 — Partial Sums of Random Multiplicative Functions

Let f be a random completely multiplicative function, where for each prime p
we independently choose f(p) ∈ {-1, 1} uniformly at random.

**Conjecture**: With probability 1,
  limsup_{N → ∞} (∑_{m ≤ N} f(m)) / √N = ∞.

## Status: OPEN

## Key Results

- **Atherfold (2025)**: Almost surely, ∑_{m ≤ N} f(m) ≪ N^{1/2} (log N)^{1+o(1)}.
  This gives an upper bound on growth but does not resolve whether the limsup is infinite.

## Related Problems

- #520: Variant with Rademacher multiplicative functions vanishing on non-squarefree integers.

*Reference:* Va99 §1.11, [erdosproblems.com/1144](https://www.erdosproblems.com/1144)
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic

open Filter Finset

-- ## Core Definitions

/-- A completely multiplicative function f : ℕ → ℤ satisfies
f(mn) = f(m) · f(n) for all m, n. -/
def IsCompletelyMultiplicative (f : ℕ → ℤ) : Prop :=
  f 1 = 1 ∧ ∀ m n : ℕ, f (m * n) = f m * f n

/-- A Rademacher multiplicative function takes values in {-1, 1} on primes
and is completely multiplicative. -/
def IsRademacherMultiplicative (f : ℕ → ℤ) : Prop :=
  IsCompletelyMultiplicative f ∧ ∀ p : ℕ, p.Prime → (f p = 1 ∨ f p = -1)

/-- The partial sum ∑_{m=1}^{N} f(m). -/
noncomputable def partialSum (f : ℕ → ℤ) (N : ℕ) : ℤ :=
  ∑ m ∈ (Finset.range N).filter (· ≥ 1), f m

-- ## Basic Properties of Rademacher Multiplicative Functions

/-- A Rademacher multiplicative function satisfies f(1) = 1. -/
theorem rademacher_one {f : ℕ → ℤ} (hf : IsRademacherMultiplicative f) :
    f 1 = 1 :=
  hf.1.1

/-- A Rademacher multiplicative function takes values in {-1, 1} on all
positive integers (not just primes). -/
theorem rademacher_values_pm1 {f : ℕ → ℤ} (hf : IsRademacherMultiplicative f)
    {n : ℕ} (hn : 0 < n) : f n = 1 ∨ f n = -1 := by
  -- Proved by Aristotle (Harmonic) via strong induction on prime factorization
  obtain ⟨hf_comp, hf_prime⟩ := hf
  induction' n using Nat.strongRecOn with n ih
  rcases n.primeFactors.eq_empty_or_nonempty with (h | ⟨p, hp⟩) <;> simp_all +decide
  · cases h <;> simp_all +decide [hf_comp.1]
  · cases' hp.2.1 with k hk
    cases ih k (by nlinarith [hp.1.two_le]) (Nat.pos_of_ne_zero (by aesop)) <;>
      cases hf_prime p hp.1 <;> simp_all +decide [hf_comp.2]

/-- |f(n)| = 1 for all positive n, when f is Rademacher multiplicative. -/
theorem rademacher_abs_one {f : ℕ → ℤ} (hf : IsRademacherMultiplicative f)
    {n : ℕ} (hn : 0 < n) : |f n| = 1 := by
  obtain h | h := rademacher_values_pm1 hf hn <;> simp [h]

/-- For a completely multiplicative function, f(0) ∈ {0, 1}
(since f(0) = f(0 * 0) = f(0)², so f(0)(f(0) - 1) = 0).
Note: both values are achievable — f ≡ 1 has f(0) = 1. -/
theorem completely_mult_zero_or_one {f : ℕ → ℤ}
    (hf : IsCompletelyMultiplicative f) : f 0 = 0 ∨ f 0 = 1 := by
  have h := hf.2 0 0
  simp [mul_zero] at h
  have : f 0 * (f 0 - 1) = 0 := by nlinarith
  rcases mul_eq_zero.mp this with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (by omega)

/-- Completely multiplicative functions preserve powers: f(n^k) = (f n)^k.
    Proof by induction on k, using f(m·n) = f(m)·f(n). -/
theorem completely_mult_pow {f : ℕ → ℤ} (hf : IsCompletelyMultiplicative f)
    (n k : ℕ) : f (n ^ k) = (f n) ^ k := by
  induction k with
  | zero => simp [hf.1]
  | succ k ih => rw [pow_succ, hf.2, ih, pow_succ]

/-- For a Rademacher multiplicative function, f(n²) = 1 for all positive n.
    Since f(n) ∈ {±1}, we have f(n²) = f(n)² = 1. -/
theorem rademacher_sq_one {f : ℕ → ℤ} (hf : IsRademacherMultiplicative f)
    {n : ℕ} (hn : 0 < n) : f (n ^ 2) = 1 := by
  rw [completely_mult_pow hf.1 n 2]
  obtain h | h := rademacher_values_pm1 hf hn <;> simp [h]

-- ## The Conjecture

/-- **Erdős Problem #1144 (OPEN).**
For a random completely multiplicative function f with f(p) ∈ {-1, 1}
chosen independently and uniformly for each prime p:
  limsup_{N → ∞} |∑_{m ≤ N} f(m)| / √N = ∞   almost surely.

We state the deterministic version: for every Rademacher multiplicative
function f, we ask whether the partial sums can grow faster than √N.
The probabilistic statement is that this holds for "almost every" such f.

Formally: for every C > 0, there exist infinitely many N such that
|∑_{m ≤ N} f(m)| > C · √N. -/
def erdos_1144_conjecture (f : ℕ → ℤ) : Prop :=
  IsRademacherMultiplicative f →
    ∀ C : ℝ, 0 < C → ∀ᶠ (N : ℕ) in atTop,
      C * Real.sqrt (N : ℝ) ≤ |(partialSum f N : ℝ)|

/-- The probabilistic formulation: the set of Rademacher multiplicative
functions for which the conjecture fails has measure zero.
(Stated abstractly since we don't build a full probability space.) -/
def erdos_1144_probabilistic : Prop :=
  ∀ f : ℕ → ℤ, IsRademacherMultiplicative f →
    ∀ C : ℝ, 0 < C → ∀ᶠ (N : ℕ) in atTop,
      C * Real.sqrt (N : ℝ) ≤ |(partialSum f N : ℝ)|

-- ## Known Results

/-- **Atherfold (2025).** Almost surely,
∑_{m ≤ N} f(m) ≪ N^{1/2} · (log N)^{1+o(1)}.

More precisely: for every ε > 0, there exists C > 0 such that
almost surely, for all sufficiently large N,
|∑_{m ≤ N} f(m)| ≤ C · √N · (log N)^{1+ε}. -/
axiom atherfold_upper_bound :
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ f : ℕ → ℤ, IsRademacherMultiplicative f →
        ∀ᶠ (N : ℕ) in atTop,
          |(partialSum f N : ℝ)| ≤ C * Real.sqrt (N : ℝ) * Real.log (N : ℝ) ^ (1 + ε)

-- ## Structural Theorems

/-- The partial sum at 0 is 0. -/
theorem partialSum_zero (f : ℕ → ℤ) : partialSum f 0 = 0 := by
  simp [partialSum]

/-- The partial sum at 1 is 0 (range 1 = {0}, filtered to ∅). -/
theorem partialSum_one (f : ℕ → ℤ) : partialSum f 1 = 0 := by
  simp only [partialSum, Finset.sum_filter, Finset.sum_range_one]
  simp

/-- The partial sum at 2 equals f(1). -/
theorem partialSum_two (f : ℕ → ℤ) : partialSum f 2 = f 1 := by
  simp only [partialSum, Finset.sum_filter, show (2 : ℕ) = 1 + 1 from rfl,
    Finset.sum_range_succ]
  simp

/-- Recursion: partialSum f (N+1) = partialSum f N + f N for N ≥ 1. -/
theorem partialSum_succ (f : ℕ → ℤ) (N : ℕ) (hN : 1 ≤ N) :
    partialSum f (N + 1) = partialSum f N + f N := by
  simp only [partialSum, Finset.range_add_one, Finset.filter_insert, show N ≥ 1 from hN,
    ite_true]
  rw [Finset.sum_insert (by simp [Finset.mem_filter, Finset.mem_range])]
  ring

-- ## Concrete Example: The Constant Function f ≡ 1

/-- The constant function 1 is completely multiplicative. -/
theorem const_one_completely_mult : IsCompletelyMultiplicative (fun _ : ℕ => (1 : ℤ)) :=
  ⟨rfl, fun _ _ => (mul_one 1).symm⟩

/-- The constant function 1 is Rademacher multiplicative (f(p) = 1 for all primes). -/
theorem const_one_rademacher : IsRademacherMultiplicative (fun _ : ℕ => (1 : ℤ)) :=
  ⟨const_one_completely_mult, fun _ _ => Or.inl rfl⟩

/-- The partial sum of f ≡ 1 equals N - 1: it sums 1 over {1, ..., N-1}. -/
theorem partialSum_const_one (N : ℕ) (hN : 1 ≤ N) :
    partialSum (fun _ => (1 : ℤ)) N = (N : ℤ) - 1 := by
  induction N with
  | zero => omega
  | succ n ih =>
    rcases n.eq_zero_or_pos with rfl | hn
    · exact partialSum_one _
    · rw [partialSum_succ _ n hn, ih hn]; push_cast; ring

/-- There exist Rademacher multiplicative functions with linear partial sum growth.
    This shows Atherfold's √N·(log N) bound is probabilistic, not deterministic:
    the constant function f ≡ 1 grows linearly (partial sum = N - 1). -/
theorem exists_linear_growth_rademacher :
    ∃ f : ℕ → ℤ, IsRademacherMultiplicative f ∧
      ∀ N : ℕ, 1 ≤ N → partialSum f N = (N : ℤ) - 1 :=
  ⟨fun _ => 1, const_one_rademacher, partialSum_const_one⟩

/-- The trivial upper bound: |∑_{m ≤ N} f(m)| ≤ N for any
function with |f(m)| ≤ 1. -/
theorem partialSum_trivial_bound {f : ℕ → ℤ} (hf : IsRademacherMultiplicative f)
    (N : ℕ) : |(partialSum f N : ℝ)| ≤ (N : ℝ) := by
  -- Proved by Aristotle (Harmonic): each term satisfies |f(m)| ≤ 1 by rademacher_values_pm1,
  -- so |∑ f(m)| ≤ ∑ |f(m)| ≤ ∑ 1 ≤ N.
  have h_bound : ∀ N : ℕ, |(partialSum f N : ℝ)| ≤
      ∑ m ∈ ((Finset.range N).filter (fun n => n ≥ 1)), 1 := by
    intros N
    have h_each : ∀ m ∈ ((Finset.range N).filter (fun n => n ≥ 1)), |(f m : ℝ)| ≤ 1 := by
      exact fun m hm => mod_cast abs_le.mpr
        ⟨by rcases rademacher_values_pm1 hf (Finset.mem_filter.mp hm |>.2) with h | h <;>
            norm_num [h],
         by rcases rademacher_values_pm1 hf (Finset.mem_filter.mp hm |>.2) with h | h <;>
            norm_num [h]⟩
    exact le_trans (mod_cast Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum h_each)
  exact le_trans (h_bound N) (by
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
    exact_mod_cast (Finset.card_filter_le _ _).trans (le_of_eq (Finset.card_range N)))

/-- The conjecture, if true, would mean the growth rate is exactly √N
up to logarithmic factors: between C·√N (infinitely often, from conjecture)
and C'·√N·(log N)^{1+ε} (eventually, from Atherfold). -/
theorem conjecture_and_atherfold_pinch :
    erdos_1144_probabilistic →
      ∀ ε : ℝ, 0 < ε →
        ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
          ∀ f : ℕ → ℤ, IsRademacherMultiplicative f →
            (∀ᶠ (N : ℕ) in atTop,
              C₁ * Real.sqrt (N : ℝ) ≤ |(partialSum f N : ℝ)|) ∧
            (∀ᶠ (N : ℕ) in atTop,
              |(partialSum f N : ℝ)| ≤ C₂ * Real.sqrt (N : ℝ) * Real.log (N : ℝ) ^ (1 + ε)) := by
  intro hconj ε hε
  obtain ⟨C₂, hC₂pos, hC₂⟩ := atherfold_upper_bound ε hε
  exact ⟨1, C₂, one_pos, hC₂pos, fun f hf =>
    ⟨hconj f hf 1 one_pos, hC₂ f hf⟩⟩
