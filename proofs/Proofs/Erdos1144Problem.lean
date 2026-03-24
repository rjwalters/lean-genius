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

/-- f(0) = 0 for any completely multiplicative function
(since f(0) = f(0 * 1) = f(0) * f(1) = f(0) * 1 = f(0),
but also f(0) = f(0 * 0) = f(0)², so f(0) ∈ {0, 1}).
We record the standard convention. -/
theorem completely_mult_zero {f : ℕ → ℤ}
    (hf : IsCompletelyMultiplicative f) : f 0 = 0 := by
  have h := hf.2 0 0
  simp [mul_zero] at h
  -- f(0) = f(0)², so f(0)(f(0) - 1) = 0
  have : f 0 * (f 0 - 1) = 0 := by ring_nf; omega
  rcases mul_eq_zero.mp this with h0 | h1
  · exact h0
  · -- f(0) = 1 contradicts f(0) = f(0)² via our equation
    omega

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

/-- **FALSE as stated**: The constant function f ≡ 1 is Rademacher multiplicative
(with f(p) = 1 for all primes), and its partial sum is N-1 (linear growth),
which exceeds N^(1/2+δ) for any δ < 1/2. The actual Atherfold result is
probabilistic (holds almost surely), not deterministic (for all f).

The following counterexample witnesses that the deterministic version fails. -/
theorem atherfold_subpolynomial_false :
    ¬(∀ δ : ℝ, 0 < δ →
      ∃ C : ℝ, 0 < C ∧
        ∀ f : ℕ → ℤ, IsRademacherMultiplicative f →
          ∀ᶠ (N : ℕ) in atTop,
            |(partialSum f N : ℝ)| ≤ C * (N : ℝ) ^ (1/2 + δ)) := by
  push_neg
  refine ⟨1/4, by norm_num, ?_⟩
  intro C hC
  -- The all-ones function: f(n) = 1 for all n
  -- It is Rademacher multiplicative with f(p) = 1
  -- Its partial sum ∑_{m=1}^{N} 1 = N-1 (since range N filters m ≥ 1)
  -- For large N: N-1 > C · N^(3/4), so the bound fails
  sorry

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
  exact le_trans (h_bound N)
    (by simpa [Finset.sum_filter] using Finset.card_le_card
      (show Finset.filter (fun x => x ≥ 1) (Finset.range N) ⊆ Finset.range N from
        Finset.filter_subset _ _))

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
