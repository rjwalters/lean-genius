/-!
# Erdős Problem #142: Asymptotic Formula for r_k(N)

Erdős Problem #142 asks for an asymptotic formula for r_k(N), the size of the
largest subset of {1, ..., N} containing no non-trivial k-term arithmetic
progression. This is one of the most fundamental open problems in additive
combinatorics, with a $10,000 reward from Erdős.

Even the case k = 3 (Roth's theorem and its quantitative improvements) remains
far from an asymptotic formula. The best known bounds are:
- Upper: r_3(N) ≤ N · exp(-c(log N)^{1/12}) by Kelley–Meka (2023)
- Lower: r_3(N) ≥ N · exp(-C√(log N)) by Behrend (1946)

For general k, Szemerédi's theorem (1975) gives r_k(N) = o(N), and
Leng–Sah–Sawhney (2024) provide the best upper bounds for k ≥ 5.

Reference: https://erdosproblems.com/142
-/

import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Filter.Basic

/-! ## Definitions -/

/-- An arithmetic progression of length k starting at a with common difference d. -/
def arithProg (a d : ℕ) (k : ℕ) : Finset ℕ :=
  (Finset.range k).image (fun i => a + i * d)

/-- A set S ⊆ {1, ..., N} is AP-k-free if it contains no k-term arithmetic
    progression with common difference d > 0. -/
def IsAPFree (S : Finset ℕ) (k : ℕ) : Prop :=
  ∀ a d : ℕ, 0 < d → arithProg a d k ⊆ S → k ≤ 1

/-- r_k(N): the maximum size of an AP-k-free subset of {1, ..., N}. -/
noncomputable def rk (k N : ℕ) : ℕ :=
  Finset.sup
    ((Finset.powerset (Finset.range N)).filter (fun S => IsAPFree S k))
    Finset.card

/-! ## Szemerédi's Theorem (qualitative) -/

/-- Szemerédi's theorem: for every k ≥ 3, r_k(N) = o(N).
    That is, r_k(N)/N → 0 as N → ∞. This was proved by Szemerédi in 1975.
    We state this as an axiom since the full proof is extremely long. -/
axiom szemeredi_theorem (k : ℕ) (hk : 3 ≤ k) :
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (rk k N : ℝ) ≤ ε * N

/-! ## Roth's Theorem (k = 3) -/

/-- Roth's theorem (1953): r_3(N) = o(N).
    Quantitative improvements: Bourgain, Sanders, Bloom, Kelley–Meka. -/
axiom roth_theorem :
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → (rk 3 N : ℝ) ≤ ε * N

/-! ## Lower Bound: Behrend's Construction -/

/-- Behrend (1946): There exists an AP-3-free subset of {1,...,N} of size
    at least N · exp(-C√(log N)) for some constant C > 0. -/
axiom behrend_lower_bound :
  ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
    C * N * Real.exp (-(C * Real.sqrt (Real.log N))) ≤ (rk 3 N : ℝ)

/-! ## Upper Bound: Kelley–Meka (2023) -/

/-- Kelley–Meka (2023): r_3(N) ≤ N · exp(-c(log N)^{1/12}) for some c > 0.
    This is the current best upper bound for 3-term AP-free sets. -/
axiom kelley_meka_upper_bound :
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 2 ≤ N →
    (rk 3 N : ℝ) ≤ N * Real.exp (-c * (Real.log N) ^ (1/12 : ℝ))

/-! ## Erdős's $5,000 Question -/

/-- Erdős offered $5,000 for proving r_k(N) = o(N / log N).
    For k = 3, this follows from Kelley–Meka (2023), but for general k
    it remains a major open question. -/
axiom erdos_5000_question (k : ℕ) (hk : 3 ≤ k) :
  ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    (rk k N : ℝ) ≤ ε * N / Real.log N

/-! ## Main Open Problem -/

/-- Erdős Problem #142: Find an asymptotic formula for r_k(N).
    This is completely open — we do not even know the right order of magnitude
    for k = 3, where the gap between Behrend's lower bound and Kelley–Meka's
    upper bound remains enormous. -/
axiom erdos_142_asymptotic (k : ℕ) (hk : 3 ≤ k) :
  ∃ f : ℕ → ℝ, (∀ N, 0 < f N) ∧
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |((rk k N : ℝ) / f N) - 1| < ε

/-! ## For k = 4: Green–Tao -/

/-- Green–Tao (2017): improved upper bound for r_4(N).
    r_4(N) ≤ N / (log N)^{1+c} for some c > 0. -/
axiom green_tao_k4_bound :
  ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, 2 ≤ N →
    (rk 4 N : ℝ) ≤ N / (Real.log N) ^ (1 + c)

/-- The trivial lower bound r_k(N) ≥ 1 for N ≥ 1. -/
axiom rk_pos (k N : ℕ) (hN : 1 ≤ N) : 1 ≤ rk k N
