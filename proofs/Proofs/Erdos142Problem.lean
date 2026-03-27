/-
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

/- ## Definitions -/

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

/- ## Szemerédi's Theorem (qualitative) -/

/- ## Roth's Theorem (k = 3) -/

/- ## Lower Bound: Behrend's Construction -/

/- ## Upper Bound: Kelley–Meka (2023) -/

/- ## Erdős's $5,000 Question -/

/- ## Main Open Problem -/

/- ## For k = 4: Green–Tao -/
