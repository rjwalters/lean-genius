/-
# Erdős Problem #340 — Growth of the Greedy Sidon Sequence

The greedy Sidon sequence (Mian–Chowla sequence) is A = {1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97, ...}:
start with 1, then iteratively include the smallest integer preserving
the Sidon property (no non-trivial solutions to a + b = c + d).

**Conjecture:** |A ∩ {1,...,N}| ≫ N^{1/2 - ε} for all ε > 0.

**Status: OPEN.**

Known: trivial lower bound Ω(N^{1/3}). The sequence is OEIS A005282.
Erdős and Graham also asked whether A - A has positive density.

Reference: https://erdosproblems.com/340
-/

import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Tactic

open Filter Finset

/- ## Core Definitions -/

/-- A Sidon set (B₂ set): all pairwise sums a + b (a ≤ b, a,b ∈ S) are distinct. -/
def IsSidonSet (S : Finset ℕ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S,
    a ≤ b → c ≤ d → a + b = c + d → a = c ∧ b = d

/-- The greedy Sidon sequence: a(0) = 1, a(n+1) is the smallest integer
    not in {a(0),...,a(n)} such that adding it preserves the Sidon property. -/
noncomputable def greedySidon : ℕ → ℕ
  | 0 => 1
  | n + 1 => sInf { m : ℕ | m > greedySidon n ∧
      IsSidonSet (Finset.image greedySidon (Finset.range (n + 1)) ∪ {m}) }

/-- The counting function: |A ∩ {1,...,N}|. -/
noncomputable def greedySidonCount (N : ℕ) : ℕ :=
  (Finset.range N).filter (fun k => greedySidon k ≤ N) |>.card

/- ## Known Initial Values (OEIS A005282) -/

/- ## Basic Properties -/

/- ## Known Lower Bound -/

/- ## The Main Conjecture -/

/- ## Difference Set Question -/

/-- The difference set A - A = {a - b : a, b ∈ A, a > b}. -/
noncomputable def greedySidonDiffSet : Set ℕ :=
  { d : ℕ | ∃ m n : ℕ, m > n ∧ greedySidon m - greedySidon n = d }

/- ## Connection to Random Sidon Sets -/
