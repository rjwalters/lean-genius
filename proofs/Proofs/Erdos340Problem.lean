/-!
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

/-! ## Core Definitions -/

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

/-! ## Known Initial Values (OEIS A005282) -/

/-- The first 11 values of the Mian–Chowla sequence. -/
axiom greedy_sidon_values :
    greedySidon 0 = 1 ∧ greedySidon 1 = 2 ∧ greedySidon 2 = 4 ∧
    greedySidon 3 = 8 ∧ greedySidon 4 = 13 ∧ greedySidon 5 = 21 ∧
    greedySidon 6 = 31 ∧ greedySidon 7 = 45 ∧ greedySidon 8 = 66 ∧
    greedySidon 9 = 81 ∧ greedySidon 10 = 97

/-! ## Basic Properties -/

/-- The greedy Sidon sequence is strictly increasing. -/
axiom greedy_sidon_strict_mono : StrictMono greedySidon

/-- At every stage, the set of selected elements is Sidon. -/
axiom greedy_sidon_is_sidon (n : ℕ) :
    IsSidonSet (Finset.image greedySidon (Finset.range (n + 1)))

/-! ## Known Lower Bound -/

/-- Trivial lower bound: |A ∩ [1,N]| ≥ cN^{1/3}.
    A Sidon set in [1,N] has at most ~√N elements (since C(k,2) ≤ N),
    and the greedy construction is at least cube-root efficient. -/
axiom lower_bound_cube_root :
    ∃ c > 0, ∀ N : ℕ, 1 ≤ N →
      c * (N : ℝ) ^ (1/3 : ℝ) ≤ (greedySidonCount N : ℝ)

/-- Upper bound: any Sidon set in [1,N] has ≤ √N + O(N^{1/4}) elements
    (Erdős–Turán). -/
axiom sidon_upper_bound :
    ∃ C > 0, ∀ N : ℕ, 1 ≤ N →
      (greedySidonCount N : ℝ) ≤ Real.sqrt N + C * (N : ℝ) ^ (1/4 : ℝ)

/-! ## The Main Conjecture -/

/-- **Erdős Problem #340**: The greedy Sidon sequence has nearly
    optimal growth: |A ∩ [1,N]| ≫ N^{1/2 - ε} for all ε > 0.
    This would mean the greedy construction is essentially as dense
    as the densest possible Sidon set. -/
axiom erdos_340_conjecture :
    ∀ ε > 0, ∃ c > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      c * (N : ℝ) ^ ((1 : ℝ)/2 - ε) ≤ (greedySidonCount N : ℝ)

/-! ## Difference Set Question -/

/-- The difference set A - A = {a - b : a, b ∈ A, a > b}. -/
noncomputable def greedySidonDiffSet : Set ℕ :=
  { d : ℕ | ∃ m n : ℕ, m > n ∧ greedySidon m - greedySidon n = d }

/-- Erdős–Graham also asked: does A - A have positive density?
    Known: 22, 33 are among the smallest uncertain cases. -/
axiom erdos_340_diff_set_question :
    ∃ δ > 0, ∀ N : ℕ, 1 ≤ N →
      δ * N ≤ ((Finset.range (N + 1)).filter (· ∈ greedySidonDiffSet)).card

/-! ## Connection to Random Sidon Sets -/

/-- A random Sidon set in [1,N] has ~√N elements. The conjecture says
    the greedy construction is nearly as good as random. -/
axiom random_sidon_context :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
      (greedySidonCount N : ℝ) ≤ Real.sqrt N * (1 + ε)
