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

/-- The first 11 terms of the Mian-Chowla sequence match OEIS A005282:
    1, 2, 4, 8, 13, 21, 31, 45, 66, 81, 97. -/
axiom greedy_sidon_values :
    greedySidon 0 = 1 ∧ greedySidon 1 = 2 ∧ greedySidon 2 = 4 ∧
    greedySidon 3 = 8 ∧ greedySidon 4 = 13 ∧ greedySidon 5 = 21 ∧
    greedySidon 6 = 31 ∧ greedySidon 7 = 45 ∧ greedySidon 8 = 66 ∧
    greedySidon 9 = 81 ∧ greedySidon 10 = 97

/- ## Basic Properties -/

/-- The greedy Sidon sequence is strictly increasing:
    each element is larger than the preceding one. -/
axiom greedy_sidon_strict_mono : StrictMono greedySidon

/-- Every prefix of the greedy sequence forms a valid Sidon set. -/
axiom greedy_sidon_is_sidon : ∀ n : ℕ,
    IsSidonSet (Finset.image greedySidon (Finset.range (n + 1)))

/- ## Known Lower Bound -/

/-- **Known lower bound:** the greedy Sidon sequence grows at least as N^{1/3}.
    There exists a constant C > 0 such that |A ∩ [1,N]| ≥ C · N^{1/3} for all N ≥ 1.
    This follows from a forbidden-sum counting argument: O(k²) blocked values per step
    means the k-th element is at most O(k³), so k ≥ Ω(N^{1/3}). -/
axiom greedy_sidon_lower_bound : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N →
    C * (N : ℝ) ^ ((1 : ℝ) / 3) ≤ (greedySidonCount N : ℝ)

/-- **Erdős–Turán upper bound:** any Sidon set in [1,N] has at most √N + O(N^{1/4}) elements.
    So the greedy sequence satisfies f(N) ≤ √N + C·N^{1/4} for some constant C > 0. -/
axiom erdos_turan_upper_bound : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 0 < N →
    (greedySidonCount N : ℝ) ≤ Real.sqrt (N : ℝ) + C * (N : ℝ) ^ ((1 : ℝ) / 4)

/- ## The Main Conjecture -/

/-- **Main conjecture (open):** The greedy Sidon sequence achieves near-optimal growth.
    For every ε > 0 there exists C_ε > 0 such that |A ∩ [1,N]| ≥ C_ε · N^{1/2 - ε}
    for all sufficiently large N. This would show greedy is nearly as good as optimal. -/
axiom greedy_sidon_growth_conjecture : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
    C * (N : ℝ) ^ ((1 : ℝ) / 2 - ε) ≤ (greedySidonCount N : ℝ)

/- ## Difference Set Question -/

/-- The difference set A - A = {a(m) - a(n) : m > n}. -/
noncomputable def greedySidonDiffSet : Set ℕ :=
  { d : ℕ | ∃ m n : ℕ, m > n ∧ greedySidon m - greedySidon n = d }

/-- **Open question (Erdős–Graham):** Does the difference set A - A have positive
    upper density? There exists δ > 0 with infinitely many N satisfying
    |{d ≤ N : d ∈ A-A}| ≥ δ · N. -/
axiom greedy_sidon_diffset_pos_density : ∃ δ : ℝ, 0 < δ ∧ ∀ B : ℕ, ∃ N : ℕ,
    B ≤ N ∧ δ * (N : ℝ) ≤
    (Set.ncard (greedySidonDiffSet ∩ Set.Icc 1 N) : ℝ)

/- ## Connection to Random Sidon Sets -/
/- A random Sidon set in [1,N] has expected size ~N^{1/3} (birthday paradox).
   The greedy sequence empirically achieves ~N^{0.497}, far exceeding randomness. -/
