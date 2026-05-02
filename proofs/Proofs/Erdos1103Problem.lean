/-
# Erdős Problem 1103: Squarefree Sumsets

Let `A` be an infinite sequence of positive integers such that every element of
`A + A = {a + b : a, b ∈ A}` is squarefree. How fast must `A` grow?

Erdős expected that no such sequence of polynomial growth exists — exponential
growth may be necessary.

## Known results

- An exponential-growth sequence satisfying the conditions exists.
- van Doorn–Tao (2025) proved an exponential upper bound: `a_j < exp(5j / log j)`
  for large `j`.
- van Doorn–Tao proved a polynomial lower bound: `a_j > 0.24 · j^{4/3}` for all `j`.
- Konyagin: `a_j ≫ j^{15/11 - o(1)}` (finite case).

*Reference:* [erdosproblems.com/1103](https://www.erdosproblems.com/1103)
-/

import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

open Finset Filter

/- ## Definitions -/

/-- `SquarefreeSumset A` holds when every element of `A + A` is squarefree,
i.e., for all `a, b ∈ A`, `a + b` is squarefree. -/
def SquarefreeSumset (A : Set ℕ) : Prop :=
    ∀ a ∈ A, ∀ b ∈ A, Squarefree (a + b)

/-- Increasing enumeration of an infinite set: `enumSet A j` is the `j`-th smallest
element of `A`. Previously axiomatized (2 axioms); now defined via Mathlib's `Nat.nth`
with properties proved from `Nat.nth_strictMono`, `Nat.nth_mem_of_infinite`, `Nat.nth_count`. -/
noncomputable def enumSet (A : Set ℕ) (j : ℕ) : ℕ := Nat.nth (· ∈ A) j

/-- The enumeration is strictly monotone and surjects onto `A`. -/
theorem enumSet_spec (A : Set ℕ) (hA : A.Infinite) :
    StrictMono (enumSet A) ∧ Set.range (enumSet A) = A := by
  constructor
  · exact Nat.nth_strictMono hA
  · ext n; simp only [Set.mem_range, enumSet]
    constructor
    · rintro ⟨j, rfl⟩; exact Nat.nth_mem_of_infinite hA j
    · intro hn; exact ⟨Nat.count (· ∈ A) n, Nat.nth_count hn⟩

/- ## Main conjecture -/

/-- Erdős Problem 1103: Does every infinite `A ⊆ ℕ` with `SquarefreeSumset A`
grow at least exponentially? That is, does there exist `C > 1` such that
`a_j ≥ C^j` for all large `j`? -/
def ErdosProblem1103 : Prop :=
    ∀ A : Set ℕ, A.Infinite → SquarefreeSumset A →
      ∃ (C : ℝ), 1 < C ∧ ∀ᶠ (j : ℕ) in atTop,
        C ^ (j : ℝ) ≤ (enumSet A j : ℝ)

/- ## Known bounds -/

/-- van Doorn–Tao upper bound: there exists an infinite squarefree-sumset
sequence with `a_j < exp(5j / log j)` for large `j`. -/
axiom vanDoorn_tao_upper :
    ∃ A : Set ℕ, A.Infinite ∧ SquarefreeSumset A ∧
      ∀ᶠ j in atTop,
        (enumSet A j : ℝ) < Real.exp (5 * (j : ℝ) / Real.log j)

/- van Doorn–Tao lower bound: `a_j > 0.24 · j^{4/3}` for any infinite
squarefree-sumset sequence. (Not axiomatized in this file.) -/
/- Konyagin's bound for finite sets: for `A ⊆ {1,...,N}` with squarefree sumset,
`|A| ≪ N^{11/15 + o(1)}`. (Not axiomatized in this file.) -/
/- ## Basic properties -/

/-- Every singleton set has a squarefree sumset iff `2a` is squarefree. -/
theorem squarefreeSumset_singleton (a : ℕ) :
    SquarefreeSumset {a} ↔ Squarefree (a + a) := by
  simp [SquarefreeSumset]

/-- The empty set trivially has a squarefree sumset. -/
theorem squarefreeSumset_empty : SquarefreeSumset ∅ := by
  intro a ha; exact absurd ha (Set.notMem_empty a)

/-- If `SquarefreeSumset A` and `B ⊆ A`, then `SquarefreeSumset B`. -/
theorem squarefreeSumset_subset {A B : Set ℕ} (h : B ⊆ A) (hA : SquarefreeSumset A) :
    SquarefreeSumset B :=
  fun a ha b hb => hA a (h ha) b (h hb)

/-- `1` is squarefree (basic fact used in constructions). -/
theorem one_squarefree : Squarefree 1 := squarefree_one

/-- {1} has a squarefree sumset since 1 + 1 = 2 is squarefree. -/
theorem squarefreeSumset_one : SquarefreeSumset {1} :=
  (squarefreeSumset_singleton 1).mpr (by decide)

/-- For a two-element set {a, b}, squarefree sumset requires
    2a, a+b, and 2b all squarefree. -/
theorem squarefreeSumset_pair (a b : ℕ) :
    SquarefreeSumset ({a, b} : Set ℕ) ↔
    Squarefree (a + a) ∧ Squarefree (a + b) ∧ Squarefree (b + b) := by
  simp only [SquarefreeSumset, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    exact ⟨h a (Or.inl rfl) a (Or.inl rfl),
           h a (Or.inl rfl) b (Or.inr rfl),
           h b (Or.inr rfl) b (Or.inr rfl)⟩
  · rintro ⟨haa, hab_sf, hbb⟩ x (rfl | rfl) y (rfl | rfl)
    · exact haa
    · exact hab_sf
    · rwa [add_comm]
    · exact hbb

/- ## Refutation of the exponential growth conjecture

The van Doorn–Tao upper bound shows there exists an infinite squarefree-sumset
sequence growing like exp(5j / log j), which is subexponential. Since C^j
eventually exceeds exp(5j / log j) for any C > 1, no exponential lower
bound can hold for that sequence, refuting ErdosProblem1103. -/

/-- For any C > 1, the subexponential function exp(5j / log j) is eventually
    smaller than the exponential C^j. This is the key analysis lemma. -/
theorem subexp_eventually_lt_exp (C : ℝ) (hC : 1 < C) :
    ∀ᶠ (j : ℕ) in atTop,
      Real.exp (5 * (j : ℝ) / Real.log (j : ℝ)) < C ^ (j : ℝ) := by
  have hC0 : (0 : ℝ) < C := by linarith
  have hlogC : 0 < Real.log C := Real.log_pos hC
  -- log(n : ℝ) → ∞ as n → ∞
  have hlog_tend : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- Eventually log n > 5 / log C
  have hev_log : ∀ᶠ n in atTop, 5 / Real.log C < Real.log (n : ℝ) :=
    hlog_tend.eventually (eventually_gt_atTop (5 / Real.log C))
  filter_upwards [hev_log, eventually_gt_atTop 2] with j hj_log hj_ge
  -- Derived: log j > 0 and j > 0 (since 5/log C > 0 and log j > 5/log C)
  have hlog_j_pos : (0 : ℝ) < Real.log (j : ℝ) :=
    lt_trans (div_pos (by norm_num : (0:ℝ) < 5) hlogC) hj_log
  have hj_pos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr (by omega)
  -- Rewrite C^(j : ℝ) = exp(log C * j) via rpow definition
  rw [Real.rpow_def_of_pos hC0]
  -- Goal: exp(5 * j / log j) < exp(log C * j)
  apply Real.exp_lt_exp.mpr
  -- From hj_log: 5 / log C < log j, i.e., 5 < log j * log C
  rw [div_lt_iff hlogC] at hj_log
  -- Goal: 5 * j / log j < log C * j
  rw [div_lt_iff hlog_j_pos]
  -- Goal: 5 * j < log C * j * log j. From hj_log: 5 < log j * log C, so 5*j < (log j * log C)*j
  nlinarith [mul_comm (Real.log C) (Real.log (j : ℝ))]

/-- The van Doorn–Tao upper bound refutes the conjecture that every infinite
    squarefree-sumset sequence must grow exponentially. -/
theorem erdos_1103_false : ¬ ErdosProblem1103 := by
  intro hconj
  obtain ⟨A, hAinf, hAsf, hAub⟩ := vanDoorn_tao_upper
  obtain ⟨C, hC1, hClb⟩ := hconj A hAinf hAsf
  have hexp := subexp_eventually_lt_exp C hC1
  -- Combine the three "eventually" statements
  have hcombined := hClb.and (hAub.and hexp)
  -- Extract a witness where all three hold simultaneously
  obtain ⟨j, hj_lb, hj_ub, hj_exp⟩ := hcombined.exists
  -- C^j ≤ a_j < exp(5j/log j) < C^j gives C^j < C^j
  linarith
