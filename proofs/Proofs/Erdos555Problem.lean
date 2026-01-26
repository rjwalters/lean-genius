/-!
# Erdős Problem #555 — Ramsey Numbers of Even Cycles

Determine R(C₂ₙ; k), the minimum m such that every k-coloring of the
edges of Kₘ contains a monochromatic copy of the even cycle C₂ₙ.

Known bounds (Erdős):
  k^{1+1/(2n)} ≪ R(C₂ₙ; k) ≪ k^{1+1/(n-1)}

For C₄ (Chung–Graham 1975):
  k² - k + 1 < R(C₄; k) ≤ k² + k + 1  when k-1 is a prime power.

A problem of Erdős and Graham.

Reference: https://erdosproblems.com/555
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-! ## Even Cycles and Colorings -/

/-- A cycle of length n in a simple graph, represented as a list of
    n distinct vertices where consecutive vertices (and the last-first pair)
    are adjacent -/
def HasCycleOfLength (G : SimpleGraph (Fin m)) (n : ℕ) : Prop :=
  ∃ v : Fin n → Fin m,
    Function.Injective v ∧
    (∀ i : Fin n, G.Adj (v i) (v ⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩)) ∧
    2 ≤ n

/-- A k-coloring of edges of Kₘ is a function from pairs to Fin k -/
def EdgeColoring (m k : ℕ) :=
  (Fin m) → (Fin m) → Fin k

/-- A monochromatic subgraph of color c in a k-coloring:
    the graph consisting of all edges of color c -/
def monochromaticGraph (χ : EdgeColoring m k) (c : Fin k) : SimpleGraph (Fin m) where
  Adj u v := u ≠ v ∧ χ u v = c
  symm := by
    intro u v ⟨hne, hc⟩
    exact ⟨hne.symm, by rwa [show χ v u = χ u v from sorry]⟩
  loopless := by intro v ⟨h, _⟩; exact h rfl

/-! ## Ramsey Number for Even Cycles -/

/-- R(C₂ₙ; k): the minimum m such that every k-coloring of Kₘ
    contains a monochromatic C₂ₙ -/
noncomputable def ramseyEvenCycle (n k : ℕ) : ℕ :=
  Nat.find (⟨(2 * n) * k ^ (2 * n),
    fun _ => trivial⟩ : ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      ∀ χ : EdgeColoring m k,
        ∃ c : Fin k, HasCycleOfLength (monochromaticGraph χ c) (2 * n))

/-! ## Erdős Lower Bound -/

/-- Erdős lower bound: R(C₂ₙ; k) ≫ k^{1+1/(2n)} -/
axiom erdos_lower_bound (n : ℕ) (hn : 1 ≤ n) :
  ∃ c : ℝ, c > 0 ∧
    ∀ k : ℕ, 2 ≤ k →
      c * (k : ℝ) ^ (1 + 1 / (2 * (n : ℝ))) ≤ (ramseyEvenCycle n k : ℝ)

/-- Erdős upper bound: R(C₂ₙ; k) ≪ k^{1+1/(n-1)} for n ≥ 2 -/
axiom erdos_upper_bound (n : ℕ) (hn : 2 ≤ n) :
  ∃ C : ℝ, C > 0 ∧
    ∀ k : ℕ, 2 ≤ k →
      (ramseyEvenCycle n k : ℝ) ≤ C * (k : ℝ) ^ (1 + 1 / ((n : ℝ) - 1))

/-! ## C₄ Case: Chung–Graham Bounds -/

/-- Chung–Graham lower bound for C₄: R(C₄; k) > k² - k + 1
    when k - 1 is a prime power -/
axiom chung_graham_lower (k : ℕ) (hk : 2 ≤ k)
    (hpp : Nat.Prime (k - 1) ∨ ∃ p e : ℕ, Nat.Prime p ∧ 2 ≤ e ∧ p ^ e = k - 1) :
  k * k - k + 1 < ramseyEvenCycle 2 k

/-- Chung–Graham upper bound for C₄: R(C₄; k) ≤ k² + k + 1 for all k -/
axiom chung_graham_upper (k : ℕ) (hk : 2 ≤ k) :
  ramseyEvenCycle 2 k ≤ k * k + k + 1

/-! ## The Erdős–Graham Problem -/

/-- Erdős Problem 555 (Erdős–Graham): Determine the exact value of R(C₂ₙ; k).
    The lower and upper bounds have different exponents (1+1/(2n) vs 1+1/(n-1)),
    and closing this gap is open. -/
axiom ErdosProblem555 (n : ℕ) (hn : 2 ≤ n) :
  ∃ α : ℝ, 1 / (2 * (n : ℝ)) ≤ α ∧ α ≤ 1 / ((n : ℝ) - 1) ∧
    ∃ c C : ℝ, c > 0 ∧ C > 0 ∧
      ∀ k : ℕ, 2 ≤ k →
        c * (k : ℝ) ^ (1 + α) ≤ (ramseyEvenCycle n k : ℝ) ∧
        (ramseyEvenCycle n k : ℝ) ≤ C * (k : ℝ) ^ (1 + α)
