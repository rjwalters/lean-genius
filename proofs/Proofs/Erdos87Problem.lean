/-!
# Erdős Problem 87: Ramsey Numbers and Chromatic Number

For `ε > 0`, is it true that for sufficiently large `k`,
`R(G) > (1 - ε)^k · R(k)` for every graph `G` with `χ(G) = k`?

Stronger conjecture: does there exist `c > 0` such that
`R(G) > c · R(k)` for all large `k` and all `G` with `χ(G) = k`?

Erdős originally conjectured `R(G) ≥ R(k)`, disproved by Faudree–McKay:
the pentagonal wheel `W` has `χ(W) = 4` but `R(W) = 17 < R(4) = 18`.

*Reference:* [erdosproblems.com/87](https://www.erdosproblems.com/87)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open SimpleGraph Finset

/-! ## Axiomatized Ramsey and chromatic numbers -/

/-- The diagonal Ramsey number `R(k)` is the minimum `N` such that every
2-colouring of `K_N` edges contains a monochromatic `K_k`. -/
axiom diagonalRamsey : ℕ → ℕ

/-- `diagonalRamsey k` is always positive for `k ≥ 1`. -/
axiom diagonalRamsey_pos (k : ℕ) (hk : 1 ≤ k) : 0 < diagonalRamsey k

/-- The graph Ramsey number: smallest `N` such that every 2-colouring of
`K_N` contains a monochromatic copy of `G`. -/
axiom graphRamsey (n : ℕ) : SimpleGraph (Fin n) → ℕ

/-- Graph Ramsey number is positive. -/
axiom graphRamsey_pos (n : ℕ) (G : SimpleGraph (Fin n)) : 0 < graphRamsey n G

/-- The chromatic number of a finite simple graph: the minimum number of
colours needed to properly colour its vertices. -/
axiom chromaticNumber {n : ℕ} : SimpleGraph (Fin n) → ℕ

/-- The chromatic number is at most the number of vertices. -/
axiom chromaticNumber_le (n : ℕ) (G : SimpleGraph (Fin n)) : chromaticNumber G ≤ n

/-- The chromatic number is at least 1 for non-empty vertex sets. -/
axiom chromaticNumber_pos (n : ℕ) (hn : 0 < n) (G : SimpleGraph (Fin n)) :
    0 < chromaticNumber G

/-! ## Main conjecture -/

/-- Erdős Problem 87 (weak form): For every `ε > 0`, if `k` is large enough,
then `R(G) > (1-ε)^k · R(k)` for all `G` with `χ(G) = k`. -/
def ErdosProblem87 : Prop :=
    ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
        ∀ (G : SimpleGraph (Fin k)),
          chromaticNumber G = k →
            (1 - ε) ^ k * (diagonalRamsey k : ℝ) < (graphRamsey k G : ℝ)

/-- Erdős Problem 87 (strong form): There exists `c > 0` such that
`R(G) > c · R(k)` for all large `k` and all `G` with `χ(G) = k`. -/
def ErdosProblem87_strong : Prop :=
    ∃ c : ℝ, 0 < c ∧
      ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
        ∀ (G : SimpleGraph (Fin k)),
          chromaticNumber G = k →
            c * (diagonalRamsey k : ℝ) < (graphRamsey k G : ℝ)

/-! ## Known bounds -/

/-- Random colouring bound: `R(G) ≫ 2^{k/2}` for `χ(G) = k`. -/
axiom graphRamsey_exponential_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, 2 ≤ k →
      ∀ (G : SimpleGraph (Fin k)),
        chromaticNumber G = k →
          C * 2 ^ (k / 2 : ℝ) ≤ (graphRamsey k G : ℝ)

/-- Upper bound: `R(k) ≤ 4^k`. -/
axiom diagonalRamsey_upper (k : ℕ) :
    (diagonalRamsey k : ℝ) ≤ 4 ^ (k : ℝ)

/-! ## Counterexample to original conjecture -/

/-- Faudree–McKay: `R(W) = 17` for the pentagonal wheel `W` with `χ(W) = 4`,
while `R(4) = 18`, disproving `R(G) ≥ R(k)`. -/
axiom faudree_mckay_counterexample :
    ∃ (W : SimpleGraph (Fin 6)),
      chromaticNumber W = 4 ∧ graphRamsey 6 W = 17 ∧ diagonalRamsey 4 = 18
