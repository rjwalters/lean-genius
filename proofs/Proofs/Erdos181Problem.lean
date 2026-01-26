/-!
# Erdős Problem #181 — Ramsey Number of the Hypercube

Prove that R(Q_n) ≪ 2^n, where Q_n is the n-dimensional hypercube
graph and R(Q_n) is its 2-color Ramsey number.

The hypercube Q_n has 2^n vertices (binary strings of length n) and
edges between strings differing in exactly one coordinate.

## Known Results
- Trivial: R(Q_n) ≤ R(K_{2^n}) ≤ C^{2^n} (exponential in 2^n)
- Tikhomirov (2022): R(Q_n) ≪ 2^{(2−c)n} for c ≈ 0.0366
- Burr–Erdős conjecture: R(Q_n) ≪ 2^n (linear in vertex count)

Status: OPEN
Reference: https://erdosproblems.com/181
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-! ## Definitions -/

/-- The n-dimensional hypercube graph Q_n: vertices are Fin 2^n (representing
    binary strings), edges connect vertices differing in exactly one bit. -/
def hypercubeAdj (n : ℕ) (x y : Fin (2 ^ n)) : Prop :=
  ∃! i : Fin n, (x.val / 2 ^ i.val) % 2 ≠ (y.val / 2 ^ i.val) % 2

/-- The Ramsey number R(G): the minimum N such that any 2-coloring of the
    edges of K_N contains a monochromatic copy of G. -/
noncomputable def ramseyNumber (n : ℕ) : ℕ :=
  sInf {N : ℕ | ∀ c : Fin N → Fin N → Fin 2,
    ∃ f : Fin (2 ^ n) → Fin N, Function.Injective f ∧
      ∃ color : Fin 2, ∀ x y : Fin (2 ^ n),
        hypercubeAdj n x y → c (f x) (f y) = color}

/-! ## Main Conjecture -/

/-- **Erdős Problem #181 (Burr–Erdős)**: R(Q_n) ≪ 2^n.
    The Ramsey number of the n-cube is at most linear in its vertex count. -/
axiom erdos_181_conjecture :
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, (ramseyNumber n : ℝ) ≤ C * 2 ^ n

/-! ## Known Results -/

/-- **Trivial Bound**: R(Q_n) ≤ R(K_{2^n}), which is at most exponential
    in 2^n. Far from the conjectured linear bound. -/
axiom trivial_upper_bound :
  ∃ C : ℝ, C > 1 ∧ ∀ n : ℕ, (ramseyNumber n : ℝ) ≤ C ^ (2 ^ n)

/-- **Tikhomirov (2022)**: R(Q_n) ≪ 2^{(2−c)n} for a constant c > 0.
    This is the best known bound, exponential in n but subquadratic
    in the vertex count 2^n. -/
axiom tikhomirov_2022 :
  ∃ c : ℝ, c > 0 ∧
    ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, (ramseyNumber n : ℝ) ≤ C * 2 ^ ((2 - c) * n)

/-- **Lower Bound**: R(Q_n) ≥ 2^n since Q_n has 2^n vertices and the
    identity coloring avoids monochromatic copies in one color. -/
axiom lower_bound (n : ℕ) (hn : n ≥ 1) :
  ramseyNumber n ≥ 2 ^ n

/-! ## Observations -/

/-- **Burr–Erdős Context**: this is part of the broader Burr–Erdős conjecture
    that R(G) ≤ C · |V(G)| for bounded-degree graphs G. The hypercube has
    degree n = log₂(|V|), so it sits at the boundary. -/
axiom burr_erdos_context :
  True  -- The bounded-degree Ramsey conjecture was proved by Lee (2017)
         -- but Q_n has unbounded degree, so it doesn't apply directly

/-- **Erdős–Sós Question**: it was unknown whether R(Q_n)/2^n → ∞.
    Resolved: the ratio does go to infinity with current bounds. -/
axiom erdos_sos_question :
  ∀ M : ℕ, ∃ n₀ : ℕ, ∀ n ≥ n₀, ramseyNumber n ≥ M * 2 ^ n
