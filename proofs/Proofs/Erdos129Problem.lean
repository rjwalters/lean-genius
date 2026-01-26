/-!
# Erdős Problem 129: Ramsey Numbers Avoiding Monochromatic Cliques

Let `R(n; k, r)` denote the smallest `N` such that if the edges of `K_N` are
`r`-colored, there exists a set of `n` vertices containing no monochromatic `K_k`.

Erdős and Gyárfás conjectured that there exist constants `C₁, C₂ > 1`
(depending only on `r`) such that
$$C_1^{n^{1/(k-1)}} < R(n; k, r) < C_2^{n^{1/(k-1)}}.$$

They proved the lower bound for `k = 3`. The upper bound for `k = 3` remains open,
though Girão noted the original formulation may need clarification.

*Reference:* [erdosproblems.com/129](https://www.erdosproblems.com/129)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open Finset

/-! ## Edge coloring and monochromatic clique avoidance -/

/-- An `r`-coloring of edges of the complete graph on `Fin N`. -/
def EdgeColoring (N : ℕ) (r : ℕ) : Type :=
    { p : Fin N × Fin N // p.1 < p.2 } → Fin r

/-- A set `S` of vertices avoids monochromatic `K_k` in color `c` if no `k`-element
subset of `S` has all edges colored `c`. -/
def AvoidsMono (N : ℕ) (r : ℕ) (coloring : EdgeColoring N r)
    (S : Finset (Fin N)) (k : ℕ) (c : Fin r) : Prop :=
    ∀ T : Finset (Fin N), T ⊆ S → T.card = k →
      ∃ e : { p : Fin N × Fin N // p.1 < p.2 },
        e.val.1 ∈ T ∧ e.val.2 ∈ T ∧ coloring e ≠ c

/-- A set `S` contains no monochromatic `K_k` (in any color). -/
def NoMonoClique (N : ℕ) (r : ℕ) (coloring : EdgeColoring N r)
    (S : Finset (Fin N)) (k : ℕ) : Prop :=
    ∀ c : Fin r, AvoidsMono N r coloring S k c

/-- `HasRamseyAvoid N n k r` holds when every `r`-coloring of `K_N`
admits a set of `n` vertices with no monochromatic `K_k`. -/
def HasRamseyAvoid (N n k r : ℕ) : Prop :=
    ∀ coloring : EdgeColoring N r,
      ∃ S : Finset (Fin N), S.card ≥ n ∧ NoMonoClique N r coloring S k

/-! ## Main conjecture: exponential bounds -/

/-- The Erdős–Gyárfás conjecture for general `k`: there exist `C₁, C₂ > 1` such that
`C₁^{n^{1/(k-1)}} < R(n;k,r) < C₂^{n^{1/(k-1)}}` for all sufficiently large `n`. -/
def ErdosProblem129 (k r : ℕ) : Prop :=
    2 ≤ k ∧ 2 ≤ r →
    ∃ (C₁ C₂ : ℝ), 1 < C₁ ∧ 1 < C₂ ∧
      ∀ᶠ n in Filter.atTop, ∀ N : ℕ,
        HasRamseyAvoid N n k r →
          C₁ ^ ((n : ℝ) ^ (1 / ((k : ℝ) - 1))) < (N : ℝ) ∧
          ∃ M : ℕ, HasRamseyAvoid M n k r ∧
            (M : ℝ) < C₂ ^ ((n : ℝ) ^ (1 / ((k : ℝ) - 1)))

/-- The specific case `k = 3`: prove `R(n;3,r) < C^{√n}` for some `C > 1`. -/
def ErdosProblem129_k3 (r : ℕ) : Prop :=
    2 ≤ r →
    ∃ (C : ℝ), 1 < C ∧ ∀ᶠ n in Filter.atTop,
      ∃ M : ℕ, HasRamseyAvoid M n 3 r ∧ (M : ℝ) < C ^ Real.sqrt n

/-! ## Known results -/

/-- Erdős–Gyárfás lower bound for `k = 3`: `R(n;3,r) > C^{√n}` for some `C > 1`.
That is, for large `n`, no `N < C^{√n}` satisfies `HasRamseyAvoid N n 3 r`. -/
axiom erdos_gyarfas_lower_bound (r : ℕ) (hr : 2 ≤ r) :
    ∃ (C : ℝ), 1 < C ∧ ∀ᶠ n in Filter.atTop,
      ∀ N : ℕ, (N : ℝ) < C ^ Real.sqrt n → ¬HasRamseyAvoid N n 3 r

/-! ## Basic properties -/

/-- Monotonicity: if `HasRamseyAvoid N n k r`, then `HasRamseyAvoid M n k r`
for any `M ≥ N`. More vertices only makes it easier to find a large independent set. -/
axiom hasRamseyAvoid_mono (N M n k r : ℕ) (h : N ≤ M) :
    HasRamseyAvoid N n k r → HasRamseyAvoid M n k r

/-- With more colors, avoiding monochromatic cliques is easier. -/
axiom hasRamseyAvoid_more_colors (N n k r₁ r₂ : ℕ) (h : r₁ ≤ r₂) :
    HasRamseyAvoid N n k r₁ → HasRamseyAvoid N n k r₂

/-- For `k ≤ 2` and `n ≤ N`, the property holds vacuously since no edge
forms a monochromatic `K_k` when `k ≤ 2`. -/
axiom hasRamseyAvoid_small_k (N n k r : ℕ) (hk : k ≤ 2) (hn : n ≤ N) (hr : 0 < r) :
    HasRamseyAvoid N n k r

/-- The singleton case: any graph has a 1-vertex set avoiding mono `K_3`. -/
axiom hasRamseyAvoid_one (N r : ℕ) (hN : 1 ≤ N) (hr : 0 < r) :
    HasRamseyAvoid N 1 3 r

/-- The `n = 0` case is trivially satisfiable. -/
axiom hasRamseyAvoid_zero (N k r : ℕ) (hr : 0 < r) :
    HasRamseyAvoid N 0 k r
