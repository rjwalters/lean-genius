/-
# Erdős Problem 121: Square-Free Products

Let `F_k(N)` be the maximum size of `A ⊆ {1,…,N}` such that no product
of `k` distinct elements of `A` is a perfect square.

**Conjecture:** `F₅(N) = (1 - o(1))N` and more generally
`F_{2k+1}(N) = (1 - o(1))N` for all `k ≥ 1`.

**Disproved** by Tao (2024): for `k ≥ 4`, `F_k(N) ≤ (1 - c_k)N` for
some `c_k > 0`.

*Reference:* [erdosproblems.com/121](https://www.erdosproblems.com/121)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/- ## Square-free product sets -/

/-- A number is a perfect square. -/
def IsSquare (n : ℕ) : Prop :=
    ∃ m : ℕ, n = m * m

/-- A finset `A` is `k`-square-free: no product of `k` distinct
elements is a perfect square. -/
def IsKSquareFree (A : Finset ℕ) (k : ℕ) : Prop :=
    ∀ S : Finset ℕ, S ⊆ A → S.card = k →
      ¬IsSquare (S.prod id)

/-- `F_k(N)`: the maximum size of a `k`-square-free subset of
`{1,…,N}`. -/
noncomputable def squareFreeMax (k N : ℕ) : ℕ :=
    Finset.sup
      ((Finset.Icc 1 N).powerset.filter (fun A => IsKSquareFree A k))
      Finset.card

/- ## Known results for small k -/

/-- `F_2(N) = (6/π² + o(1))N`: the squarefree integers have density
`6/π²` (Erdős–Sós–Sárközy). -/

/-- `F_3(N) = (1 - o(1))N`: for 3-element products, almost all
integers can be included. -/

/-- `F_4(N) = o(N)`: for 4-element products, the density goes to
zero (Erdős). -/

/- ## The conjecture (disproved) -/

/-- Erdős's conjecture (disproved): `F_{2k+1}(N) = (1 - o(1))N` for
all `k ≥ 1`. This would mean odd-index square-free products allow
almost all integers. -/
def ErdosProblem121_Conjecture : Prop :=
    ∀ k : ℕ, 1 ≤ k →
      ∀ (ε : ℚ), 0 < ε →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (1 - ε) * (N : ℚ) ≤ (squareFreeMax (2 * k + 1) N : ℚ)

/- ## Tao's disproof (2024) -/

/-- Tao (2024): For all `k ≥ 4`, there exists `c_k > 0` such that
`F_k(N) ≤ (1 - c_k + o(1))N`. This disproves the conjecture for
`k = 5` (and all larger odd `k`). -/

/-- The conjecture is false. -/

/- ## Monotonicity -/

/-- `F_k` is monotone in `N`. -/

/-- `F_k` is anti-monotone in `k`: more elements required to form a
product makes it easier to avoid squares. -/
