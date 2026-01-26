/-!
# Erdős Problem 201: Arithmetic Progressions in Integer Sets

Let `G_k(N)` denote the minimum size of a subset guaranteed to exist
in any set of `N` integers that avoids `k`-term arithmetic progressions.
Let `R_k(N)` be the maximum size of a subset of `{1,…,N}` without
`k`-term arithmetic progressions.

**Questions:**
1. Determine `G_k(N)`.
2. Is it true that `lim_{N→∞} R₃(N) / G₃(N) = 1`?

Komlós–Sulyok–Szemerédi (1975) proved `R_k(N) ≪_k G_k(N)`.
First investigated by Riddell (1969).

*Reference:* [erdosproblems.com/201](https://www.erdosproblems.com/201)
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

/-! ## Arithmetic progressions -/

/-- A list of integers forms a `k`-term arithmetic progression. -/
def IsArithProg (s : List ℤ) : Prop :=
    s.length ≥ 2 ∧ ∃ d : ℤ, ∀ i : Fin s.length,
      i.val + 1 < s.length →
        s.get ⟨i.val + 1, by omega⟩ = s.get i + d

/-- A set `A` of integers contains a `k`-term arithmetic progression. -/
def ContainsAPOfLength (A : Finset ℤ) (k : ℕ) : Prop :=
    ∃ (a d : ℤ), d ≠ 0 ∧ k ≥ 1 ∧
      ∀ i : Fin k, a + (i.val : ℤ) * d ∈ A

/-- A set `A` is `k`-AP-free: it contains no `k`-term arithmetic
progression. -/
def IsAPFree (A : Finset ℤ) (k : ℕ) : Prop :=
    ¬ContainsAPOfLength A k

/-! ## The functions G_k and R_k -/

/-- `R_k(N)`: the maximum size of a `k`-AP-free subset of `{1,…,N}`. -/
noncomputable def rk (k N : ℕ) : ℕ :=
    Finset.sup
      ((Finset.Icc (1 : ℤ) N).powerset.filter (fun A => IsAPFree A k))
      Finset.card

/-- `G_k(N)`: the minimum size of a `k`-AP-free subset guaranteed in any
set of `N` integers. Formally, the maximum over all `N`-element integer
sets of the largest `k`-AP-free subset. -/
axiom gk : ℕ → ℕ → ℕ

/-! ## Basic bounds -/

/-- Trivial bound: `G_k(N) ≤ R_k(N)`. Any `N`-element integer set can
be embedded into `{1,…,M}` for some `M`, so the worst-case `k`-AP-free
subset is at most the Szemerédi bound. -/
axiom gk_le_rk (k N : ℕ) (hk : 3 ≤ k) : gk k N ≤ rk k N

/-- Strict inequality example: `G_3(5) = 3` while `R_3(5) = 4`. -/
axiom g3_5_eq : gk 3 5 = 3
axiom r3_5_eq : rk 3 5 = 4

/-- `G_3(14) ≤ 7` while `R_3(14) = 8`. -/
axiom g3_14_le : gk 3 14 ≤ 7
axiom r3_14_eq : rk 3 14 = 8

/-! ## Komlós–Sulyok–Szemerédi bound -/

/-- Komlós, Sulyok, Szemerédi (1975): `R_k(N)` and `G_k(N)` have the
same order of magnitude, i.e., `R_k(N) ≪_k G_k(N)`. -/
axiom komlos_sulyok_szemeredi (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, 0 < C ∧ ∀ N : ℕ, rk k N ≤ C * gk k N

/-! ## Main conjecture -/

/-- Erdős Problem 201: Is the ratio `R_3(N) / G_3(N)` asymptotically 1?

Formally: for every `ε > 0`, there exists `N₀` such that for all
`N ≥ N₀`, `R_3(N) ≤ (1 + ε) * G_3(N)`. -/
def ErdosProblem201 : Prop :=
    ∀ (ε : ℚ), 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (rk 3 N : ℚ) ≤ (1 + ε) * (gk 3 N : ℚ)

/-! ## Monotonicity -/

/-- `R_k` is monotone in `N`: adding elements to the ground set cannot
decrease the maximum AP-free subset size. -/
axiom rk_mono (k : ℕ) (M N : ℕ) (h : M ≤ N) : rk k M ≤ rk k N

/-- For `k ≤ l`, being `l`-AP-free implies `k`-AP-free, so
`R_k(N) ≥ R_l(N)`. -/
axiom rk_anti_k (k l N : ℕ) (h : k ≤ l) : rk l N ≤ rk k N
