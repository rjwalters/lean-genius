/-!
# Erdős Problem 49: Sets with Increasing Euler Totient Values

Let `A = {a₁ < ⋯ < aₜ} ⊆ {1,…,N}` with `φ(a₁) < ⋯ < φ(aₜ)`.
The primes form such a set. Are they the largest possible?

**Conjecture:** `|A| ≤ (1 + o(1)) π(N)`.

**Solved** by Tao (2023): `|A| ≤ (1 + O((log log x)⁵ / log x)) π(x)`.

*Reference:* [erdosproblems.com/49](https://www.erdosproblems.com/49)
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! ## Increasing totient sets -/

/-- A set `A ⊆ {1,…,N}` has strictly increasing Euler totient values
if for all `a, b ∈ A` with `a < b`, we have `φ(a) < φ(b)`. -/
def IsIncreasingTotientSet (A : Finset ℕ) : Prop :=
    ∀ a ∈ A, ∀ b ∈ A, a < b → Nat.totient a < Nat.totient b

/-- The maximum size of an increasing totient set in `{1,…,N}`. -/
noncomputable def maxIncTotientSize (N : ℕ) : ℕ :=
    Finset.sup
      ((Finset.Icc 1 N).powerset.filter IsIncreasingTotientSet)
      Finset.card

/-! ## Prime counting function -/

/-- The prime counting function `π(N)`: number of primes up to `N`. -/
noncomputable def primeCounting (N : ℕ) : ℕ :=
    ((Finset.Icc 1 N).filter Nat.Prime).card

/-! ## Primes form an increasing totient set -/

/-- The set of primes in `{1,…,N}` has strictly increasing totient
values since `φ(p) = p - 1` for primes. -/
axiom primes_increasing_totient (N : ℕ) :
    IsIncreasingTotientSet ((Finset.Icc 1 N).filter Nat.Prime)

/-- Consequently, `maxIncTotientSize(N) ≥ π(N)`. -/
axiom maxIncTotientSize_ge_primeCounting (N : ℕ) :
    primeCounting N ≤ maxIncTotientSize N

/-! ## Tao's theorem (2023) -/

/-- Tao (2023): For all `ε > 0` and sufficiently large `N`,
`maxIncTotientSize(N) ≤ (1 + ε) · π(N)`.

This proves the primes are asymptotically the largest increasing
totient set. -/
axiom tao_increasing_totient :
    ∀ (ε : ℚ), 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (maxIncTotientSize N : ℚ) ≤ (1 + ε) * (primeCounting N : ℚ)

/-! ## Main statement -/

/-- Erdős Problem 49 (solved): The maximum size of an increasing totient
set in `{1,…,N}` is asymptotically `π(N)`. -/
def ErdosProblem49 : Prop :=
    ∀ (ε : ℚ), 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (maxIncTotientSize N : ℚ) ≤ (1 + ε) * (primeCounting N : ℚ)

/-! ## Weaker form -/

/-- The weaker conjecture `|A| = o(N)`: any increasing totient set has
density zero. This follows from Tao's result since `π(N) = o(N)`. -/
axiom incTotientSet_density_zero :
    ∀ (ε : ℚ), 0 < ε →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (maxIncTotientSize N : ℚ) ≤ ε * (N : ℚ)

/-! ## Totient properties -/

/-- `φ(p) = p - 1` for primes. -/
axiom totient_prime (p : ℕ) (hp : Nat.Prime p) :
    Nat.totient p = p - 1

/-- `φ(n) ≤ n` for all `n`. -/
axiom totient_le (n : ℕ) : Nat.totient n ≤ n
