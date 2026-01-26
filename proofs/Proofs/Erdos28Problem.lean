/-!
# Erdős Problem #28 — The Erdős–Turán Conjecture on Additive Bases

If A ⊆ ℕ is an additive basis of order 2 (i.e., A + A contains all but
finitely many natural numbers), then the representation function
r(n) = |{(a,b) ∈ A × A : a + b = n}| satisfies lim sup r(n) = ∞.

**Status: OPEN.** $500 bounty.

Conjectured by Erdős and Turán (1941). One of the most famous open
problems in additive combinatorics.

Stronger conjectures:
- lim sup r(n)/log n > 0
- The conclusion holds if |A ∩ [1,N]| ≫ √N for all large N

Reference: https://erdosproblems.com/28
-/

import Mathlib.Combinatorics.Additive.SumConv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Order.Filter.ENNReal
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

open Filter Set
open scoped Pointwise

/-! ## Core Definitions -/

/-- The representation function: number of ways to write n as a + b
    with a, b ∈ A and a ≤ b. -/
def repFunction (A : Set ℕ) (n : ℕ) : ℕ :=
  (Finset.Icc 0 n).filter (fun a => a ∈ A ∧ (n - a) ∈ A ∧ a ≤ n - a) |>.card

/-- A is an asymptotic additive basis of order 2: A + A contains
    all sufficiently large natural numbers. -/
def IsAsymptoticBasis2 (A : Set ℕ) : Prop :=
  (A + A)ᶜ.Finite

/-- The counting function: |A ∩ [1, N]|. -/
def countingFn (A : Set ℕ) (N : ℕ) : ℕ :=
  (Finset.Icc 1 N).filter (· ∈ A) |>.card

/-! ## The Main Conjecture -/

/-- **Erdős–Turán Conjecture (1941)**: If A + A covers all but finitely
    many naturals, then the representation function is unbounded.
    Equivalently: no asymptotic basis of order 2 can have bounded
    representations.

    This is Problem #28. $500 bounty. -/
axiom erdos_turan_conjecture (A : Set ℕ) (h : IsAsymptoticBasis2 A) :
    ∀ B : ℕ, ∃ n : ℕ, B ≤ repFunction A n

/-! ## Stronger Forms -/

/-- Stronger conjecture: lim sup r(n) / log n > 0.
    This would mean r(n) ≥ c log n infinitely often. -/
axiom erdos_turan_strong (A : Set ℕ) (h : IsAsymptoticBasis2 A) :
    ∃ c > 0, ∀ N : ℕ, ∃ n ≥ N, (repFunction A n : ℝ) ≥ c * Real.log n

/-- Alternative strengthening: the conclusion holds under the weaker
    hypothesis |A ∩ [1,N]| ≫ √N. This encompasses all bases of order 2. -/
axiom erdos_turan_density_version :
    ∀ A : Set ℕ,
    (∃ c > 0, ∀ N : ℕ, 1 ≤ N → (countingFn A N : ℝ) ≥ c * Real.sqrt N) →
    ∀ B : ℕ, ∃ n : ℕ, B ≤ repFunction A n

/-! ## Known Results -/

/-- A basis of order 2 must have |A ∩ [1,N]| ≫ √N.
    (Necessary condition from counting.) -/
axiom basis_counting_lower (A : Set ℕ) (h : IsAsymptoticBasis2 A) :
    ∃ c > 0, ∀ N : ℕ, 1 ≤ N → (countingFn A N : ℝ) ≥ c * Real.sqrt N

/-- If A is a Sidon set (B₂ sequence), then A + A has density 0,
    so A cannot be a basis of order 2. Sidon sets have r(n) ≤ 1,
    confirming the conjecture vacuously for this extremal case. -/
axiom sidon_not_basis (A : Set ℕ) :
    (∀ n, repFunction A n ≤ 1) →
    ¬ IsAsymptoticBasis2 A

/-! ## Connection to Problem #40 -/

/-- Problem #40 (also Erdős–Turán): If A is a B₂[g] set
    (r(n) ≤ g for all n), then A cannot be a basis of order 2.
    This is implied by Problem #28. -/
axiom erdos_40_from_28 (g : ℕ) (A : Set ℕ) :
    (∀ n, repFunction A n ≤ g) →
    ¬ IsAsymptoticBasis2 A

/-! ## Partial Results -/

/-- Erdős and Fuchs (1956): If A is any set, then
    Σ_{n≤N} r(n) cannot be cN + o(N^{1/4} / (log N)^{1/2}).
    This means the average of r(n) fluctuates from its mean. -/
axiom erdos_fuchs_theorem (A : Set ℕ) (h : IsAsymptoticBasis2 A) :
    ¬∃ c > 0, ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀,
      |(Finset.range (N + 1)).sum (fun n => (repFunction A n : ℤ)) - (c * N : ℤ)| ≤
        ε * (N : ℝ) ^ (1/4 : ℝ)

/-- Halberstam and Roth: basic counting shows that for a basis of order 2,
    the average representation is Σ r(n≤N) / N → ∞ as N → ∞.
    But this does NOT prove lim sup r(n) = ∞ (the average could be
    dominated by rare large values). -/
axiom average_rep_unbounded (A : Set ℕ) (h : IsAsymptoticBasis2 A) :
    Tendsto (fun N => (Finset.range (N + 1)).sum (fun n => repFunction A n) / (N + 1))
      atTop atTop
