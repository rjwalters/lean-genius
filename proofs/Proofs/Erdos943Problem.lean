/-
# Erdős Problem #943 — Representation by Sums of Two Powerful Numbers

A powerful number is n such that if p | n then p² | n. Let A be the
set of powerful numbers. Define r(n) = |{(a,b) : a,b ∈ A, a+b = n}|,
the number of representations of n as a sum of two powerful numbers.

Question: Is r(n) = n^{o(1)} for every n? Equivalently, does the
Dirichlet-style convolution 1_A ∗ 1_A(n) grow subpolynomially?

This asks whether every integer has at most subpolynomially many
representations as a sum of two powerful numbers.

Status: OPEN
Reference: https://erdosproblems.com/943
Source: [Er76d]
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/- ## Definitions -/

/-- A natural number is powerful if every prime dividing it
    appears with exponent ≥ 2. Equivalently, n = a²b³ for
    some a, b. -/
def IsPowerful (n : ℕ) : Prop :=
  n ≥ 1 ∧ ∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n

/-- The set of powerful numbers. -/
def PowerfulSet : Set ℕ := {n : ℕ | IsPowerful n}

/-- r(n): the number of representations of n as a sum of two
    powerful numbers. -/
noncomputable def powerfulSumRep (n : ℕ) : ℕ :=
  Finset.card (Finset.filter
    (fun a => IsPowerful a ∧ IsPowerful (n - a) ∧ a ≤ n)
    (Finset.range (n + 1)))

/- ## Part I: Basic Properties of Powerful Numbers -/

/-- 0 is not powerful (requires n ≥ 1). -/
theorem not_isPowerful_zero : ¬IsPowerful 0 := by
  intro ⟨h, _⟩; omega

/-- 1 is powerful: no primes divide 1, so the condition is vacuous. -/
theorem isPowerful_one : IsPowerful 1 :=
  ⟨le_refl 1, fun p hp hpd => absurd (Nat.le_of_dvd (by omega) hpd) (by omega)⟩

/-- p² is powerful for any prime p: the only prime dividing p² is p itself. -/
theorem isPowerful_prime_sq {p : ℕ} (hp : Nat.Prime p) : IsPowerful (p ^ 2) :=
  ⟨by positivity, fun q hq hqd => by
    have hqp : q ∣ p := hq.dvd_of_dvd_pow hqd
    have heq : q = p := by
      rcases hp.eq_one_or_self_of_dvd q hqp with h | h
      · exact absurd h hq.ne_one
      · exact h
    rw [heq]⟩

/-- Perfect squares ≥ 1 are powerful: if p | n² then p | n, so p² | n². -/
theorem isPowerful_sq {n : ℕ} (hn : n ≥ 1) : IsPowerful (n ^ 2) :=
  ⟨by positivity, fun p hp hpd => by
    have := hp.dvd_of_dvd_pow hpd
    exact Dvd.dvd.pow this (by omega : 0 < 2)⟩

/-- Products of powerful numbers are powerful. -/
theorem isPowerful_mul {m n : ℕ} (hm : IsPowerful m) (hn : IsPowerful n) :
    IsPowerful (m * n) :=
  ⟨by omega, fun p hp hpd => by
    have := hp.dvd_mul.mp hpd
    rcases this with h | h
    · exact dvd_mul_of_dvd_left (hm.2 p hp h) n
    · exact dvd_mul_of_dvd_right (hn.2 p hp h) m⟩

/- ## Part II: Main Question -/

/-- **Erdős Problem #943**: Is r(n) = n^{o(1)}? That is, for every
    ε > 0, is r(n) < n^ε for all sufficiently large n? -/
/- ## Part III: Known Results -/

/-- **Powerful number density**: The number of powerful numbers
    up to x is asymptotically c·√x where c = ζ(3/2)/ζ(3).
    This gives about √x potential summands for each n. -/
axiom powerful_density :
  ∃ c : ℝ, c > 0 ∧ ∀ x : ℕ, x ≥ 1 →
    (Finset.card (Finset.filter IsPowerful (Finset.range (x + 1))) : ℝ) ≤
      c * (x : ℝ) ^ ((1 : ℝ) / 2)

/-- **Trivial upper bound (PROVED from powerful_density)**:
    r(n) ≤ |A ∩ [0,n]| ≤ c·√n.

    Proof: r(n) counts pairs (a, n-a) with a powerful and n-a powerful,
    which is at most the count of powerful numbers in [0,n]. -/
theorem trivial_upper_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ n : ℕ, n ≥ 1 →
      (powerfulSumRep n : ℝ) ≤ c * (n : ℝ) ^ ((1 : ℝ) / 2) := by
  obtain ⟨c, hc, hbound⟩ := powerful_density
  exact ⟨c, hc, fun n hn => by
    -- powerfulSumRep n ≤ card(filter IsPowerful (range (n+1)))
    have hle : powerfulSumRep n ≤
        (Finset.filter IsPowerful (Finset.range (n + 1))).card := by
      unfold powerfulSumRep
      apply Finset.card_le_card
      intro a
      simp only [Finset.mem_filter, Finset.mem_range]
      exact fun ⟨h1, h2, _, _⟩ => ⟨h1, h2⟩
    -- Combine with density bound
    calc (powerfulSumRep n : ℝ)
        ≤ ((Finset.filter IsPowerful (Finset.range (n + 1))).card : ℝ) := by
          exact_mod_cast hle
      _ ≤ c * (n : ℝ) ^ (1 / 2) := hbound n hn⟩

/-- **Powerful number structure**: Every powerful number can be
    written as a²b³ for some a, b ≥ 1. The special structure
    constrains which pairs can sum to n. -/
/- ## Part IV: Observations -/

/- **Average order**: On average over n ≤ x, the sum
    Σ_{n≤x} r(n) ∼ c²x (since there are ~c√x powerful numbers
    up to x). The question is about pointwise bounds. -/

/- **Connection to squares**: Perfect squares form a subset of
    powerful numbers. Representations as sums of two squares
    are well-understood (Jacobi's formula), but the powerful
    number case is harder due to the irregular structure. -/

/- **Diophantine constraints**: For n = a²b³ + c²d³, the
    equation constrains a,b,c,d in ways that should limit
    the number of solutions, but making this rigorous is
    the core difficulty. -/
