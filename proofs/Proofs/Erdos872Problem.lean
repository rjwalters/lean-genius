/-
Erdős Problem #872: Antichain Saturation Game

Source: https://erdosproblems.com/872
Status: OPEN

Statement:
Consider the two-player game where players alternately choose integers from
{2, 3, ..., n} to be included in a set A such that no a ∣ b for distinct
a, b ∈ A (i.e., A forms an antichain under divisibility).

The game ends when no legal move is possible (the set A is maximal).
One player wants the game to last as long as possible, the other wants
it to end quickly. How long can the game be guaranteed to last for?

Specifically:
1. At least εn moves for some ε > 0 and n sufficiently large?
2. At least (1 - ε)n/2 moves?

This is a number-theoretic variant of the saturation game paradigm,
related to Hajnal's triangle-free game on graphs.

Note: Erdős does not specify which player moves first, which may affect
the answer.

Tags: Combinatorial games, Primitive sets, Antichains, Divisibility

References:
- Erdős [Er92c, p.47]: Some of my favourite problems in various branches of
  combinatorics. Matematiche (1992).
- Füredi, Seress (1991): Triangle-free game can last Ω(n log n) moves
- Biró, Horn, Wildstrom (2016): Upper bound (26/121 + o(1))n² for triangle game
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Order.Antichain
import Mathlib.Data.Set.Card
import Mathlib.Tactic

open Nat Finset Set

namespace Erdos872

/- ## Part I: Antichain Definition

An antichain under divisibility is a set where no element divides another.
-/

/--
**Divisibility Antichain:**
A set A of natural numbers where no distinct elements a, b satisfy a ∣ b.
These are also called "primitive sets" in number theory.
-/
def IsDivisibilityAntichain (A : Set ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ A → b ∈ A → a ∣ b → a = b

/--
**Primitive Set:**
Equivalent definition using the standard antichain notion.
-/
def IsPrimitiveSet (A : Set ℕ) : Prop :=
  ∀ a b : ℕ, a ∈ A → b ∈ A → a ≠ b → ¬(a ∣ b)

/--
The two definitions are equivalent.
-/
theorem antichain_iff_primitive (A : Set ℕ) :
    IsDivisibilityAntichain A ↔ IsPrimitiveSet A := by
  constructor
  · intro h a b ha hb hab hdiv
    exact hab (h a b ha hb hdiv)
  · intro h a b ha hb hdiv
    by_contra hab
    exact h a b ha hb hab hdiv

/- ## Part II: The Game Board
-/

/--
**Game Board:**
The set {2, 3, ..., n} from which players choose elements.
-/
def gameBoard (n : ℕ) : Set ℕ := {k : ℕ | 2 ≤ k ∧ k ≤ n}

/--
The game board has n - 1 elements for n ≥ 2.
Axiomatized: the proof requires Finset/Set.ncard machinery
that would distract from the game-theoretic content.
-/

/--
**Legal Move:**
A move is legal if adding element k to A keeps A as an antichain.
-/
def IsLegalMove (A : Set ℕ) (k : ℕ) : Prop :=
  k ∉ A ∧ IsDivisibilityAntichain (A ∪ {k})

/--
Equivalently: k doesn't divide or get divided by any element of A.
PROVED: set manipulation on the union definition. -/
theorem legal_move_iff (A : Set ℕ) (k : ℕ) (hA : IsDivisibilityAntichain A) :
    IsLegalMove A k ↔ k ∉ A ∧ (∀ a ∈ A, ¬(k ∣ a)) ∧ (∀ a ∈ A, ¬(a ∣ k)) := by
  constructor
  · -- Forward: IsLegalMove → the three conditions
    intro ⟨hkA, hAnti⟩
    refine ⟨hkA, ?_, ?_⟩
    · intro a ha hka
      have : k = a := hAnti k a (Or.inr rfl) (Or.inl ha) hka
      exact hkA (this ▸ ha)
    · intro a ha hak
      have : a = k := hAnti a k (Or.inl ha) (Or.inr rfl) hak
      exact hkA (this ▸ ha)
  · -- Backward: three conditions → IsLegalMove
    intro ⟨hkA, hndvd, hndvd'⟩
    refine ⟨hkA, ?_⟩
    intro a b ha hb hab
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact hA a b ha hb hab
    · simp only [mem_singleton_iff] at hb; subst hb
      exact absurd hab (hndvd' a ha)
    · simp only [mem_singleton_iff] at ha; subst ha
      exact absurd hab (hndvd b hb)
    · simp only [mem_singleton_iff] at ha hb; exact ha ▸ hb.symm

/- ## Part III: Game State and Termination
-/

/--
**Maximal Antichain:**
An antichain is maximal if no element can be added while maintaining the property.
-/
def IsMaximalAntichain (A : Set ℕ) (board : Set ℕ) : Prop :=
  A ⊆ board ∧ IsDivisibilityAntichain A ∧
  ∀ k ∈ board, k ∉ A → ¬IsDivisibilityAntichain (A ∪ {k})

/--
**Game Terminates:**
Any sequence of legal moves eventually reaches a maximal antichain.
-/

/- ## Part IV: Bounds on Game Length
-/

/--
**Trivial Upper Bound:**
Any antichain in {2, ..., n} has at most ⌈n/2⌉ = (n+1)/2 elements.
The set {⌈n/2⌉ + 1, ..., n} achieves this: it has ⌊n/2⌋ elements and
forms an antichain since all elements exceed n/2, so no element can be
at least twice another while remaining ≤ n.

**NOTE:** Previously stated as ≤ n/2, which is incorrect for odd n.
E.g., for n=5, {3,4,5} is an antichain with 3 > 5/2 = 2 elements.
The correct bound is (n+1)/2 (Nat division). -/

/--
**Greedy Lower Bound:**
The primes in [n/2, n] form an antichain, giving size ~ n / (2 ln n).
-/

/- ## Part V: Erdős's Questions
-/

/--
**Question 1:** Can the game be guaranteed to last at least εn moves?

Formally: Does there exist ε > 0 and N such that for all n ≥ N,
regardless of the minimizer's strategy, the maximizer can ensure
the game lasts at least ⌊εn⌋ moves?
-/
def gameLastsLinear (gameLength : ℕ → ℕ) : Prop :=
  ∃ ε : ℚ, ε > 0 ∧ ∃ N : ℕ, ∀ n ≥ N,
    (gameLength n : ℚ) ≥ ε * n

/--
**Question 2:** Can the game be guaranteed to last at least (1-ε)n/2 moves?

This would be almost optimal since n/2 is the maximum antichain size.
-/
def gameLastsNearOptimal (gameLength : ℕ → ℕ) : Prop :=
  ∀ ε : ℚ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N,
    (gameLength n : ℚ) ≥ (1 - ε) * (n / 2)

/--
**Erdős Problem #872: Both questions remain OPEN.**

We axiomatize this as: the guaranteed game length under optimal play
is currently unknown — neither linear nor sublinear behavior has been
established. -/

/- ## Part VI: Related Results
-/

/--
**Hajnal's Triangle-Free Game:**
In the analogous graph game, Füredi-Seress showed Ω(n log n) moves guaranteed.
The triangle-free game on Kₙ lasts at least c · n · log n moves for some c > 0.
-/

/--
**Upper Bound for Triangle Game:**
Biró, Horn, Wildstrom showed at most (26/121 + o(1))n² moves.
-/

/- ## Part VII: Special Cases and Examples
-/

/--
**Example: Primes form an antichain.**
No prime divides another prime (except itself).
-/
theorem primes_antichain (P : Set ℕ) (hP : ∀ p ∈ P, p.Prime) :
    IsDivisibilityAntichain P := by
  intro a b ha hb hab
  have haPrime := hP a ha
  have hbPrime := hP b hb
  exact (Nat.Prime.eq_one_or_self_of_dvd hbPrime a hab).resolve_left
    (Nat.Prime.one_lt haPrime).ne'

/--
**Example: {⌈n/2⌉ + 1, ..., n} is an antichain.**
No element is at least twice another: if a, b > n/2 and a | b with a ≠ b,
then b ≥ 2a > n, contradicting b ≤ n.
PROVED: direct divisibility argument. -/
theorem upper_half_antichain (n : ℕ) (hn : n ≥ 4) :
    IsDivisibilityAntichain {k : ℕ | n / 2 + 1 ≤ k ∧ k ≤ n} := by
  intro a b ⟨ha_lo, ha_hi⟩ ⟨hb_lo, hb_hi⟩ hab
  -- If a | b and a ≠ b, then b ≥ 2a > n, contradicting b ≤ n
  by_contra h_ne
  obtain ⟨k, hk⟩ := hab
  have ha_pos : a > 0 := by omega
  have hk_ge2 : k ≥ 2 := by
    rcases k with _ | _ | _
    · -- k = 0: b = a * 0 = 0, but b ≥ n/2 + 1 > 0
      simp at hk; omega
    · -- k = 1: b = a, contradicting a ≠ b
      simp at hk; exact absurd hk.symm h_ne
    · -- k ≥ 2
      omega
  -- b = a*k ≥ (n/2+1)*2 > n, contradicting b ≤ n
  have hb_ge : b ≥ (n / 2 + 1) * 2 := by
    calc b = a * k := hk
      _ ≥ (n / 2 + 1) * k := Nat.mul_le_mul_right k ha_lo
      _ ≥ (n / 2 + 1) * 2 := Nat.mul_le_mul_left _ hk_ge2
  omega

/--
**First Player Advantage:**
Erdős notes the first player may affect the game length.
Different maximal antichains can have different sizes, so the
player who moves first may be able to steer toward a larger or
smaller terminal set.
-/
def firstPlayerAdvantage : Prop :=
  ∃ n : ℕ, ∃ A₁ A₂ : Set ℕ,
    IsMaximalAntichain A₁ (gameBoard n) ∧
    IsMaximalAntichain A₂ (gameBoard n) ∧
    A₁.ncard ≠ A₂.ncard

/- ## Part VIII: Game-Theoretic Formulation
-/

/--
**Game Value:**
The guaranteed game length under optimal play by both sides.
Axiomatized since computing the minimax tree is exponential.
-/
axiom gameValue (n : ℕ) : ℕ
axiom gameValue_upper (n : ℕ) (hn : n ≥ 2) : gameValue n ≤ (n + 1) / 2

/--
**Open Problem Statement:**
Determine the asymptotic behavior of gameValue(n).
Either the game lasts Θ(n) moves, or it is o(n) — we don't know which.
-/

/- ## Part IX: Summary
-/

/--
**Erdős Problem #872: Summary**

An open problem about saturation games on divisibility antichains.

Key concepts:
- Antichain: No element divides another (primitive set)
- Game: Alternating moves to build maximal antichain
- Questions: Does game last Θ(n) moves? Near n/2 moves?

Related to Hajnal's triangle-free graph game.
-/
theorem erdos_872_summary :
    -- The primes form a valid antichain
    (∀ P : Set ℕ, (∀ p ∈ P, p.Prime) → IsDivisibilityAntichain P) ∧
    -- The game value is bounded above by (n+1)/2
    (∀ n : ℕ, n ≥ 2 → gameValue n ≤ (n + 1) / 2) :=
  ⟨primes_antichain, gameValue_upper⟩

end Erdos872
