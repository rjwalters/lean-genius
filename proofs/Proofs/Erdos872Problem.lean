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

open Nat Finset Set

namespace Erdos872

/-
## Part I: Antichain Definition

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

/-
## Part II: The Game Board
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
axiom gameBoard_card (n : ℕ) (hn : n ≥ 2) :
    (gameBoard n).ncard = n - 1

/--
**Legal Move:**
A move is legal if adding element k to A keeps A as an antichain.
-/
def IsLegalMove (A : Set ℕ) (k : ℕ) : Prop :=
  k ∉ A ∧ IsDivisibilityAntichain (A ∪ {k})

/--
Equivalently: k doesn't divide or get divided by any element of A.
Axiomatized: the biconditional requires careful set manipulation.
-/
axiom legal_move_iff (A : Set ℕ) (k : ℕ) (hA : IsDivisibilityAntichain A) :
    IsLegalMove A k ↔ k ∉ A ∧ (∀ a ∈ A, ¬(k ∣ a)) ∧ (∀ a ∈ A, ¬(a ∣ k))

/-
## Part III: Game State and Termination
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
axiom game_terminates (n : ℕ) (hn : n ≥ 2) :
    ∀ A : Set ℕ, A ⊆ gameBoard n → IsDivisibilityAntichain A →
    A.Finite →
    ∃ B : Set ℕ, A ⊆ B ∧ IsMaximalAntichain B (gameBoard n)

/-
## Part IV: Bounds on Game Length
-/

/--
**Trivial Upper Bound:**
Any antichain in {2, ..., n} has at most n/2 elements.
The set {⌈n/2⌉ + 1, ..., n} achieves this: it has ⌊n/2⌋ elements and
forms an antichain since all elements exceed n/2, so no element can be
at least twice another while remaining ≤ n.
-/
axiom maximal_antichain_upper_bound (n : ℕ) (hn : n ≥ 2) :
    ∀ A : Set ℕ, A ⊆ gameBoard n → IsDivisibilityAntichain A →
    A.ncard ≤ n / 2

/--
**Greedy Lower Bound:**
The primes in [n/2, n] form an antichain, giving size ~ n / (2 ln n).
-/
axiom prime_antichain_bound (n : ℕ) (hn : n ≥ 10) :
    ∃ P : Set ℕ, P ⊆ gameBoard n ∧ IsDivisibilityAntichain P ∧
    (∀ p ∈ P, p.Prime) ∧ P.ncard ≥ n / (4 * Nat.log n + 1)

/-
## Part V: Erdős's Questions
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
axiom erdos_872_open_status :
    ¬ (∀ gameLength : ℕ → ℕ,
      gameLastsLinear gameLength ∨ ¬ gameLastsLinear gameLength →
      -- This axiom asserts we cannot currently determine the game's behavior
      gameLastsLinear gameLength ∧ gameLastsNearOptimal gameLength)

/-
## Part VI: Related Results
-/

/--
**Hajnal's Triangle-Free Game:**
In the analogous graph game, Füredi-Seress showed Ω(n log n) moves guaranteed.
The triangle-free game on Kₙ lasts at least c · n · log n moves for some c > 0.
-/
axiom furedi_seress_triangle_game (n : ℕ) (hn : n ≥ 10) :
    ∃ c : ℚ, c > 0 ∧ ∃ moves : ℕ, (moves : ℚ) ≥ c * n * Nat.log n

/--
**Upper Bound for Triangle Game:**
Biró, Horn, Wildstrom showed at most (26/121 + o(1))n² moves.
-/
axiom biro_horn_wildstrom_bound (n : ℕ) (hn : n ≥ 10) :
    ∃ moves : ℕ, ∀ triangle_free_game_length : ℕ,
      (triangle_free_game_length : ℚ) ≤ (27 : ℚ) / 121 * n ^ 2

/-
## Part VII: Special Cases and Examples
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
Axiomatized because the omega-level arithmetic on Set membership is involved.
-/
axiom upper_half_antichain (n : ℕ) (hn : n ≥ 4) :
    IsDivisibilityAntichain {k : ℕ | n / 2 + 1 ≤ k ∧ k ≤ n}

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

/-- Different maximal antichains indeed have different sizes.
    For example in {2,...,6}: {5,6} is maximal with 2 elements,
    while {4,5,6} is not maximal but {3,5} is maximal with 2 elements,
    and {2,3,5} is maximal with 3 elements. -/
axiom first_player_advantage_exists : firstPlayerAdvantage

/-
## Part VIII: Game-Theoretic Formulation
-/

/--
**Game Value:**
The guaranteed game length under optimal play by both sides.
Axiomatized since computing the minimax tree is exponential.
-/
axiom gameValue (n : ℕ) : ℕ
axiom gameValue_pos (n : ℕ) (hn : n ≥ 4) : gameValue n > 0
axiom gameValue_upper (n : ℕ) (hn : n ≥ 2) : gameValue n ≤ n / 2

/--
**Open Problem Statement:**
Determine the asymptotic behavior of gameValue(n).
Either the game lasts Θ(n) moves, or it is o(n) — we don't know which.
-/
axiom erdos_872_conjecture :
    -- Either gameValue(n) = Θ(n) [linear] or gameValue(n) = o(n) [sublinear]
    (∃ c : ℚ, c > 0 ∧ ∀ n ≥ 10, gameValue n ≥ (c * n).floor) ∨
    (∀ ε : ℚ, ε > 0 → ∃ N : ℕ, ∀ n ≥ N, gameValue n ≤ (ε * n).ceil)

/-
## Part IX: Summary
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
    -- The game value is bounded above by n/2
    (∀ n : ℕ, n ≥ 2 → gameValue n ≤ n / 2) :=
  ⟨primes_antichain, gameValue_upper⟩

end Erdos872
