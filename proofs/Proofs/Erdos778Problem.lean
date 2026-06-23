/-
Erdős Problem #778: Clique-Building Games on Complete Graphs

Source: https://erdosproblems.com/778
Status: OPEN (Partial Results by Malekshahian-Spiro 2024)

Statement:
Alice and Bob play a game on the edges of K_n, alternating coloring edges red (Alice)
and blue (Bob). Alice goes first. Three variants:

1. CLIQUE GAME: Alice wins if her largest red clique is larger than any blue clique.
   Question: Does Bob have a winning strategy for n ≥ 3?

2. MODIFIED GAME: Bob colors 2 edges per turn. Bob wins if his largest clique is
   strictly larger than Alice's. Does Bob win for n > 3?

3. DEGREE GAME: Alice wins if max degree of red subgraph > max degree of blue.
   Who wins?

Known Results (Malekshahian-Spiro 2024):
- Game 1: Bob wins with density ≥ 3/4. If Alice wins at n, Bob wins at n+1, n+2, n+3.
- Game 3: Bob wins with density ≥ 2/3. If Alice wins at n, Bob wins at n+1, n+2.

Erdős believed Bob should always have a winning strategy for Game 1.

Reference: https://erdosproblems.com/778
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Basic

open SimpleGraph Finset

namespace Erdos778

/- ## Part I: Basic Definitions

Game setup on the complete graph.
-/

/-- A coloring of edges: each edge is Red, Blue, or Uncolored -/
inductive EdgeColor where
  | Red : EdgeColor
  | Blue : EdgeColor
  | Uncolored : EdgeColor
  deriving DecidableEq

/-- A game state: symmetric assignment of colors to edges of K_n -/
structure GameState (n : ℕ) where
  color : Fin n → Fin n → EdgeColor
  symm : ∀ i j, color i j = color j i
  diag : ∀ i, color i i = EdgeColor.Uncolored

/-- The complete graph K_n (all distinct pairs connected) -/
def Kn (n : ℕ) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y
  symm := fun _ _ h => h.symm
  loopless := fun x h => h rfl

/-- Number of edges in K_n: n(n-1)/2 -/
def numEdges (n : ℕ) : ℕ := n * (n - 1) / 2

/- ## Part II: Colored Subgraphs

Extract the red and blue subgraphs from a game state.
-/

/-- The red subgraph: edges colored Red by Alice -/
def redSubgraph (n : ℕ) (state : GameState n) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ state.color x y = EdgeColor.Red
  symm := fun x y ⟨hne, hred⟩ => ⟨hne.symm, by rw [state.symm]; exact hred⟩
  loopless := fun _ ⟨hne, _⟩ => hne rfl

/-- The blue subgraph: edges colored Blue by Bob -/
def blueSubgraph (n : ℕ) (state : GameState n) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ state.color x y = EdgeColor.Blue
  symm := fun x y ⟨hne, hblue⟩ => ⟨hne.symm, by rw [state.symm]; exact hblue⟩
  loopless := fun _ ⟨hne, _⟩ => hne rfl

/-- A graph contains a clique of size k -/
def hasClique (G : SimpleGraph (Fin n)) (k : ℕ) : Prop :=
  ∃ s : Finset (Fin n), s.card = k ∧ G.IsClique ↑s

/- ## Part III: Game Mechanics

Turn order and game completion.
-/

/-- Whose turn it is (Alice = true on even moves, Bob on odd) -/
def isAliceTurn (moveCount : ℕ) : Bool :=
  moveCount % 2 == 0

/-- Game is over when all edges are colored -/
def gameOver (n : ℕ) (state : GameState n) : Prop :=
  ∀ i j : Fin n, i ≠ j → state.color i j ≠ EdgeColor.Uncolored

/- ## Part IV: Winning Conditions

The three game variants with their winning criteria.
-/

/-- Game 1 (Clique Game): Alice wins if max red clique > max blue clique -/
def aliceWinsCliqueGame (n : ℕ) (state : GameState n) : Prop :=
  gameOver n state ∧
  ∃ k : ℕ, hasClique (redSubgraph n state) k ∧
    ¬hasClique (blueSubgraph n state) k

/-- Game 2 (Modified): Bob colors 2 edges per Alice's 1; Bob wins if max blue > max red -/
def bobWinsModifiedGame (n : ℕ) (state : GameState n) : Prop :=
  gameOver n state ∧
  ∃ k : ℕ, hasClique (blueSubgraph n state) k ∧
    ¬hasClique (redSubgraph n state) k

/-- Maximum degree of a vertex in a subgraph -/
noncomputable def maxDegree (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.sup fun v => (Finset.univ.filter (G.Adj v)).card

/-- Game 3 (Degree Game): Alice wins if max red degree > max blue degree -/
def aliceWinsDegreeGame (n : ℕ) (state : GameState n) : Prop :=
  gameOver n state ∧
  @maxDegree n (redSubgraph n state) (Classical.decRel _) >
  @maxDegree n (blueSubgraph n state) (Classical.decRel _)

/- ## Part V: Strategies

Definitions for winning strategies.
-/

/-- A strategy for Alice: given state, choose an uncolored edge to color Red -/
def AliceStrategy (n : ℕ) := GameState n → Fin n × Fin n

/-- A strategy for Bob: given state, choose an uncolored edge to color Blue -/
def BobStrategy (n : ℕ) := GameState n → Fin n × Fin n

/-- The result of playing strategy σ against strategy τ on K_n
    (axiomatized: the game tree is finite so a final state exists) -/
axiom playGame (n : ℕ) (alice : AliceStrategy n) (bob : BobStrategy n) : GameState n

/-- Bob has a winning strategy for the clique game on K_n -/
def BobHasWinningStrategy_CliqueGame (n : ℕ) : Prop :=
  ∃ σ : BobStrategy n, ∀ τ : AliceStrategy n,
    ¬aliceWinsCliqueGame n (playGame n τ σ)

/-- Alice has a winning strategy for the clique game on K_n -/
def AliceHasWinningStrategy_CliqueGame (n : ℕ) : Prop :=
  ∃ τ : AliceStrategy n, ∀ σ : BobStrategy n,
    aliceWinsCliqueGame n (playGame n τ σ)

/-- Alice has a winning strategy for the degree game on K_n -/
def AliceHasWinningStrategy_DegreeGame (n : ℕ) : Prop :=
  ∃ τ : AliceStrategy n, ∀ σ : BobStrategy n,
    aliceWinsDegreeGame n (playGame n τ σ)

/-- Bob has a winning strategy for the degree game on K_n -/
def BobHasWinningStrategy_DegreeGame (n : ℕ) : Prop :=
  ∃ σ : BobStrategy n, ∀ τ : AliceStrategy n,
    ¬aliceWinsDegreeGame n (playGame n τ σ)

/- ## Part VI: Erdős's Conjecture and Known Results -/

/-- Erdős's Conjecture: Bob has winning strategy for all n ≥ 3 -/
def ErdosConjecture : Prop :=
  ∀ n : ℕ, n ≥ 3 → BobHasWinningStrategy_CliqueGame n

/-- Malekshahian-Spiro 2024: If Alice wins clique game at n, Bob wins at n+1, n+2, n+3.
    The set {n : Bob wins clique game} has natural density ≥ 3/4. -/
axiom malekshahian_spiro_alice_n_bob_n123 :
  ∀ n : ℕ, AliceHasWinningStrategy_CliqueGame n →
    BobHasWinningStrategy_CliqueGame (n + 1) ∧
    BobHasWinningStrategy_CliqueGame (n + 2) ∧
    BobHasWinningStrategy_CliqueGame (n + 3)

/-- Malekshahian-Spiro 2024: If Alice wins degree game at n, Bob wins at n+1 and n+2.
    The set {n : Bob wins degree game} has natural density ≥ 2/3. -/
axiom malekshahian_spiro_alice_n_bob_n12_degree :
  ∀ n : ℕ, AliceHasWinningStrategy_DegreeGame n →
    BobHasWinningStrategy_DegreeGame (n + 1) ∧
    BobHasWinningStrategy_DegreeGame (n + 2)

/- ## Part VII: Consequences of Known Results -/

/-- Alice cannot win the clique game at 4 consecutive values of n.
    Proof: If she wins at n, then by Malekshahian-Spiro, Bob wins
    at n+1, n+2, n+3, contradicting Alice winning at n+1. -/
theorem alice_no_four_consecutive (n : ℕ) :
    AliceHasWinningStrategy_CliqueGame n →
    ¬(AliceHasWinningStrategy_CliqueGame (n + 1) ∧
      AliceHasWinningStrategy_CliqueGame (n + 2) ∧
      AliceHasWinningStrategy_CliqueGame (n + 3)) := by
  intro hAlice ⟨h1, _, _⟩
  have hBob := malekshahian_spiro_alice_n_bob_n123 n hAlice
  -- Bob has winning strategy at n+1
  obtain ⟨σ, hσ⟩ := hBob.1
  -- Alice has winning strategy at n+1
  obtain ⟨τ, hτ⟩ := h1
  -- Contradiction: σ beats all Alice strategies, but τ beats all Bob strategies
  exact hσ τ (hτ σ)

/- ## Part VIII: Summary

Erdős Problem #778: OPEN

PROBLEM: Three games on K_n where Alice and Bob color edges.

KNOWN (Malekshahian-Spiro 2024):
1. Clique game: Bob wins with density ≥ 3/4
2. Degree game: Bob wins with density ≥ 2/3
3. If Alice wins at n, Bob wins at n+1, n+2, n+3 (clique game)
4. If Alice wins at n, Bob wins at n+1, n+2 (degree game)

OPEN: Does Bob ALWAYS win for n ≥ 3? (Erdős believed yes)
-/

/-- Summary of Erdős Problem #778: The Malekshahian-Spiro periodicity
    result implies Alice cannot win 4 consecutive values. -/
theorem erdos_778_periodicity :
    ∀ n : ℕ, AliceHasWinningStrategy_CliqueGame n →
    ¬(AliceHasWinningStrategy_CliqueGame (n + 1) ∧
      AliceHasWinningStrategy_CliqueGame (n + 2) ∧
      AliceHasWinningStrategy_CliqueGame (n + 3)) :=
  alice_no_four_consecutive

end Erdos778
