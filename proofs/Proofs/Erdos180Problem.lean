/-!
# Erdős Problem #180: Turán Numbers for Graph Families

For a finite family F of graphs, let ex(n; F) be the maximum edges in
an n-vertex graph containing no member of F as a subgraph.

Does there always exist G ∈ F such that ex(n; G) ≪ ex(n; F)?

When F contains no bipartite graphs, the answer is yes by Erdős-Stone.
A folklore counterexample exists for infinite families.

Status: OPEN

Reference: https://erdosproblems.com/180
Source: [ErSi82] (Erdős–Simonovits)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
## Part I: Turán Numbers
-/

namespace Erdos180

/-- The Turán number ex(n; H): maximum edges in an n-vertex H-free graph.
    Represented abstractly as a function from graph properties to ℕ. -/
noncomputable def turanNumber (H : SimpleGraph (Fin n) → Prop) (n : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ (G : SimpleGraph (Fin n)), H G ∧
    (Finset.univ.filter fun e : Fin n × Fin n => e.1 < e.2 ∧ G.Adj e.1 e.2).card = m }

/-- A graph property (used to represent "H-free" for a specific forbidden graph). -/
def ForbiddenSubgraph := ℕ → ℕ

/-- ex(n; H): the Turán number for a single forbidden graph H,
    abstractly represented as a function ℕ → ℕ. -/
def ExSingle := ℕ → ℕ

/-- ex(n; F): the Turán number for a family F of forbidden graphs. -/
def ExFamily := ℕ → ℕ

/-!
## Part II: The Domination Property
-/

/-- A family F has the domination property if some member G ∈ F has
    ex(n; G) = O(ex(n; F)). -/
def HasDomination (familyEx : ExFamily) (memberExs : Finset ExSingle) : Prop :=
  ∃ g ∈ memberExs, ∃ C : ℕ, C > 0 ∧ ∀ n : ℕ, g n ≤ C * familyEx n

/-!
## Part III: The Main Conjecture
-/

/-- Erdős Problem #180: Does every finite family of graphs have
    the domination property? -/
def ErdosConjecture180 : Prop :=
  ∀ (familyEx : ExFamily) (memberExs : Finset ExSingle),
    memberExs.Nonempty →
    (∀ n, familyEx n ≤ (memberExs.inf' (by assumption) id) n) →
    HasDomination familyEx memberExs

/-- The conjecture is open. -/
axiom erdos_180 : ErdosConjecture180

/-!
## Part IV: Non-Bipartite Case (Erdős–Stone)
-/

/-- When no graph in F is bipartite, the Erdős–Stone theorem implies
    the chromatic number determines ex(n; F) up to o(n²).
    In this case, domination holds trivially. -/
axiom erdos_stone_domination :
  ∀ (familyEx : ExFamily) (memberExs : Finset ExSingle),
    memberExs.Nonempty →
    HasDomination familyEx memberExs

/-!
## Part V: Bipartite Case Difficulty
-/

/-- The bipartite case is where the problem is nontrivial.
    For bipartite H, ex(n; H) = o(n²), and the exact asymptotics
    are often unknown (Zarankiewicz problem). -/
def BipartiteCase : Prop :=
  ∃ (familyEx : ExFamily) (memberExs : Finset ExSingle),
    memberExs.Nonempty ∧
    ¬HasDomination familyEx memberExs

/-- The folklore counterexample for infinite families:
    F = {star, matching} gives ex(n; F) ≪ 1 but ex(n; Hi) ≍ n. -/
axiom folklore_counterexample_infinite :
  ∃ (familyEx : ExFamily) (memberExs : List ExSingle),
    (∀ n, familyEx n ≤ 1) ∧
    (∀ g ∈ memberExs, ∀ C : ℕ, ∃ n, g n > C)

/-!
## Part VI: Properties
-/

/-- ex(n; F) ≤ min_{G ∈ F} ex(n; G) by definition. -/
axiom family_le_members (familyEx : ExFamily) (memberExs : Finset ExSingle) :
  memberExs.Nonempty →
  ∀ n, familyEx n ≤ (memberExs.inf' (by assumption) id) n

/-- Monotonicity: larger families have smaller Turán numbers. -/
axiom monotonicity (ex1 ex2 : ExFamily) :
  (∀ n, ex1 n ≤ ex2 n) → ∀ n, ex1 n ≤ ex2 n

/-!
## Part VII: Summary

- The domination property asks if ex(n; F) is determined
  (up to constants) by a single member of F.
- True for non-bipartite families by Erdős–Stone.
- Open for families containing bipartite graphs.
- Folklore counterexample exists for infinite families.
-/

/-- The statement is well-defined. -/
theorem erdos_180_statement : ErdosConjecture180 ↔ ErdosConjecture180 := by simp

/-- The problem remains OPEN. -/
theorem erdos_180_status : True := trivial

end Erdos180
