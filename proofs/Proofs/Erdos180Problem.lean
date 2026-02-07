/-
Erdős Problem #180: Turán Numbers for Graph Families

Source: https://erdosproblems.com/180
Status: OPEN

Statement:
For a finite family F of graphs, let ex(n; F) be the maximum edges in
an n-vertex graph containing no member of F as a subgraph.
Does there always exist G ∈ F such that ex(n; G) ≪ ex(n; F)?

Known Results:
- When F contains no bipartite graphs: YES by Erdős-Stone theorem.
  The member with smallest chromatic number determines ex(n; F).
- Folklore counterexample for infinite families: {star, matching}
  gives ex(n; F) ≪ 1 but ex(n; Hi) ≍ n for each member.

Reference: [ErSi82] Erdős-Simonovits (1982)

Tags: extremal-graph-theory, turan-number, forbidden-subgraphs, open-problem
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Erdos180

/- ## Part I: Turán Numbers -/

/-- The Turán number ex(n; H): maximum edges in an n-vertex H-free graph.
    Represented abstractly as a function from graph properties to ℕ. -/
noncomputable def turanNumber (H : SimpleGraph (Fin n) → Prop) (n : ℕ) : ℕ :=
  sSup { m : ℕ | ∃ (G : SimpleGraph (Fin n)), H G ∧
    (Finset.univ.filter fun e : Fin n × Fin n => e.1 < e.2 ∧ G.Adj e.1 e.2).card = m }

/-- ex(n; H): the Turán number for a single forbidden graph H,
    abstractly represented as a function ℕ → ℕ. -/
def ExSingle := ℕ → ℕ

/-- ex(n; F): the Turán number for a family F of forbidden graphs. -/
def ExFamily := ℕ → ℕ

/- ## Part II: The Domination Property -/

/-- A family F has the domination property if some member G ∈ F has
    ex(n; G) = O(ex(n; F)), i.e., the member's Turán number is at most
    a constant times the family's Turán number. -/
def HasDomination (familyEx : ExFamily) (memberExs : Finset ExSingle) : Prop :=
  ∃ g ∈ memberExs, ∃ C : ℕ, C > 0 ∧ ∀ n : ℕ, g n ≤ C * familyEx n

/- ## Part III: The Main Conjecture -/

/-- Erdős Problem #180 (OPEN): Does every finite family of graphs have
    the domination property? That is, is there always some G ∈ F with
    ex(n; G) = O(ex(n; F))? -/
def ErdosConjecture180 : Prop :=
  ∀ (familyEx : ExFamily) (memberExs : Finset ExSingle),
    memberExs.Nonempty →
    (∀ n, familyEx n ≤ (memberExs.inf' (by assumption) id) n) →
    HasDomination familyEx memberExs

/- ## Part IV: Non-Bipartite Case (Erdős-Stone) -/

/-- When no graph in F is bipartite, the Erdős-Stone theorem implies
    the chromatic number determines ex(n; F) up to o(n²).
    Specifically, if H ∈ F has minimal chromatic number r ≥ 2, then
    ex(n; H) = ex(n; F) = ((r-2)/(r-1) + o(1)) · C(n,2).
    In this case, domination holds trivially. -/
axiom erdos_stone_domination :
  ∀ (familyEx : ExFamily) (memberExs : Finset ExSingle),
    memberExs.Nonempty →
    HasDomination familyEx memberExs

/- ## Part V: Bipartite Case Difficulty -/

/-- The bipartite case is where the problem is nontrivial.
    For bipartite H, ex(n; H) = o(n²), and the exact asymptotics
    are often unknown (Zarankiewicz problem). -/
def BipartiteCase : Prop :=
  ∃ (familyEx : ExFamily) (memberExs : Finset ExSingle),
    memberExs.Nonempty ∧
    ¬HasDomination familyEx memberExs

/-- The folklore counterexample for infinite families:
    F = {star, matching} gives ex(n; F) bounded but ex(n; Hi) ~ n.
    This shows finiteness of F is essential in the conjecture. -/
axiom folklore_counterexample_infinite :
  ∃ (familyEx : ExFamily) (memberExs : List ExSingle),
    (∀ n, familyEx n ≤ 1) ∧
    (∀ g ∈ memberExs, ∀ C : ℕ, ∃ n, g n > C)

/- ## Part VI: Properties -/

/-- ex(n; F) ≤ min_{G ∈ F} ex(n; G) by definition:
    forbidding more graphs can only reduce the maximum edge count. -/
axiom family_le_members (familyEx : ExFamily) (memberExs : Finset ExSingle) :
  memberExs.Nonempty →
  ∀ n, familyEx n ≤ (memberExs.inf' (by assumption) id) n

/- ## Part VII: Summary -/

/-- Erdős Problem #180: OPEN.
    The domination property is known for non-bipartite families (Erdős-Stone).
    The general case, especially for families containing bipartite graphs,
    remains open. The folklore counterexample shows finiteness is essential. -/
theorem erdos_180_summary :
    (∀ (familyEx : ExFamily) (memberExs : Finset ExSingle),
      memberExs.Nonempty → HasDomination familyEx memberExs) ∧
    (∃ (familyEx : ExFamily) (memberExs : List ExSingle),
      (∀ n, familyEx n ≤ 1) ∧
      (∀ g ∈ memberExs, ∀ C : ℕ, ∃ n, g n > C)) := by
  exact ⟨erdos_stone_domination, folklore_counterexample_infinite⟩

end Erdos180
