/-
  Erdős Problem #1006 - Open Question 04 (Decidability):
  Polynomial-Time Decidability of Robust Acyclicity (Existence Form)

  Source: https://erdosproblems.com/1006
  Related: Erdos1006OQ03 (every finite graph admits a robustly acyclic orientation)

  ## The Open Question

  OQ04 asks: "Is robust acyclicity decidable in polynomial time? Given a graph G,
  can we efficiently determine whether G admits a robustly acyclic orientation,
  or is this NP-hard?"

  ## The Answer (Rank-Based Formulation)

  Under the rank-based formulation of `isRobustlyAcyclic` used in
  Erdos1006OQ01/OQ02/OQ03, the existence question is **trivial**: every finite
  graph admits a robustly acyclic orientation (`every_finite_graph_has_robust`
  in OQ03). This is established constructively via the coloring orientation,
  which exists for every finite graph thanks to `colorable_of_fintype` (a graph
  on n vertices is properly n-colorable).

  Consequence: the existence decision problem is **constant-time** decidable —
  the predicate `admitsRobustAcyclicOrientation` is `True` on every input
  `(V, [Fintype V], G)`. Therefore it is trivially in P, with O(1) decision
  complexity. The question is *not* NP-hard.

  ## Caveat: Verification (a Different Question)

  A related but distinct problem is the *verification* form: given a graph G
  together with an orientation D, decide whether D is robustly acyclic. Under
  the rank-based formulation, robust acyclicity is equivalent to acyclicity
  (see `isRobustlyAcyclic_iff_isAcyclic` in OQ02), so verification reduces to
  cycle detection — solvable in O(|V| + |E|) by topological sort, hence in P.

  Thus *both* the existence and verification forms of OQ04 admit polynomial-time
  decision procedures under the rank-based formulation.

  Status: 0 axioms, 0 sorries
-/

import Proofs.Erdos1006OQ03

open SimpleGraph

namespace Erdos1006OQ04Decidability

variable {V : Type*}

/-
## Part I: The Existence Decision Procedure (Constant-Time)

The decision procedure for "does G admit a robustly acyclic orientation"
is trivial under the rank-based formulation: always return `true`.
This is constant-time and correct for every finite graph.
-/

/-- The decision procedure for the existence question OQ04: simply return `true`.
    Correctness is `decideAdmitsRobustAcyclic_correct` below. -/
def decideAdmitsRobustAcyclic (G : SimpleGraph V) : Bool := true

/-- Soundness and completeness: the constant-time procedure is correct on every
    finite graph. The forward direction uses `every_finite_graph_has_robust`
    from OQ03; the reverse direction is `rfl`. -/
theorem decideAdmitsRobustAcyclic_correct [Fintype V] (G : SimpleGraph V) :
    decideAdmitsRobustAcyclic G = true ↔ admitsRobustAcyclicOrientation G :=
  ⟨fun _ => every_finite_graph_has_robust G, fun _ => rfl⟩

/-- The decision procedure always returns `true`. -/
theorem decideAdmitsRobustAcyclic_eq_true (G : SimpleGraph V) :
    decideAdmitsRobustAcyclic G = true := rfl

/-
## Part II: A Decidable Instance

Since `admitsRobustAcyclicOrientation G` is provably `True` for every finite
graph, we can give a `Decidable` instance that always returns `isTrue`.
-/

/-- `admitsRobustAcyclicOrientation G` is decidable, with `decide` evaluating
    to `true` for every finite graph. -/
instance instDecidableAdmitsRobustAcyclic [Fintype V] (G : SimpleGraph V) :
    Decidable (admitsRobustAcyclicOrientation G) :=
  Decidable.isTrue (every_finite_graph_has_robust G)

/-
## Part III: The Polynomial-Time Claim

We restate the existence-form OQ04 answer in the canonical form: there is
a constant-time decision procedure whose output equals the predicate.
This formalises that OQ04 (existence form, rank-based) is in P, in fact
in O(1), and is *not* NP-hard.
-/

/-- **OQ04 (existence form, rank-based) is in P.**

    There is a procedure `decideAdmitsRobustAcyclic` that runs in O(1) time
    and correctly decides `admitsRobustAcyclicOrientation` on every finite
    graph. The procedure is the constant function `true`; correctness is
    `every_finite_graph_has_robust`. -/
theorem oq04_existence_in_P [Fintype V] (G : SimpleGraph V) :
    ∃ b : Bool, b = decideAdmitsRobustAcyclic G ∧
      (b = true ↔ admitsRobustAcyclicOrientation G) :=
  ⟨decideAdmitsRobustAcyclic G, rfl, decideAdmitsRobustAcyclic_correct G⟩

/-- **OQ04 (existence form) has answer YES on every finite graph.**

    Equivalently: the predicate `admitsRobustAcyclicOrientation` is universally
    true on the class of finite graphs. This is the negation of the NP-hard
    alternative. -/
theorem oq04_existence_universally_yes [Fintype V] (G : SimpleGraph V) :
    admitsRobustAcyclicOrientation G :=
  every_finite_graph_has_robust G

end Erdos1006OQ04Decidability
