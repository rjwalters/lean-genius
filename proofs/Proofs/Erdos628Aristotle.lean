/-
  Aristotle companion for Erdős Problem #628: The Erdős-Lovász Tihany Conjecture

  This file exposes routine lemmas for automated proof search by Aristotle.
  The main formalization is in Erdos628Problem.lean.

  Targets: structural lemmas about perfect graphs and bipartite graphs that
  follow directly from their definitions via GraphCore, without depending on
  the sorry-defined IsLineGraph or independenceNumber functions.
-/

import Mathlib
import Proofs.GraphCore
import Proofs.Erdos628Problem

namespace Erdos628Aristotle

open Erdos628 GraphCore Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Perfect graphs satisfy cliqueNumber G < chromaticNumber G + 1.
    Follows because IsPerfect implies chromaticNumber G = cliqueNumber G. -/
theorem perfect_clique_free (G : SimpleGraph V) (hperf : IsPerfect G) :
    IsCliqueFree G (chromaticNumber G + 1) := by
  sorry

/-- For a perfect graph with chromaticNumber k, G is not K_k-free.
    Perfect graphs contain K_k when χ(G) = k. -/
theorem perfect_tihany_vacuous (G : SimpleGraph V) (hperf : IsPerfect G)
    (k : ℕ) (hχ : chromaticNumber G = k) :
    ¬IsCliqueFree G k := by
  sorry

/-- Bipartite graphs have chromatic number ≤ 2. -/
theorem bipartite_chi_le_2 (G : SimpleGraph V) (hbip : G.IsBipartite) :
    chromaticNumber G ≤ 2 := by
  sorry

/-- Every perfect graph is χ = ω (chromatic number equals clique number).
    Specialization of IsPerfect to the full vertex set. -/
theorem perfect_chi_eq_omega (G : SimpleGraph V) (hperf : IsPerfect G) :
    chromaticNumber G = cliqueNumber G := by
  sorry

end Erdos628Aristotle
