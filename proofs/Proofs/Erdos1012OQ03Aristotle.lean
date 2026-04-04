/-
  Aristotle targets for Erdős #1012 OQ-03 (Directed Hamiltonian Cycle Thresholds)
  Routine supporting lemmas for automated proof search.
  See Erdos1012OQ03.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main Hamiltonian cycle theorems (Ghouila-Houri, Moon-Moser, Redei)
  - NOT the GH insertion lemma (requires pigeonhole argument)
  - Routine finite-maximization and list-manipulation lemmas

  Main targets:

  1. exists_longest_directed_cycle_ari: Among all directed cycle lists in a
     finite digraph, one has maximum length. Key: nodup lists over a Fintype
     have bounded length (≤ Fintype.card V), so achievable lengths are bounded.
     A nonempty bounded subset of ℕ has a maximum.

  2. insertNth_directed_cycle_ari: Inserting vertex u at position i+1 in a
     directed cycle list l, given arcs l[i]→u and u→l[(i+1) mod |l|],
     yields a directed cycle list of length |l|+1.
     Proof: (a) Nodup: List.Nodup.insertNth + u ∉ l.
            (b) Length ≥ 2: immediate from |l| ≥ 2.
            (c) Arc condition: case split on j vs. i+1.
-/
import Mathlib
import Proofs.Erdos1012OQ03

namespace Erdos1012OQ03Aristotle

open Erdos1012OQ03 Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A nonempty finite digraph always has a longest directed cycle
    (maximizing list length over all directed cycle lists). -/
lemma exists_longest_directed_cycle_ari (D : Digraph V)
    (hcycle : ∃ l : List V, IsDirectedCycleList D l) :
    ∃ (lmax : List V), IsDirectedCycleList D lmax ∧
      ∀ (l' : List V), IsDirectedCycleList D l' → l'.length ≤ lmax.length := by
  sorry

/-- Inserting a vertex u at position i+1 in a directed cycle list, given arcs
    l[i]→u and u→l[(i+1) mod |l|], yields a valid directed cycle list. -/
lemma insertNth_directed_cycle_ari (D : Digraph V) (l : List V) (u : V)
    (hc : IsDirectedCycleList D l) (hu : u ∉ l) (i : ℕ) (hi : i < l.length)
    (harc_in : D.arc (l[i]'hi) u)
    (harc_out : D.arc u (l[(i + 1) % l.length]'
      (Nat.mod_lt _ (by have := hc.2.1; omega)))) :
    IsDirectedCycleList D (l.insertNth (i + 1) u) := by
  sorry

end Erdos1012OQ03Aristotle
