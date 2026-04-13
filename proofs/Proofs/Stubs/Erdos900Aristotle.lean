/-
  Aristotle targets for Erdős Problem #900
  Routine supporting lemmas for automated proof search.
  See Erdos900Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT aks_theorem (main result — open problem)
  - NOT large_c_almost_hamiltonian (depends on undefined pathLengthFunction)
  - NOT probHasProperty (definition sorry — Aristotle skips)
  - Routine: path properties, graph connectivity basics, length calculations
  - No definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos900Aristotle

open Finset Function

/-- A simple graph on n vertices. -/
abbrev Graph (n : ℕ) := SimpleGraph (Fin n)

/-- A path in a graph: a list of distinct vertices with consecutive adjacency. -/
def IsPath (G : Graph n) (vs : List (Fin n)) : Prop :=
  vs.Nodup ∧ ∀ i : ℕ, i + 1 < vs.length →
    G.Adj (vs.get ⟨i, by omega⟩) (vs.get ⟨i + 1, by omega⟩)

/-- The length of a path is the number of edges (= vertices - 1). -/
def pathLength (vs : List α) : ℕ := vs.length - 1

/-- A graph has a path of length at least k. -/
def HasPathOfLength (G : Graph n) (k : ℕ) : Prop :=
  ∃ vs : List (Fin n), IsPath G vs ∧ pathLength vs ≥ k

-- Routine: The empty list is a valid path in any graph.
theorem isPath_nil (G : Graph n) : IsPath G [] := by
  constructor
  · exact List.nodup_nil
  · intro i hi; simp at hi

-- Routine: A single-vertex list is a valid path.
theorem isPath_singleton (G : Graph n) (v : Fin n) : IsPath G [v] := by
  constructor
  · exact List.nodup_singleton v
  · intro i hi; simp at hi

-- Routine: The length of an empty path is 0.
theorem pathLength_nil : pathLength ([] : List α) = 0 := by
  simp [pathLength]

-- Routine: The length of a singleton path is 0.
theorem pathLength_singleton (v : α) : pathLength [v] = 0 := by
  simp [pathLength]

-- Routine: The length of a two-element list is 1.
theorem pathLength_pair (u v : α) : pathLength [u, v] = 1 := by
  simp [pathLength]

-- Routine: Every graph has a path of length 0 (the empty path).
theorem has_path_zero (G : Graph n) : HasPathOfLength G 0 :=
  ⟨[], isPath_nil G, le_refl 0⟩

-- Routine: pathLength is monotone with respect to list length.
theorem pathLength_le_length (vs : List α) : pathLength vs ≤ vs.length := by
  simp [pathLength]; omega

-- Routine: If HasPathOfLength G k and k' ≤ k, then HasPathOfLength G k'.
theorem has_path_mono (G : Graph n) {k k' : ℕ} (hk : k' ≤ k)
    (h : HasPathOfLength G k) : HasPathOfLength G k' := by
  obtain ⟨vs, hvs, hlen⟩ := h
  exact ⟨vs, hvs, hk.trans hlen⟩

-- Routine: A path of length 0 exists whenever the vertex type is nonempty.
theorem has_path_zero_nonempty [Nonempty (Fin n)] (G : Graph n) : HasPathOfLength G 0 :=
  has_path_zero G

end Erdos900Aristotle
