import Proofs.Erdos85CrossEdgeSwitch

/-! Finite programs of universal cross-edge switches. -/

open SimpleGraph

namespace Erdos85

/-- Degree expressed intrinsically as the cardinality of the neighbor set. -/
noncomputable def canonicalDegree
    {V : Type*} (H : SimpleGraph V) (v : V) : ℕ :=
  H.neighborSet v |>.ncard

/-- The cross-edge switch with its finite adjacency decision chosen internally. -/
noncomputable def canonicalCrossEdgeSwitch
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (x w : V) : SimpleGraph V := by
  classical
  exact crossEdgeSwitch H x w

/-- The canonical switch still preserves `C₄`-freeness. -/
theorem canonicalCrossEdgeSwitch_not_containsC4
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (x w : V) (hfree : ¬ containsC4 V H) :
    ¬ containsC4 V (canonicalCrossEdgeSwitch H x w) := by
  classical
  simpa [canonicalCrossEdgeSwitch] using
    crossEdgeSwitch_not_containsC4 H x w hfree

/-- Away from its endpoints, the canonical switch can only lower degree. -/
theorem canonicalCrossEdgeSwitch_degree_le_of_ne_endpoints
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (x w v : V) (hvx : v ≠ x) (hvw : v ≠ w) :
    canonicalDegree (canonicalCrossEdgeSwitch H x w) v ≤
      canonicalDegree H v := by
  classical
  apply Set.ncard_le_ncard (ht := Set.toFinite _)
  intro y hy
  rw [SimpleGraph.mem_neighborSet] at hy ⊢
  change (crossEdgeSwitch H x w).Adj v y at hy
  rcases (crossEdgeSwitch_adj_iff H x w v y).mp hy with hold | hnew
  · exact hold.1
  · rcases hnew.1 with ⟨h, _⟩ | ⟨h, _⟩
    · exact (hvx h).elim
    · exact (hvw h).elim

/-- Execute a finite sequence of cross-edge switches. -/
noncomputable def crossEdgeSwitchProgram
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (P : List (V × V)) : SimpleGraph V := by
  classical
  exact P.foldl (fun G p => canonicalCrossEdgeSwitch G p.1 p.2) H

@[simp] theorem crossEdgeSwitchProgram_nil
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) : crossEdgeSwitchProgram H [] = H := rfl

@[simp] theorem crossEdgeSwitchProgram_cons
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (x w : V) (P : List (V × V)) :
    crossEdgeSwitchProgram H ((x, w) :: P) =
      crossEdgeSwitchProgram (canonicalCrossEdgeSwitch H x w) P := by
  classical
  simp [crossEdgeSwitchProgram]

/-- Every finite program of cross-edge switches preserves `C₄`-freeness. -/
theorem crossEdgeSwitchProgram_not_containsC4
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (P : List (V × V))
    (hfree : ¬ containsC4 V H) :
    ¬ containsC4 V (crossEdgeSwitchProgram H P) := by
  classical
  induction P generalizing H with
  | nil => simpa
  | cons p P ih =>
      rcases p with ⟨x, w⟩
      rw [crossEdgeSwitchProgram_cons]
      exact ih (canonicalCrossEdgeSwitch H x w)
        (canonicalCrossEdgeSwitch_not_containsC4 H x w hfree)

/-- The vertices that occur as an endpoint in a switch program. -/
def crossEdgeSwitchProgramEndpoints
    {V : Type*} [DecidableEq V] (P : List (V × V)) : Finset V :=
  (P.flatMap fun p => [p.1, p.2]).toFinset

@[simp] theorem mem_crossEdgeSwitchProgramEndpoints
    {V : Type*} [DecidableEq V] {v : V} {P : List (V × V)} :
    v ∈ crossEdgeSwitchProgramEndpoints P ↔
      ∃ p ∈ P, v = p.1 ∨ v = p.2 := by
  simp [crossEdgeSwitchProgramEndpoints]

/-- A vertex untouched by every switch endpoint can only lose degree. -/
theorem crossEdgeSwitchProgram_degree_le_of_not_mem_endpoints
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (P : List (V × V)) (v : V)
    (hv : v ∉ crossEdgeSwitchProgramEndpoints P) :
    canonicalDegree (crossEdgeSwitchProgram H P) v ≤ canonicalDegree H v := by
  classical
  induction P generalizing H with
  | nil => simp
  | cons p P ih =>
      rcases p with ⟨x, w⟩
      rw [crossEdgeSwitchProgram_cons]
      have hvx : v ≠ x := by
        intro h
        apply hv
        simp [crossEdgeSwitchProgramEndpoints, h]
      have hvw : v ≠ w := by
        intro h
        apply hv
        simp [crossEdgeSwitchProgramEndpoints, h]
      have hvP : v ∉ crossEdgeSwitchProgramEndpoints P := by
        intro h
        apply hv
        have : v = x ∨ v = w ∨
            ∃ p ∈ P, v = p.1 ∨ v = p.2 :=
          Or.inr (Or.inr (mem_crossEdgeSwitchProgramEndpoints.mp h))
        simpa [crossEdgeSwitchProgramEndpoints] using this
      exact (ih (canonicalCrossEdgeSwitch H x w) hvP).trans
        (canonicalCrossEdgeSwitch_degree_le_of_ne_endpoints H x w v hvx hvw)

/-- Every initially low vertex must occur as an endpoint in any successful
switch program. -/
theorem low_degree_vertex_mem_crossEdgeSwitchProgramEndpoints
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (P : List (V × V)) (v : V) {d : ℕ}
    (hmin : ∀ u, d ≤ canonicalDegree (crossEdgeSwitchProgram H P) u)
    (hlow : canonicalDegree H v < d) :
    v ∈ crossEdgeSwitchProgramEndpoints P := by
  by_contra hv
  have hle := crossEdgeSwitchProgram_degree_le_of_not_mem_endpoints H P v hv
  have htarget := hmin v
  omega

/-- A program of `m` switches names at most `2m` distinct endpoints. -/
theorem crossEdgeSwitchProgramEndpoints_card_le
    {V : Type*} [DecidableEq V] (P : List (V × V)) :
    (crossEdgeSwitchProgramEndpoints P).card ≤ 2 * P.length := by
  calc
    (crossEdgeSwitchProgramEndpoints P).card ≤
        (P.flatMap fun p => [p.1, p.2]).length := by
      simpa [crossEdgeSwitchProgramEndpoints] using
        (List.toFinset_card_le (l := P.flatMap fun p => [p.1, p.2]))
    _ = 2 * P.length := by simp [Nat.mul_comm]

/-- Therefore repairing `k` initially low vertices needs at least `k/2`
switches, independently of the geometry of the graph. -/
theorem low_vertices_card_le_twice_switchProgram_length
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (P : List (V × V)) (D : Finset V) {d : ℕ}
    (hmin : ∀ u, d ≤ canonicalDegree (crossEdgeSwitchProgram H P) u)
    (hlow : ∀ v ∈ D, canonicalDegree H v < d) :
    D.card ≤ 2 * P.length := by
  apply (Finset.card_le_card ?_).trans
    (crossEdgeSwitchProgramEndpoints_card_le P)
  intro v hv
  exact low_degree_vertex_mem_crossEdgeSwitchProgramEndpoints
    H P v hmin (hlow v hv)

end Erdos85


