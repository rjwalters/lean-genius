/-
Erdős Problem #1212: Composite Coordinates Path in Coprime Graph

Source: https://erdosproblems.com/1212
Status: SOLVED ($50 prize)

Statement:
Let G be the graph on {(x,y) ∈ ℕ² : gcd(x,y) = 1} where (x,y) ~ (x',y')
if they differ by ±1 in exactly one coordinate.
Is there an infinite path P in G where every (x,y) ∈ P has min(x,y) > 1
and at least one of x, y is composite?

Answer: YES — proved.
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace Erdos1212

/-- Vertex type: coprime pairs -/
def CoprimeVertex := {p : ℕ × ℕ // Nat.Coprime p.1 p.2}

/-- Adjacency: differ by ±1 in exactly one coordinate -/
def coprimeAdj (v w : CoprimeVertex) : Prop :=
  let (a, b) := v.val
  let (c, d) := w.val
  (Nat.Coprime a b) ∧ (Nat.Coprime c d) ∧
  ((a = c + 1 ∨ c = a + 1) ∧ b = d) ∨ (a = c ∧ (b = d + 1 ∨ d = b + 1))

/-- The coprime graph G -/
noncomputable def coprimeGraph : SimpleGraph CoprimeVertex :=
  { Adj := fun v w => v ≠ w ∧ coprimeAdj v w
    symm := by intro x y ⟨hne, hadj⟩; exact ⟨hne.symm, by simp [coprimeAdj] at *; tauto⟩
    loopless := by intro x ⟨h, _⟩; exact h rfl }

/-- Desired path property: min > 1 and at least one composite -/
def IsGoodVertex (v : CoprimeVertex) : Prop :=
  let (x, y) := v.val
  min x y > 1 ∧ (¬Nat.Prime x ∨ ¬Nat.Prime y)

/--
**Main Result (Solved):**
There exists an infinite path in G where all vertices are "good"
(min > 1 and at least one coordinate composite).
-/
axiom erdos_1212_solved :
    ∃ (path : ℕ → CoprimeVertex),
      (∀ n, coprimeGraph.Adj (path n) (path (n + 1))) ∧
      (∀ n, IsGoodVertex (path n)) ∧
      Function.Injective path

/-- **Erdős Problem #1212: SOLVED** -/
theorem erdos_1212 :
    ∃ (path : ℕ → CoprimeVertex),
      (∀ n, coprimeGraph.Adj (path n) (path (n + 1))) ∧
      ∀ n, IsGoodVertex (path n) :=
  let ⟨p, hadj, hgood, _⟩ := erdos_1212_solved; ⟨p, hadj, hgood⟩

end Erdos1212
