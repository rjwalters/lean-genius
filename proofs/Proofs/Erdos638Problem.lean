/-!
# Erdős Problem 638: Ramsey Families and Infinite Cardinals

Let `S` be a family of finite graphs such that for every `n`, there exists
some `G_n ∈ S` where every `n`-colouring of the edges of `G_n` yields a
monochromatic triangle.

For every infinite cardinal `ℵ`, does there exist a graph `G` such that
every finite subgraph of `G` belongs to `S`, and every `ℵ`-colouring of
the edges of `G` yields a monochromatic triangle?

Erdős notes: "if the answer is affirmative many extensions and
generalisations will be possible."

*Reference:* [erdosproblems.com/638](https://www.erdosproblems.com/638)
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

open SimpleGraph

/-! ## Ramsey property for triangles -/

/-- A colouring of edges yields a monochromatic triangle if there exist
three mutually adjacent vertices whose edges all receive the same colour. -/
def HasMonoTriangle {V : Type*} {α : Type*} (G : SimpleGraph V)
    (c : V → V → α) : Prop :=
    ∃ (a b d : V), a ≠ b ∧ b ≠ d ∧ a ≠ d ∧
      G.Adj a b ∧ G.Adj b d ∧ G.Adj a d ∧
      c a b = c b d ∧ c b d = c a d

/-- A graph `G` has the `n`-colour Ramsey property for triangles if every
colouring of its vertex pairs with `n` colours yields a monochromatic
triangle. -/
def HasTriangleRamsey {V : Type*} (G : SimpleGraph V) (n : ℕ) : Prop :=
    ∀ c : V → V → Fin n, HasMonoTriangle G c

/-! ## Ramsey families -/

/-- A Ramsey family is a collection of finite graphs (indexed by vertex
count) such that for every `n`, some member has the `n`-colour triangle
Ramsey property. -/
def IsRamseyFamily (S : (m : ℕ) → Set (SimpleGraph (Fin m))) : Prop :=
    ∀ n : ℕ, 1 ≤ n →
      ∃ (m : ℕ) (G : SimpleGraph (Fin m)),
        G ∈ S m ∧ HasTriangleRamsey G n

/-- A graph has the `κ`-colour triangle Ramsey property (for any type of
`κ` colours). -/
def HasCardinalTriangleRamsey {V : Type*} (G : SimpleGraph V)
    (κ : Type*) : Prop :=
    ∀ c : V → V → κ, HasMonoTriangle G c

/-! ## Main conjecture -/

/-- Erdős Problem 638: For every Ramsey family `S` and every infinite
colour type, there exists a graph with the appropriate Ramsey property. -/
def ErdosProblem638 : Prop :=
    ∀ (S : (m : ℕ) → Set (SimpleGraph (Fin m))),
      IsRamseyFamily S →
        ∀ (κ : Type), Infinite κ →
          ∃ (V : Type) (G : SimpleGraph V),
            HasCardinalTriangleRamsey G κ

/-! ## Classical Ramsey theorem -/

/-- The classical Ramsey theorem for triangles: for every `n`, there exists
`N` such that every `n`-colouring of `K_N` contains a monochromatic
triangle. -/
axiom ramsey_triangle (n : ℕ) (hn : 1 ≤ n) :
    ∃ N : ℕ, HasTriangleRamsey (⊤ : SimpleGraph (Fin N)) n

/-- The family of complete graphs is a Ramsey family. -/
axiom complete_graphs_ramsey :
    IsRamseyFamily (fun m => {⊤ : SimpleGraph (Fin m)})

/-! ## Basic observations -/

/-- Monotonicity: if `G` has the `n`-colour property and `m ≤ n`, then
`G` also has the `m`-colour property. -/
axiom triangle_ramsey_mono {V : Type*} (G : SimpleGraph V) (m n : ℕ)
    (hmn : m ≤ n) (h : HasTriangleRamsey G n) : HasTriangleRamsey G m
