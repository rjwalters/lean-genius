/-
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

/- ## Ramsey property for triangles -/

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

/- ## Ramsey families -/

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

/- ## Main conjecture -/

/-- Erdős Problem 638: For every Ramsey family `S` and every infinite
colour type, there exists a graph with the appropriate Ramsey property. -/
def ErdosProblem638 : Prop :=
    ∀ (S : (m : ℕ) → Set (SimpleGraph (Fin m))),
      IsRamseyFamily S →
        ∀ (κ : Type), Infinite κ →
          ∃ (V : Type) (G : SimpleGraph V),
            HasCardinalTriangleRamsey G κ

/- ## Classical Ramsey theorem -/

/-- The classical Ramsey theorem for triangles: for every `n`, there exists
`N` such that every `n`-colouring of `K_N` contains a monochromatic
triangle. -/
axiom ramsey_triangle (n : ℕ) (hn : 1 ≤ n) :
    ∃ N : ℕ, HasTriangleRamsey (⊤ : SimpleGraph (Fin N)) n

/-- The family of complete graphs is a Ramsey family.
    Proved from ramsey_triangle: for each n, it provides an N with K_N Ramsey. -/
theorem complete_graphs_ramsey :
    IsRamseyFamily (fun m => ({⊤} : Set (SimpleGraph (Fin m)))) := by
  intro n hn
  obtain ⟨N, hN⟩ := ramsey_triangle n hn
  exact ⟨N, ⊤, Set.mem_singleton _, hN⟩

/- ## Basic observations -/

/-- For 1 colour, K_3 has the triangle Ramsey property: every 1-colouring
    trivially yields a monochromatic triangle (Fin 1 is a subsingleton). -/
theorem ramsey_triangle_base :
    HasTriangleRamsey (⊤ : SimpleGraph (Fin 3)) 1 := by
  intro c
  refine ⟨0, 1, 2, by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_⟩
  all_goals first | simp [SimpleGraph.top_adj] | exact Subsingleton.elim _ _

/-- The n = 1 case of ramsey_triangle, proved without using the axiom. -/
theorem ramsey_triangle_one_proved :
    ∃ N : ℕ, HasTriangleRamsey (⊤ : SimpleGraph (Fin N)) 1 :=
  ⟨3, ramsey_triangle_base⟩

/-- Monotonicity: if `G` has the `n`-colour property and `m ≤ n`, then
`G` also has the `m`-colour property. Proved by embedding Fin m into
Fin n via castLE; injectivity preserves monochromaticity. -/
theorem triangle_ramsey_mono {V : Type*} (G : SimpleGraph V) (m n : ℕ)
    (hmn : m ≤ n) (h : HasTriangleRamsey G n) : HasTriangleRamsey G m := by
  intro c
  obtain ⟨a, b, d, hab, hbd, had, eab, ebd, ead, hc1, hc2⟩ :=
    h (fun v w => (c v w).castLE hmn)
  have hInj : Function.Injective (Fin.castLE hmn) := Fin.castLE_injective hmn
  exact ⟨a, b, d, hab, hbd, had, eab, ebd, ead, hInj hc1, hInj hc2⟩
