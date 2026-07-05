/-
# The Handshake Lemma and its parity corollaries

## Statement
For a finite simple graph `G`, the sum of all vertex degrees equals twice the
number of edges:

  **∑_{v} deg(v) = 2 · |E(G)|.**

Equivalently, the degree sum is always even, and the number of vertices of odd
degree is even ("at any party, an even number of people have shaken hands an odd
number of times").

## Honest scope note
Mathlib already contains the two headline facts:
  * `SimpleGraph.sum_degrees_eq_twice_card_edges` — the handshake identity itself;
  * `SimpleGraph.even_card_odd_degree_vertices` — the even-odd-degree corollary.

This entry restates those as gallery-facing theorems and then adds the corollaries
that Mathlib does **not** state directly, which are the theory-level content here:

  1. `even_sum_degrees` — the degree sum is even (the "counting parity" form).
  2. `even_card_of_all_odd_degree` — if *every* vertex has odd degree the graph has an
     even number of vertices (the filtered set is everything).
  3. `even_card_of_oddRegular` — **an odd-regular finite graph has even order.** This is
     the clean structural consequence combining regularity with the handshake parity, and
     it is not recorded in Mathlib.
  4. A **sharpness** witness: the triangle `K₃ = (⊤ : SimpleGraph (Fin 3))` is `2`-regular
     (even degree) yet has `3` (odd) vertices, so the oddness hypothesis in
     `even_card_of_oddRegular` genuinely cannot be dropped.

Sorry-free and axiom-free (the sharpness witnesses use kernel `decide`, not
`native_decide`, so no extra trust assumptions are introduced).
-/
import Mathlib

namespace HandshakeLemma

open Finset SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **The Handshake Lemma.** In a finite simple graph the sum of the vertex degrees
equals twice the number of edges. (A gallery restatement of Mathlib's
`SimpleGraph.sum_degrees_eq_twice_card_edges`.) -/
theorem sum_degrees_eq_twice_card_edges :
    ∑ v, G.degree v = 2 * G.edgeFinset.card :=
  G.sum_degrees_eq_twice_card_edges

/-- The sum of all vertex degrees is even — the counting-parity form of the handshake
lemma, immediate from `∑ deg = 2·|E|`. -/
theorem even_sum_degrees : Even (∑ v, G.degree v) := by
  rw [sum_degrees_eq_twice_card_edges]
  exact even_two_mul _

/-- **Handshake corollary.** The number of vertices of odd degree is even. (A gallery
restatement of Mathlib's `SimpleGraph.even_card_odd_degree_vertices`.) -/
theorem even_card_odd_degree_vertices :
    Even (univ.filter fun v => Odd (G.degree v)).card :=
  G.even_card_odd_degree_vertices

/-- If **every** vertex has odd degree, then the graph has an even number of vertices:
the set of odd-degree vertices is all of `V`, and that set has even cardinality. -/
theorem even_card_of_all_odd_degree
    (h : ∀ v, Odd (G.degree v)) : Even (Fintype.card V) := by
  have hfilter : (univ.filter fun v => Odd (G.degree v)) = univ := by
    ext v; simp [h v]
  have := G.even_card_odd_degree_vertices
  rwa [hfilter, card_univ] at this

/-- **Odd-regular graphs have even order.** If `G` is `d`-regular with `d` odd, then the
number of vertices of `G` is even. This is the structural consequence of the handshake
parity: every vertex then has odd degree, so the vertex set splits into pairs. Mathlib does
not state this directly. -/
theorem even_card_of_oddRegular {d : ℕ} (hodd : Odd d)
    (hreg : G.IsRegularOfDegree d) : Even (Fintype.card V) :=
  even_card_of_all_odd_degree G fun v => by rw [hreg v]; exact hodd

section Sharpness

/-- **Sharpness (part 1).** The triangle `K₃ = (⊤ : SimpleGraph (Fin 3))` is `2`-regular:
every vertex has degree `Fintype.card (Fin 3) - 1 = 2`. -/
theorem triangle_isRegular : (⊤ : SimpleGraph (Fin 3)).IsRegularOfDegree 2 := by
  simpa using IsRegularOfDegree.top (V := Fin 3)

/-- **Sharpness (part 2).** The triangle has an odd number (`3`) of vertices. Combined
with `triangle_isRegular` and `Even 2`, this shows an *even*-regular graph can have odd
order — so the oddness hypothesis in `even_card_of_oddRegular` cannot be dropped. -/
theorem triangle_card_odd : Odd (Fintype.card (Fin 3)) := by
  decide

end Sharpness

end HandshakeLemma
