/-
Endpoints of an Eulerian Trail Are Exactly the Odd-Degree Vertices

This file completes the degree characterization of Eulerian trails for finite
simple graphs. Mathlib's `SimpleGraph.Walk.IsEulerian.even_degree_iff` gives the
awkwardly-quantified statement

    Even (G.degree x) ↔ (u ≠ v → x ≠ u ∧ x ≠ v)

and `IsEulerian.card_odd_degree` gives the count `0 ∨ 2`. The sibling file
`KonigsbergOQ01.lean` derives only the *non-endpoint ⟹ even* half of the
open-trail characterization (`euler_trail_non_endpoint_even`).

What was still missing — and is proved here — is the clean two-sided form:

* **Open trail (u ≠ v):** `Odd (G.degree w) ↔ (w = u ∨ w = v)`, i.e. the
  odd-degree vertices are *exactly* the two endpoints. The new content is the
  converse (endpoint ⟹ odd). As a set: `{w | Odd (G.degree w)} = {u, v}`, and
  the count is *exactly* 2 (sharpening the Mathlib `0 ∨ 2` to `= 2`).
* **Closed trail (circuit, u = v):** `{w | Odd (G.degree w)} = ∅`, with count 0.

Together these give the sharp dichotomy: an Eulerian trail exists as an open
walk with distinct endpoints iff there are exactly two odd vertices (and they
are the endpoints), and as a circuit iff there are none.

Builds on: Konigsberg.lean, KonigsbergOQ01.lean (Euler trail extensions)
Authors: lean-genius research (researcher-11)
-/
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Algebra.Ring.Parity

namespace KonigsbergOQ05

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-
## Part 1: The open-trail endpoint characterization

For an Eulerian trail from `u` to `v` with `u ≠ v`, a vertex has odd degree
**if and only if** it is one of the two endpoints. This is the two-sided
strengthening of `KonigsbergOQ01.euler_trail_non_endpoint_even`.
-/

/-- **Endpoint ⟺ odd degree.** For an Eulerian trail from `u` to `v` with
`u ≠ v`, a vertex `w` has odd degree iff `w` is an endpoint (`w = u ∨ w = v`).
The forward direction (odd ⟹ endpoint) restates the contrapositive of Mathlib's
`even_degree_iff`; the backward direction (endpoint ⟹ odd) is the genuinely new
content. -/
theorem euler_trail_odd_iff_endpoint {u v w : V} (p : G.Walk u v)
    (hp : p.IsEulerian) (huv : u ≠ v) :
    Odd (G.degree w) ↔ (w = u ∨ w = v) := by
  rw [← Nat.not_even_iff_odd, hp.even_degree_iff]
  constructor
  · -- ¬(u ≠ v → w ≠ u ∧ w ≠ v) ⟹ w = u ∨ w = v
    intro hn
    by_contra hc
    exact hn (fun _ => ⟨fun h => hc (Or.inl h), fun h => hc (Or.inr h)⟩)
  · -- w = u ∨ w = v ⟹ ¬(u ≠ v → w ≠ u ∧ w ≠ v)
    intro hor hi
    obtain ⟨h1, h2⟩ := hi huv
    rcases hor with rfl | rfl
    · exact h1 rfl
    · exact h2 rfl

/-- The left endpoint of an open Eulerian trail has odd degree. -/
theorem euler_trail_left_odd {u v : V} (p : G.Walk u v)
    (hp : p.IsEulerian) (huv : u ≠ v) : Odd (G.degree u) :=
  (euler_trail_odd_iff_endpoint G (w := u) p hp huv).mpr (Or.inl rfl)

/-- The right endpoint of an open Eulerian trail has odd degree. -/
theorem euler_trail_right_odd {u v : V} (p : G.Walk u v)
    (hp : p.IsEulerian) (huv : u ≠ v) : Odd (G.degree v) :=
  (euler_trail_odd_iff_endpoint G (w := v) p hp huv).mpr (Or.inr rfl)

/-- **The odd-degree vertices are exactly the endpoints.** For an open Eulerian
trail, the set of odd-degree vertices equals the (two-element) endpoint set. -/
theorem euler_trail_odd_set {u v : V} (p : G.Walk u v)
    (hp : p.IsEulerian) (huv : u ≠ v) :
    {w : V | Odd (G.degree w)} = {u, v} := by
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  exact euler_trail_odd_iff_endpoint G p hp huv

/-- **Exactly two odd-degree vertices.** For an open Eulerian trail (`u ≠ v`),
there are *exactly* two odd-degree vertices — sharpening Mathlib's
`card_odd_degree` (which only gives `0 ∨ 2`), since the endpoint `u` witnesses
that the count is nonzero. -/
theorem euler_trail_card_odd_eq_two {u v : V} (p : G.Walk u v)
    (hp : p.IsEulerian) (huv : u ≠ v) :
    Fintype.card {w : V | Odd (G.degree w)} = 2 := by
  rcases hp.card_odd_degree with h0 | h2
  · exfalso
    have hu : Odd (G.degree u) := euler_trail_left_odd G p hp huv
    have hne : Nonempty {w : V | Odd (G.degree w)} := ⟨⟨u, hu⟩⟩
    rw [← Fintype.card_pos_iff] at hne
    omega
  · exact h2

/-
## Part 2: The closed-trail (circuit) characterization

For an Eulerian circuit (`u = u`), every vertex has even degree, so there are no
odd-degree vertices at all. This is the `= ∅` / count `= 0` complement of the
open-trail case, completing the dichotomy.
-/

/-- **A circuit has no odd-degree vertices.** For an Eulerian circuit the set of
odd-degree vertices is empty. -/
theorem euler_circuit_no_odd {u : V} (p : G.Walk u u)
    (hp : p.IsEulerian) : {w : V | Odd (G.degree w)} = ∅ := by
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rw [Nat.not_odd_iff_even]
  exact (hp.even_degree_iff (x := w)).mpr (by simp)

/-- **Zero odd-degree vertices in a circuit.** The count complement of
`euler_trail_card_odd_eq_two`. -/
theorem euler_circuit_card_odd_eq_zero {u : V} (p : G.Walk u u)
    (hp : p.IsEulerian) : Fintype.card {w : V | Odd (G.degree w)} = 0 := by
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun w => ?_⟩
  have hw : Odd (G.degree (w : V)) := w.2
  have hne : ¬ Odd (G.degree (w : V)) := by
    rw [Nat.not_odd_iff_even]
    exact (hp.even_degree_iff (x := (w : V))).mpr (by simp)
  exact hne hw

end KonigsbergOQ05
