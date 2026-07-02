/-
# Undirected Eulerian Circuit Theorem — Degree Characterization (Necessity)

This file formalizes the **necessity** half of Euler's theorem on Eulerian trails
and circuits for *undirected* simple graphs, and the general **obstruction**
theorem that resolves the Königsberg Seven Bridges problem.

Euler's theorem states, for a connected undirected graph `G`:

* `G` has an Eulerian **circuit** (a closed trail using every edge exactly once)
  iff every vertex has **even** degree;
* `G` has an Eulerian **trail** from `u` to `v` (with `u ≠ v`) iff `u` and `v`
  are the only two vertices of **odd** degree.

Mathlib (`Mathlib.Combinatorics.SimpleGraph.Trails`) provides the core degree
book-keeping for Eulerian trails: `SimpleGraph.Walk.IsEulerian.even_degree_iff`
and `SimpleGraph.Walk.IsEulerian.card_odd_degree`. Here we package these into the
classical necessity statements and, crucially, prove the two results that are
*not* directly available as single Mathlib lemmas:

1. `eulerian_circuit_forall_even` — a closed Eulerian trail forces **all**
   degrees even.
2. `eulerian_trail_odd_iff_endpoint` — for an open Eulerian trail `u → v`
   (`u ≠ v`) the odd-degree vertices are **exactly** `{u, v}`. This pins the two
   endpoints, strengthening the mere cardinality bound.
3. `no_eulerian_trail_of_card_odd_ne` — if the number of odd-degree vertices is
   anything other than `0` or `2`, **no** Eulerian trail (of any endpoints)
   exists. This is the general Königsberg obstruction: the bridges graph has four
   odd-degree land masses, so no Eulerian trail can exist.

The **sufficiency** direction (connectivity + the degree condition implies an
Eulerian circuit exists — undirected Hierholzer) is not proved here; the directed
analogue is formalized in `KonigsbergOQ02OQ01.lean`
(`directed_euler_circuit_sufficient_corrected`). Undirected sufficiency remains
the open direction for this entry.

All results are machine-checked with no `sorry` and no additional axioms beyond
Mathlib's foundational ones.
-/
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Tactic

open SimpleGraph SimpleGraph.Walk

namespace UndirectedEuler

variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- **Necessity for Eulerian circuits.**
A closed Eulerian trail (an Eulerian circuit) visits every edge exactly once and
returns to its start; consequently *every* vertex must have even degree. This is
the "all degrees even" half of Euler's characterization of Eulerian circuits. -/
theorem eulerian_circuit_forall_even {u : V} {p : G.Walk u u}
    (h : p.IsEulerian) (x : V) : Even (G.degree x) := by
  rw [h.even_degree_iff]
  intro huu
  exact absurd rfl huu

/-- **Endpoint identification for Eulerian trails.**
For an *open* Eulerian trail from `u` to `v` with `u ≠ v`, a vertex has odd degree
**iff** it is one of the two endpoints. In particular the odd-degree vertices are
exactly `{u, v}`, strengthening the cardinality statement
`IsEulerian.card_odd_degree`. -/
theorem eulerian_trail_odd_iff_endpoint {u v : V} {p : G.Walk u v}
    (h : p.IsEulerian) (hne : u ≠ v) (x : V) :
    Odd (G.degree x) ↔ x = u ∨ x = v := by
  rw [← Nat.not_even_iff_odd, h.even_degree_iff]
  constructor
  · intro hnot
    by_contra hc
    push_neg at hc
    exact hnot (fun _ => hc)
  · rintro (rfl | rfl) hall
    · exact (hall hne).1 rfl
    · exact (hall hne).2 rfl

/-- The odd-degree endpoints of an open Eulerian trail are distinct and are
precisely the trail's start and finish, as a `Finset` equality. -/
theorem eulerian_trail_oddFinset_eq {u v : V} {p : G.Walk u v}
    (h : p.IsEulerian) (hne : u ≠ v) :
    (Finset.univ.filter fun x => Odd (G.degree x)) = {u, v} := by
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  exact eulerian_trail_odd_iff_endpoint h hne x

/-- **General Königsberg obstruction.**
If the number of odd-degree vertices is neither `0` nor `2`, then the graph admits
no Eulerian trail whatsoever (regardless of endpoints). The Königsberg bridges
graph has four vertices of odd degree, so this rules out any Eulerian trail — the
resolution of Euler's 1736 problem. -/
theorem no_eulerian_trail_of_card_odd_ne
    (h0 : Fintype.card {v : V | Odd (G.degree v)} ≠ 0)
    (h2 : Fintype.card {v : V | Odd (G.degree v)} ≠ 2) :
    ¬ ∃ (u v : V) (p : G.Walk u v), p.IsEulerian := by
  rintro ⟨u, v, p, h⟩
  rcases h.card_odd_degree with hc | hc
  · exact h0 hc
  · exact h2 hc

/-- **Circuit form of the obstruction.**
If some vertex has odd degree, there is no Eulerian *circuit* (closed Eulerian
trail). Contrapositive of `eulerian_circuit_forall_even`. -/
theorem no_eulerian_circuit_of_odd_degree {x : V} (hx : Odd (G.degree x)) :
    ¬ ∃ (u : V) (p : G.Walk u u), p.IsEulerian := by
  rintro ⟨u, p, h⟩
  exact (Nat.not_even_iff_odd.mpr hx) (eulerian_circuit_forall_even h x)

end UndirectedEuler
