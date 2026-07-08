/-
Erdős Problem #1080 — Open Question OQ-03: Which cycle lengths occur?

Parent problem (Erdos1080Problem.lean) studies C₄,C₆-free bipartite graphs and
the extremal function f(n,m). Erdős observed that a dense such graph must still
contain a C₈ (eight-cycle), and OQ-03 asks to "extend to other cycle lengths
(C₈, C₁₀, ...)".

This file supplies the structural foundation for that extension: in ANY
bipartite graph every cycle has EVEN length, and in fact length ≥ 4. This is
exactly why the problem lives in the even-cycle world {C₄, C₆, C₈, C₁₀, ...}
and why no odd cycle (C₅, C₇, C₉, ...) ever occurs — so the only candidate
extensions of the C₄/C₆ story are the longer even cycles.

The bipartition / cycle-length definitions are inlined here (mirroring those in
Erdos1080Problem.lean) so that this companion is self-contained and independently
verifiable; the parent gallery file currently carries an unrelated `sorry` in
`c4_free_iff_no_K22` and a malformed doc-comment, so it is not imported.

Main results (all 0 sorries / 0 axioms, over an arbitrary vertex type):
* `bipartite_walk_parity` — the parity engine: along any walk the endpoint's
  side (X or Y) is determined by the parity of the walk length.
* `bipartite_closed_walk_even` — every closed walk in a bipartite graph has
  even length.
* `bipartite_cycle_even` — every cycle length in a bipartite graph is even.
* `bipartite_odd_cycle_free` — a bipartite graph has no cycle of odd length,
  with the concrete instances `bipartite_C5_free`, `bipartite_C7_free`,
  `bipartite_C9_free`.
* `bipartite_cycle_length_ge_four` / `bipartite_cycle_length_even_ge_four` —
  every cycle length is even and at least 4.

References:
- Erdős [Er75]: C₈ observation for the C₄,C₆-free extremal problem.
- Standard fact: a graph is bipartite iff it has no odd cycle (König 1936).
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Data.Set.Basic

open SimpleGraph Set

namespace Erdos1080OQ03

variable {V : Type*} {G : SimpleGraph V}

/-
## Definitions (inlined from Erdos1080Problem.lean)
-/

/-- `(X, Y)` is a bipartition of `G`: the parts are disjoint, cover the vertex
set, and every edge crosses from one part to the other. -/
def IsBipartition (G : SimpleGraph V) (X Y : Set V) : Prop :=
  Disjoint X Y ∧ X ∪ Y = Set.univ ∧ ∀ ⦃u v⦄, G.Adj u v → (u ∈ X ↔ v ∈ Y)

/-- `G` is bipartite if it admits some bipartition. -/
def IsBipartite (G : SimpleGraph V) : Prop :=
  ∃ X Y : Set V, IsBipartition G X Y

/-- `G` contains a cycle of length `k`. -/
def HasCycleOfLength (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ (v : V) (walk : G.Walk v v), walk.IsCycle ∧ walk.length = k

/-
## Partition side algebra

`IsBipartition G X Y` packages `Disjoint X Y`, `X ∪ Y = univ`, and the edge
condition. The two lemmas below are the pure set-theoretic content: X and Y are
literal complements of each other.
-/

/-- In a bipartition, membership in the left part is the negation of membership
in the right part. -/
theorem mem_left_iff_not_right {X Y : Set V} (h : IsBipartition G X Y) (z : V) :
    z ∈ X ↔ z ∉ Y := by
  constructor
  · intro hz hzy
    exact Set.disjoint_left.mp h.1 hz hzy
  · intro hz
    have hcover : z ∈ X ∪ Y := by rw [h.2.1]; exact Set.mem_univ z
    rcases hcover with h' | h'
    · exact h'
    · exact absurd h' hz

/-- In a bipartition, membership in the right part is the negation of membership
in the left part. -/
theorem mem_right_iff_not_left {X Y : Set V} (h : IsBipartition G X Y) (z : V) :
    z ∈ Y ↔ z ∉ X := by
  have hz := mem_left_iff_not_right h z
  constructor
  · intro hzy hzx
    exact (hz.mp hzx) hzy
  · intro hzx
    by_contra hzy
    exact hzx (hz.mpr hzy)

/-
## The parity engine

Along any walk `w : G.Walk u v`, the side of the endpoint `v` is forced by the
parity of `w.length` and the side of the start `u`. Proved by induction on the
walk: each edge crosses from one part to the other, flipping both the parity and
the side.
-/

/-- **Walk parity.** For a walk `w` from `u` to `v` in a bipartite graph:
if `u` is on the left, `v` is on the left iff the walk has even length; and
symmetrically for the right part. -/
theorem bipartite_walk_parity {X Y : Set V} (h : IsBipartition G X Y)
    {u v : V} (w : G.Walk u v) :
    (u ∈ X → (Even w.length ↔ v ∈ X)) ∧ (u ∈ Y → (Even w.length ↔ v ∈ Y)) := by
  induction w with
  | nil =>
    have h0 : Even (0 : ℕ) := ⟨0, rfl⟩
    refine ⟨fun hu => ?_, fun hu => ?_⟩
    · simp only [Walk.length_nil]; exact iff_of_true h0 hu
    · simp only [Walk.length_nil]; exact iff_of_true h0 hu
  | @cons a b c hadj p ih =>
    refine ⟨fun ha => ?_, fun ha => ?_⟩
    · -- a ∈ X, so the first edge lands b ∈ Y; use the Y-branch of `ih`.
      have hb : b ∈ Y := (h.2.2 hadj).mp ha
      have hp := ih.2 hb
      rw [Walk.length_cons, Nat.even_add_one, hp]
      exact (mem_left_iff_not_right h c).symm
    · -- a ∈ Y, so the first edge lands b ∈ X; use the X-branch of `ih`.
      have haX : a ∉ X := fun hax => Set.disjoint_left.mp h.1 hax ha
      have hbY : b ∉ Y := fun hby => haX ((h.2.2 hadj).mpr hby)
      have hb : b ∈ X := (mem_left_iff_not_right h b).mpr hbY
      have hp := ih.1 hb
      rw [Walk.length_cons, Nat.even_add_one, hp]
      exact (mem_right_iff_not_left h c).symm

/-
## Even cycles
-/

/-- Every closed walk in a bipartite graph has even length. -/
theorem bipartite_closed_walk_even {X Y : Set V} (h : IsBipartition G X Y)
    {v : V} (w : G.Walk v v) : Even w.length := by
  have hcover : v ∈ X ∪ Y := by rw [h.2.1]; exact Set.mem_univ v
  rcases hcover with hv | hv
  · exact ((bipartite_walk_parity h w).1 hv).mpr hv
  · exact ((bipartite_walk_parity h w).2 hv).mpr hv

/-- **Bipartite graphs have only even cycles.** Every cycle length occurring in
a bipartite graph is even. -/
theorem bipartite_cycle_even (hbip : IsBipartite G) {k : ℕ}
    (hcyc : HasCycleOfLength G k) : Even k := by
  obtain ⟨X, Y, h⟩ := hbip
  obtain ⟨v, w, _, hlen⟩ := hcyc
  rw [← hlen]
  exact bipartite_closed_walk_even h w

/-- A bipartite graph has no cycle of odd length (the odd-cycle-free direction
of König's characterization). -/
theorem bipartite_odd_cycle_free (hbip : IsBipartite G) {k : ℕ} (hk : Odd k) :
    ¬ HasCycleOfLength G k := by
  intro hcyc
  have : Even k := bipartite_cycle_even hbip hcyc
  exact (Nat.not_even_iff_odd.mpr hk) this

/-- No 5-cycle in a bipartite graph. -/
theorem bipartite_C5_free (hbip : IsBipartite G) : ¬ HasCycleOfLength G 5 :=
  bipartite_odd_cycle_free hbip (by decide)

/-- No 7-cycle in a bipartite graph. -/
theorem bipartite_C7_free (hbip : IsBipartite G) : ¬ HasCycleOfLength G 7 :=
  bipartite_odd_cycle_free hbip (by decide)

/-- No 9-cycle in a bipartite graph. -/
theorem bipartite_C9_free (hbip : IsBipartite G) : ¬ HasCycleOfLength G 9 :=
  bipartite_odd_cycle_free hbip (by decide)

/-
## Cycle length lower bound

A cycle has length ≥ 3 (`IsCycle.three_le_length`); combined with evenness this
sharpens to ≥ 4, so the shortest possible cycle is a C₄ and the realizable
lengths are exactly {4, 6, 8, 10, ...}.
-/

/-- Every cycle in a bipartite graph has length at least 4. -/
theorem bipartite_cycle_length_ge_four (hbip : IsBipartite G) {k : ℕ}
    (hcyc : HasCycleOfLength G k) : 4 ≤ k := by
  obtain ⟨X, Y, h⟩ := hbip
  obtain ⟨v, w, hwc, hlen⟩ := hcyc
  have hthree : 3 ≤ w.length := hwc.three_le_length
  have heven : Even w.length := bipartite_closed_walk_even h w
  rw [← hlen]
  obtain ⟨m, hm⟩ := heven
  omega

/-- **Summary.** In a bipartite graph every cycle length is even and at least 4:
the admissible cycle lengths are exactly the even numbers ≥ 4 ({C₄, C₆, C₈, ...}),
so the C₄/C₆ extremal story extends only through longer even cycles, never
through odd ones. -/
theorem bipartite_cycle_length_even_ge_four (hbip : IsBipartite G) {k : ℕ}
    (hcyc : HasCycleOfLength G k) : Even k ∧ 4 ≤ k :=
  ⟨bipartite_cycle_even hbip hcyc, bipartite_cycle_length_ge_four hbip hcyc⟩

end Erdos1080OQ03
