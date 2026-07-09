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
verifiable, and to keep its import surface minimal (only the SimpleGraph modules it
needs, not the parent's full-Mathlib import). The parent's `c4_free_iff_no_K22` — once
a `sorry` placeholder — is now a discharged theorem there; the equivalence below is the
independently-verified companion form.

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
* `bipartite_girth_ge_of_forbidden` — girth lifting: forbidding every even cycle
  of length `2m` for `2 ≤ m ≤ t` forces every remaining cycle to have length
  `≥ 2t + 2`. Concrete corollaries `bipartite_C4_free_girth_ge_six` (C₄-free ⇒
  girth ≥ 6) and `bipartite_C4C6_free_girth_ge_eight` (C₄,C₆-free ⇒ girth ≥ 8)
  pin down why Erdős's next target in the C₄,C₆-free extremal problem is the C₈:
  once the short even cycles are excluded, 8 is the smallest length still
  admissible.

References:
- Erdős [Er75]: C₈ observation for the C₄,C₆-free extremal problem.
- Standard fact: a graph is bipartite iff it has no odd cycle (König 1936).
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkCounting
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
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

/-
## Girth lifting under forbidden even cycles

The parent problem forbids C₄ and C₆. Because every cycle length is even and
≥ 4, excluding the short even cycles raises the girth: the admissible lengths
are `{4, 6, 8, 10, ...}`, so knocking out `4` and `6` leaves `8` as the smallest
survivor. This is exactly why, in a dense C₄,C₆-free bipartite graph, the next
cycle Erdős looks for is a C₈.
-/

/-- **Girth lifting.** If a bipartite graph has no cycle of length `2 * m` for
every `m` with `2 ≤ m ≤ t`, then every cycle it does contain has length at
least `2 * t + 2`. (The even cycle lengths are `{4, 6, 8, ...}`; forbidding the
first `t - 1` of them leaves `2t + 2` as the smallest admissible length.) -/
theorem bipartite_girth_ge_of_forbidden (hbip : IsBipartite G) {t : ℕ}
    (hforb : ∀ m, 2 ≤ m → m ≤ t → ¬ HasCycleOfLength G (2 * m))
    {k : ℕ} (hcyc : HasCycleOfLength G k) : 2 * t + 2 ≤ k := by
  have heven : Even k := bipartite_cycle_even hbip hcyc
  have hfour : 4 ≤ k := bipartite_cycle_length_ge_four hbip hcyc
  obtain ⟨s, hs⟩ := heven
  by_contra hlt
  push_neg at hlt
  have hs2 : 2 ≤ s := by omega
  have hst : s ≤ t := by omega
  have hk2s : 2 * s = k := by omega
  exact hforb s hs2 hst (by rw [hk2s]; exact hcyc)

/-- A C₄-free bipartite graph has girth ≥ 6: every cycle has length at least 6. -/
theorem bipartite_C4_free_girth_ge_six (hbip : IsBipartite G)
    (h4 : ¬ HasCycleOfLength G 4) {k : ℕ}
    (hcyc : HasCycleOfLength G k) : 6 ≤ k := by
  have hforb : ∀ m, 2 ≤ m → m ≤ 2 → ¬ HasCycleOfLength G (2 * m) := by
    intro m hm2 hm2'
    have hm : m = 2 := by omega
    subst hm
    have e : (2 * 2 : ℕ) = 4 := by omega
    rw [e]; exact h4
  have := bipartite_girth_ge_of_forbidden hbip hforb hcyc
  omega

/-- **C₄,C₆-free ⇒ girth ≥ 8.** In a bipartite graph with no 4-cycle and no
6-cycle, every cycle has length at least 8. This is the structural reason the
smallest cycle Erdős's C₄,C₆-free extremal problem can hope to force is a C₈. -/
theorem bipartite_C4C6_free_girth_ge_eight (hbip : IsBipartite G)
    (h4 : ¬ HasCycleOfLength G 4) (h6 : ¬ HasCycleOfLength G 6) {k : ℕ}
    (hcyc : HasCycleOfLength G k) : 8 ≤ k := by
  have hforb : ∀ m, 2 ≤ m → m ≤ 3 → ¬ HasCycleOfLength G (2 * m) := by
    intro m hm2 hm3
    have hm : m = 2 ∨ m = 3 := by omega
    rcases hm with hm | hm <;> subst hm
    · have e : (2 * 2 : ℕ) = 4 := by omega
      rw [e]; exact h4
    · have e : (2 * 3 : ℕ) = 6 := by omega
      rw [e]; exact h6
  have := bipartite_girth_ge_of_forbidden hbip hforb hcyc
  omega

/-! ### Bridge to Mathlib's two-colourability

`IsBipartite` (this file's ad-hoc predicate) coincides with Mathlib's
`SimpleGraph.Colorable 2`.  This lets the even-cycle / girth results above be
transported to any graph the wider gallery presents as `2`-colourable, and
conversely lets Mathlib's colouring API act on graphs built here. -/

/-- **`IsBipartite G ↔ G.Colorable 2`.**  A bipartition `(X, Y)` is exactly a
proper `2`-colouring: colour `X` with `0` and `Y` with `1`; conversely the two
colour classes of a `2`-colouring form a bipartition (edges are bichromatic, so
they cross). -/
theorem isBipartite_iff_colorable_two : IsBipartite G ↔ G.Colorable 2 := by
  have fin2 : ∀ x : Fin 2, x = 0 ∨ x = 1 := by decide
  constructor
  · rintro ⟨X, Y, h⟩
    classical
    refine ⟨Coloring.mk (fun v => if v ∈ X then (0 : Fin 2) else 1) ?_⟩
    intro u v huv
    have hiff : u ∈ X ↔ v ∈ Y := h.2.2 huv
    by_cases hu : u ∈ X
    · have hvnotX : v ∉ X := fun hvx => (mem_left_iff_not_right h v).mp hvx (hiff.mp hu)
      simp only [if_pos hu, if_neg hvnotX]; decide
    · have hvX : v ∈ X := (mem_left_iff_not_right h v).mpr (fun hvy => hu (hiff.mpr hvy))
      simp only [if_neg hu, if_pos hvX]; decide
  · rintro ⟨c⟩
    refine ⟨{v | c v = 0}, {v | c v = 1}, ?_, ?_, ?_⟩
    · rw [Set.disjoint_left]
      rintro v hv0 hv1
      simp only [Set.mem_setOf_eq] at hv0 hv1
      rw [hv0] at hv1; exact absurd hv1 (by decide)
    · ext v
      simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact fin2 (c v)
    · intro u v huv
      have hne : c u ≠ c v := c.valid huv
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hu0
        rcases fin2 (c v) with h0 | h1
        · exact absurd (hu0.trans h0.symm) hne
        · exact h1
      · intro hv1
        rcases fin2 (c u) with h0 | h1
        · exact h0
        · exact absurd (h1.trans hv1.symm) hne

/-! ### C₄-freeness ⇔ K₂,₂-freeness

In a bipartition `(X, Y)`, a `4`-cycle is exactly a `K_{2,2}`: two distinct
left vertices `a₁, a₂ ∈ X` and two distinct right vertices `b₁, b₂ ∈ Y` with all
four cross edges present.  The two lemmas below establish this equivalence, the
companion form of the parent problem file's `c4_free_iff_no_K22`
(`Erdos1080Problem.lean`, now a discharged theorem — formerly a `sorry` placeholder).

Since the bipartition forces the cycle's vertices to alternate sides, a `4`-cycle
must visit exactly two `X`-vertices and two `Y`-vertices; conversely a `K_{2,2}`
closes up into the cycle `a₁-b₁-a₂-b₂-a₁`. -/

/-- A `K_{2,2}` in a bipartite graph — two distinct `X`-vertices `a₁, a₂` each
adjacent to two distinct `Y`-vertices `b₁, b₂` — yields a `4`-cycle
`a₁-b₁-a₂-b₂-a₁`.  This is the "hard" content: assembling the explicit cycle and
checking it really is a cycle (its four vertices are distinct because the two
sides of a bipartition are disjoint). -/
theorem hasCycleOfLength_four_of_K22 {X Y : Set V} (h : IsBipartition G X Y)
    {a₁ a₂ b₁ b₂ : V} (ha₁ : a₁ ∈ X) (ha₂ : a₂ ∈ X) (hb₁ : b₁ ∈ Y) (hb₂ : b₂ ∈ Y)
    (hane : a₁ ≠ a₂) (hbne : b₁ ≠ b₂)
    (e11 : G.Adj a₁ b₁) (e12 : G.Adj a₁ b₂) (e21 : G.Adj a₂ b₁) (e22 : G.Adj a₂ b₂) :
    HasCycleOfLength G 4 := by
  -- Cross disequalities: an `X`-vertex and a `Y`-vertex are never equal.
  have ha₁Y : a₁ ∉ Y := (mem_left_iff_not_right h a₁).mp ha₁
  have ha₂Y : a₂ ∉ Y := (mem_left_iff_not_right h a₂).mp ha₂
  have hab11 : a₁ ≠ b₁ := fun heq => ha₁Y (heq ▸ hb₁)
  have hab12 : a₁ ≠ b₂ := fun heq => ha₁Y (heq ▸ hb₂)
  have hab21 : a₂ ≠ b₁ := fun heq => ha₂Y (heq ▸ hb₁)
  have hab22 : a₂ ≠ b₂ := fun heq => ha₂Y (heq ▸ hb₂)
  -- The path `b₁ → a₂ → b₂ → a₁`, built bottom-up so each extension is a path.
  have hp3 : (Walk.cons e12.symm Walk.nil : G.Walk b₂ a₁).IsPath :=
    Walk.IsPath.nil.cons (by
      simp only [Walk.support_nil, List.mem_singleton]; exact hab12.symm)
  have hp2 : (Walk.cons e22 (Walk.cons e12.symm Walk.nil) : G.Walk a₂ a₁).IsPath :=
    hp3.cons (by
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false]
      push_neg; exact ⟨hab22, hane.symm⟩)
  have hp1 : (Walk.cons e21.symm (Walk.cons e22 (Walk.cons e12.symm Walk.nil)) :
      G.Walk b₁ a₁).IsPath :=
    hp2.cons (by
      simp only [Walk.support_cons, Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false]
      push_neg; exact ⟨hab21.symm, hbne, hab11.symm⟩)
  -- Consing the edge `a₁ → b₁` closes the path into a cycle, provided that edge
  -- is not already used.
  refine ⟨a₁, Walk.cons e11 (Walk.cons e21.symm (Walk.cons e22 (Walk.cons e12.symm
    Walk.nil))), ?_, by simp [Walk.length_cons]⟩
  rw [Walk.cons_isCycle_iff]
  refine ⟨hp1, ?_⟩
  have hEdge : ∀ {c d : V}, ¬(a₁ = c ∧ b₁ = d) → ¬(a₁ = d ∧ b₁ = c) →
      s(a₁, b₁) ≠ s(c, d) := by
    intro c d h1 h2 heq
    rw [Sym2.eq_iff] at heq
    rcases heq with hh | hh
    · exact h1 hh
    · exact h2 hh
  simp only [Walk.edges_cons, Walk.edges_nil, List.mem_cons,
    List.not_mem_nil, or_false]
  push_neg
  exact ⟨hEdge (fun hh => hab11 hh.1) (fun hh => hane hh.1),
         hEdge (fun hh => hane hh.1) (fun hh => hab12 hh.1),
         hEdge (fun hh => hab12 hh.1) (fun hh => hbne hh.2)⟩

/-- **`C₄`-freeness ⇔ `K_{2,2}`-freeness** for a bipartite graph.  A bipartite
graph has no `4`-cycle iff no two distinct left vertices share two distinct
common neighbours — i.e. it contains no `K_{2,2}`.  This discharges the
`c4_free_iff_no_K22` statement left open in `Erdos1080Problem.lean`. -/
theorem c4Free_iff_no_K22 {X Y : Set V} (h : IsBipartition G X Y) :
    ¬ HasCycleOfLength G 4 ↔
      ∀ (a₁ a₂ b₁ b₂ : V), a₁ ∈ X → a₂ ∈ X → a₁ ≠ a₂ →
        b₁ ∈ Y → b₂ ∈ Y → b₁ ≠ b₂ →
        ¬(G.Adj a₁ b₁ ∧ G.Adj a₁ b₂ ∧ G.Adj a₂ b₁ ∧ G.Adj a₂ b₂) := by
  constructor
  · -- `C₄`-free ⇒ no `K_{2,2}`: a `K_{2,2}` would produce a `4`-cycle.
    intro hC4 a₁ a₂ b₁ b₂ ha₁ ha₂ hane hb₁ hb₂ hbne
    rintro ⟨e11, e12, e21, e22⟩
    exact hC4 (hasCycleOfLength_four_of_K22 h ha₁ ha₂ hb₁ hb₂ hane hbne e11 e12 e21 e22)
  · -- no `K_{2,2}` ⇒ `C₄`-free: a `4`-cycle would produce a `K_{2,2}`.
    intro hforbid ⟨v, w, hcyc, hlen⟩
    -- A closed walk of length `4` decomposes as four consecutive edges.
    cases w with
    | nil => simp at hlen
    | @cons _ x1 _ g1 w1 =>
    cases w1 with
    | nil => simp at hlen
    | @cons _ x2 _ g2 w2 =>
    cases w2 with
    | nil => simp at hlen
    | @cons _ x3 _ g3 w3 =>
    cases w3 with
    | nil => simp at hlen
    | @cons _ x4 _ g4 w4 =>
    cases w4 with
    | cons g5 w5 => simp only [Walk.length_cons] at hlen; omega
    | nil =>
      -- `w = v → x1 → x2 → x3 → v`; the four inner vertices are distinct.
      have htail := (Walk.isCycle_def _).mp hcyc |>.2.2
      simp only [Walk.support_cons, Walk.support_nil, List.tail_cons, List.nodup_cons,
        List.mem_cons, List.not_mem_nil, List.nodup_nil, or_false,
        and_true] at htail
      push_neg at htail
      obtain ⟨⟨_h12, h13, _h1v⟩, ⟨_h23, h2v⟩, _h3v⟩ := htail
      have hv : v ∈ X ∪ Y := by rw [h.2.1]; exact Set.mem_univ v
      rcases hv with hvX | hvY
      · -- `v ∈ X`, so the walk alternates `X, Y, X, Y`.
        have hx1 : x1 ∈ Y := (h.2.2 g1).mp hvX
        have hx1nX : x1 ∉ X := (mem_right_iff_not_left h x1).mp hx1
        have hx2 : x2 ∈ X :=
          (mem_left_iff_not_right h x2).mpr (fun hx2Y => hx1nX ((h.2.2 g2).mpr hx2Y))
        have hx3 : x3 ∈ Y := (h.2.2 g3).mp hx2
        exact hforbid v x2 x1 x3 hvX hx2 h2v.symm hx1 hx3 h13 ⟨g1, g4.symm, g2.symm, g3⟩
      · -- `v ∈ Y`, so the walk alternates `Y, X, Y, X`.
        have hvnX : v ∉ X := (mem_right_iff_not_left h v).mp hvY
        have hx1 : x1 ∈ X :=
          (mem_left_iff_not_right h x1).mpr (fun hx1Y => hvnX ((h.2.2 g1).mpr hx1Y))
        have hx2 : x2 ∈ Y := (h.2.2 g2).mp hx1
        have hx2nX : x2 ∉ X := (mem_right_iff_not_left h x2).mp hx2
        have hx3 : x3 ∈ X :=
          (mem_left_iff_not_right h x3).mpr (fun hx3Y => hx2nX ((h.2.2 g3).mpr hx3Y))
        exact hforbid x1 x3 v x2 hx1 hx3 h13 hvY hx2 h2v.symm ⟨g1.symm, g2, g4, g3.symm⟩

/-! ### Realizability: every even length ≥ 4 actually occurs

The results above are the *necessity* side of the cycle-length characterization:
in a bipartite graph every cycle length is even and `≥ 4`.  This section supplies
the matching *sufficiency* side — every even `k ≥ 4` really is the length of a
cycle in some bipartite graph — closing the characterization into an iff.

The witness for length `k` is Mathlib's cycle graph `cycleGraph k` on `Fin k`:
* it is bipartite when `k` is even (`cycleGraph.bicoloring_of_even` gives a proper
  `2`-colouring, hence `Colorable 2`, hence `IsBipartite` by the bridge above);
* it contains the Hamiltonian `k`-cycle `0 → (k-1) → (k-2) → … → 1 → 0`, built
  here as the descending path `descPath` closed by the wrap edge `0 → (k-1)`.

Mathlib has `cycleGraph` and its bicolouring but no lemma that `cycleGraph k` is
Hamiltonian, so the explicit cycle and its `IsCycle` proof are constructed from
scratch. -/

section Realizability

open SimpleGraph

variable (N : ℕ) [NeZero N]

/-- The descending path `⟨j⟩ → ⟨j-1⟩ → … → ⟨1⟩ → ⟨0⟩` inside `cycleGraph N`
(each step drops the index by one; consecutive indices differ by `1`, so they are
adjacent in the cycle graph). -/
def descPath : (j : ℕ) → (hj : j < N) → (cycleGraph N).Walk ⟨j, hj⟩ 0
  | 0, _ => Walk.nil
  | j + 1, h =>
      Walk.cons (by
          rw [cycleGraph_adj']
          left
          have hle : (⟨j, Nat.lt_of_succ_lt h⟩ : Fin N) ≤ ⟨j + 1, h⟩ :=
            Fin.mk_le_mk.mpr (Nat.le_succ j)
          rw [Fin.sub_val_of_le hle]; show j + 1 - j = 1; omega)
        (descPath j (Nat.lt_of_succ_lt h))

/-- The descending path from `⟨j⟩` has length `j`. -/
theorem descPath_length : ∀ (j : ℕ) (hj : j < N),
    (descPath N j hj).length = j := by
  intro j
  induction j with
  | zero => intro hj; unfold descPath; rfl
  | succ k ih =>
      intro hj
      unfold descPath
      rw [Walk.length_cons, ih (Nat.lt_of_succ_lt hj)]

/-- Every vertex on the descending path from `⟨j⟩` has index `≤ j`. -/
theorem descPath_support_val_le : ∀ (j : ℕ) (hj : j < N) (x : Fin N),
    x ∈ (descPath N j hj).support → x.val ≤ j := by
  intro j
  induction j with
  | zero =>
      intro hj x hx
      unfold descPath at hx
      rw [Walk.support_nil, List.mem_singleton] at hx
      subst hx; simp
  | succ k ih =>
      intro hj x hx
      unfold descPath at hx
      rw [Walk.support_cons, List.mem_cons] at hx
      rcases hx with h1 | h2
      · subst h1; simp
      · exact le_trans (ih (Nat.lt_of_succ_lt hj) x h2) (Nat.le_succ k)

/-- The descending path is a genuine path: its vertices are distinct (each new
index strictly exceeds every earlier one). -/
theorem descPath_isPath : ∀ (j : ℕ) (hj : j < N),
    (descPath N j hj).IsPath := by
  intro j
  induction j with
  | zero => intro hj; unfold descPath; exact Walk.IsPath.nil
  | succ k ih =>
      intro hj
      unfold descPath
      rw [Walk.cons_isPath_iff]
      refine ⟨ih (Nat.lt_of_succ_lt hj), ?_⟩
      intro hmem
      have hval : ((⟨k + 1, hj⟩ : Fin N) : ℕ) = k + 1 := rfl
      have := descPath_support_val_le N k (Nat.lt_of_succ_lt hj) ⟨k + 1, hj⟩ hmem
      omega

/-- Every edge of the descending path joins two indices differing by exactly one
(each edge is `s(⟨i+1⟩, ⟨i⟩)`). -/
theorem descPath_edges_diff_one : ∀ (j : ℕ) (hj : j < N) (e : Sym2 (Fin N)),
    e ∈ (descPath N j hj).edges → ∃ a b : Fin N, e = s(a, b) ∧ a.val = b.val + 1 := by
  intro j
  induction j with
  | zero =>
      intro hj e he
      unfold descPath at he
      rw [Walk.edges_nil] at he
      exact absurd he (List.not_mem_nil)
  | succ k ih =>
      intro hj e he
      unfold descPath at he
      rw [Walk.edges_cons, List.mem_cons] at he
      rcases he with h1 | h2
      · exact ⟨_, _, h1, rfl⟩
      · exact ih (Nat.lt_of_succ_lt hj) e h2

/-- The wrap-around edge `s(0, N-1)` closing the cycle is **not** one of the
descending-path edges: those all join indices differing by `1`, whereas `0` and
`N-1` differ by `N-1 ≥ 2`. -/
theorem closingEdge_not_mem (hN3 : 3 ≤ N) (hlast : N - 1 < N) :
    s((0 : Fin N), ⟨N - 1, hlast⟩) ∉ (descPath N (N - 1) hlast).edges := by
  intro he
  obtain ⟨a, b, heq, hab⟩ := descPath_edges_diff_one N (N - 1) hlast _ he
  rw [Sym2.eq_iff] at heq
  rcases heq with ⟨h1, _h2⟩ | ⟨h1, h2⟩
  · have ha0 : a.val = 0 := by rw [← h1]; simp
    omega
  · have hb0 : b.val = 0 := by rw [← h1]; simp
    have haN : a.val = N - 1 := by rw [← h2]
    omega

/-- **`cycleGraph N` contains an `N`-cycle** (for `N ≥ 3`): the Hamiltonian cycle
`0 → (N-1) → (N-2) → … → 1 → 0`. -/
theorem cycleGraph_hasCycleOfLength (hN3 : 3 ≤ N) :
    HasCycleOfLength (cycleGraph N) N := by
  have hlast : N - 1 < N := by omega
  have hz : ((0 : Fin N) : ℕ) = 0 := by simp
  have hl : ((⟨N - 1, hlast⟩ : Fin N) : ℕ) = N - 1 := rfl
  have hadj : (cycleGraph N).Adj (0 : Fin N) ⟨N - 1, hlast⟩ := by
    rw [cycleGraph_adj']
    left
    have hlt : (0 : Fin N) < ⟨N - 1, hlast⟩ := by rw [Fin.lt_def, hz, hl]; omega
    rw [Fin.coe_sub_iff_lt.mpr hlt, hz, hl]
    omega
  refine ⟨0, Walk.cons hadj (descPath N (N - 1) hlast), ?_, ?_⟩
  · rw [Walk.cons_isCycle_iff]
    exact ⟨descPath_isPath N (N - 1) hlast, closingEdge_not_mem N hN3 hlast⟩
  · rw [Walk.length_cons, descPath_length N (N - 1) hlast]
    omega

omit [NeZero N] in
/-- **`cycleGraph N` is bipartite when `N` is even** (its standard parity
`2`-colouring). -/
theorem cycleGraph_isBipartite_of_even (hEven : Even N) :
    IsBipartite (cycleGraph N) := by
  rw [isBipartite_iff_colorable_two]
  have hc := (cycleGraph.bicoloring_of_even N hEven).colorable
  rwa [Fintype.card_bool] at hc

/-- **`cycleGraph N` is NOT bipartite when `N` is odd** (for `N ≥ 3`): it *is* an
odd cycle, and a bipartite graph has no odd cycle.  This is the converse of
`cycleGraph_isBipartite_of_even`, closing the parity dichotomy of the cycle
graphs. -/
theorem cycleGraph_not_isBipartite_of_odd (hN3 : 3 ≤ N) (hOdd : Odd N) :
    ¬ IsBipartite (cycleGraph N) := fun hbip =>
  bipartite_odd_cycle_free hbip hOdd (cycleGraph_hasCycleOfLength N hN3)

/-- **`cycleGraph N` is bipartite iff `N` is even** (for `N ≥ 3`).  Combines the
standard even parity `2`-colouring with the odd-cycle obstruction, giving the
sharp characterization of which cycle graphs are two-colourable. -/
theorem cycleGraph_isBipartite_iff_even (hN3 : 3 ≤ N) :
    IsBipartite (cycleGraph N) ↔ Even N := by
  constructor
  · intro hbip
    rcases Nat.even_or_odd N with heven | hodd
    · exact heven
    · exact absurd hbip (cycleGraph_not_isBipartite_of_odd N hN3 hodd)
  · exact cycleGraph_isBipartite_of_even N

end Realizability

/-- **Sufficiency.** Every even `k ≥ 4` is the length of a cycle in some bipartite
graph — witnessed by the even cycle graph `cycleGraph k`. -/
theorem bipartite_realizes_even_ge_four {k : ℕ} (hEven : Even k) (hk : 4 ≤ k) :
    ∃ (V : Type) (G : SimpleGraph V), IsBipartite G ∧ HasCycleOfLength G k := by
  haveI : NeZero k := ⟨by omega⟩
  exact ⟨Fin k, cycleGraph k, cycleGraph_isBipartite_of_even k hEven,
    cycleGraph_hasCycleOfLength k (by omega)⟩

/-- **The bipartite cycle spectrum.**  A natural number `k` is the length of some
cycle in some bipartite graph **iff** `k` is even and `≥ 4`.  The forward
direction is the necessity engine (`bipartite_cycle_length_even_ge_four`); the
backward direction is the explicit even-cycle-graph construction
(`bipartite_realizes_even_ge_four`).  So the realizable cycle lengths of the
bipartite world are exactly `{4, 6, 8, 10, …}`. -/
theorem bipartite_cycle_spectrum (k : ℕ) :
    (∃ (V : Type) (G : SimpleGraph V), IsBipartite G ∧ HasCycleOfLength G k) ↔
      (Even k ∧ 4 ≤ k) := by
  constructor
  · rintro ⟨V, G, hbip, hcyc⟩
    exact bipartite_cycle_length_even_ge_four hbip hcyc
  · rintro ⟨hEven, hk⟩
    exact bipartite_realizes_even_ge_four hEven hk

/-! ### Sharpness of the girth-lifting bound

`bipartite_girth_ge_of_forbidden` is a *lower* bound: forbidding `C₄, …, C₂ₜ`
forces every remaining cycle to have length `≥ 2t + 2`.  This final section proves
that bound is **sharp** — for every `t ≥ 1` the even cycle graph
`cycleGraph (2t + 2)` is a bipartite graph that avoids every shorter even cycle
yet realises a `(2t + 2)`-cycle.  So `2t + 2` is exactly the girth, not merely a
lower bound, and Erdős's "next target is `C₈`" heuristic (the `t = 3` instance) is
seen to be optimal: an actual bipartite `C₄,C₆`-free graph of girth exactly `8`
exists.

The engine is that `cycleGraph N` is a **`2`-regular** graph (`SimpleGraph.IsCycles`).
By `IsCycle.adj_toSubgraph_iff_of_isCycles`, any cycle sitting inside a `2`-regular
graph has, at each of its vertices, exactly the same incident edges as the ambient
graph — so its vertex set is closed under the graph's adjacency.  In `cycleGraph N`
adjacency is `· ± 1`, so the support is closed under `· + 1`; the successor map
generates the whole cyclic group `Fin N`, forcing the cycle to span every vertex.
A spanning cycle is Hamiltonian, hence has length exactly `N`.  Consequently
`cycleGraph N` has **no cycle of any length except `N`** — its girth is exactly `N`.
-/

section Sharpness

open SimpleGraph

/-- A nonempty subset of `Fin N` closed under `· + 1` is all of `Fin N`: the
successor map generates the cyclic group, so the forward orbit of any point is
everything. -/
theorem eq_univ_of_succ_closed {N : ℕ} [NeZero N] {S : Set (Fin N)}
    (hne : S.Nonempty) (hclosed : ∀ x ∈ S, x + 1 ∈ S) : S = Set.univ := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hstep : ∀ k : ℕ, x₀ + (k : Fin N) ∈ S := by
    intro k
    induction k with
    | zero => simpa using hx₀
    | succ j ih =>
        have h1 : x₀ + (j : Fin N) + 1 ∈ S := hclosed _ ih
        have hc : ((j + 1 : ℕ) : Fin N) = (j : Fin N) + 1 := by push_cast; ring
        rw [hc, ← add_assoc]; exact h1
  rw [Set.eq_univ_iff_forall]
  intro y
  have hy := hstep (y - x₀).val
  have he : x₀ + (y - x₀) = y := by abel
  rwa [Fin.cast_val_eq_self, he] at hy

/-- **`cycleGraph N` is a graph of cycles** (`SimpleGraph.IsCycles`) for `N ≥ 3`:
every vertex has exactly two neighbours (`v - 1` and `v + 1`). -/
theorem cycleGraph_isCycles {N : ℕ} (hN : 3 ≤ N) : (cycleGraph N).IsCycles := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 3 := ⟨N - 3, by omega⟩
  intro v _
  have hcoe : ((cycleGraph (n + 3)).neighborSet v).ncard
      = (cycleGraph (n + 3)).degree v := by
    rw [SimpleGraph.degree, SimpleGraph.neighborFinset_def, Set.ncard_eq_toFinset_card']
  rw [hcoe]; exact cycleGraph_degree_three_le

/-- **Every cycle in `cycleGraph N` is Hamiltonian, hence has length exactly `N`**
(for `N ≥ 3`).  The graph is `2`-regular, so a cycle inside it uses both edges at
each of its vertices; its support is therefore closed under `· + 1` and spans all
of `Fin N`. -/
theorem cycleGraph_cycle_length_eq {N : ℕ} (hN : 3 ≤ N) {v : Fin N}
    {p : (cycleGraph N).Walk v v} (hp : p.IsCycle) : p.length = N := by
  haveI : NeZero N := ⟨by omega⟩
  have hcyc : (cycleGraph N).IsCycles := cycleGraph_isCycles hN
  -- The support of the cycle is closed under `· + 1`.
  have hclosed : ∀ x ∈ p.support, x + 1 ∈ p.support := by
    intro x hx
    have hxv : x ∈ p.toSubgraph.verts := (p.mem_verts_toSubgraph).mpr hx
    have hadjG : (cycleGraph N).Adj x (x + 1) := by
      rw [cycleGraph_adj']
      right
      have h1 : x + 1 - x = 1 := by abel
      rw [h1]
      obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
      simp
    have hadjSub : p.toSubgraph.Adj x (x + 1) :=
      (hp.adj_toSubgraph_iff_of_isCycles hcyc hxv (x + 1)).mpr hadjG
    exact (p.mem_verts_toSubgraph).mp (p.toSubgraph.edge_vert hadjSub.symm)
  -- Closed under successor + nonempty ⇒ the support is everything.
  have hspan : ∀ w, w ∈ p.support := by
    have hu := eq_univ_of_succ_closed (S := {x : Fin N | x ∈ p.support})
      ⟨v, p.start_mem_support⟩ hclosed
    exact fun w => Set.eq_univ_iff_forall.mp hu w
  -- A spanning cycle is a Hamiltonian cycle.
  have hham : p.IsHamiltonianCycle := by
    rw [isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one]
    refine ⟨hp, fun a => ?_⟩
    have hnodup : p.support.tail.Nodup := hp.support_nodup
    have hmem : a ∈ p.support.tail := by
      have ha : a ∈ p.support := hspan a
      rw [Walk.support_eq_cons] at ha
      rcases List.mem_cons.mp ha with h | h
      · subst h
        rw [← support_tail_of_not_nil p hp.not_nil]
        exact p.tail.end_mem_support
      · exact h
    exact le_antisymm (List.nodup_iff_count_le_one.mp hnodup a)
      (List.count_pos_iff.mpr hmem)
  simpa [Fintype.card_fin] using hham.length_eq

/-- **`cycleGraph N` has a cycle of length `k` iff `k = N`** (for `N ≥ 3`): every
cycle is Hamiltonian (length `N`), and the Hamiltonian `N`-cycle realises `k = N`.
So `cycleGraph N` contains no cycle other than its full `N`-cycle. -/
theorem cycleGraph_hasCycleOfLength_iff {N : ℕ} (hN : 3 ≤ N) (k : ℕ) :
    HasCycleOfLength (cycleGraph N) k ↔ k = N := by
  constructor
  · rintro ⟨w, p, hp, hlen⟩
    rw [← hlen]; exact cycleGraph_cycle_length_eq hN hp
  · rintro rfl
    haveI : NeZero N := ⟨by omega⟩
    exact cycleGraph_hasCycleOfLength N hN

/-- **`cycleGraph N` has extended girth exactly `N`** (for `N ≥ 3`).  Combines the
upper bound from the explicit Hamiltonian `N`-cycle with the lower bound that every
cycle spans, so no shorter cycle exists. -/
theorem cycleGraph_egirth {N : ℕ} (hN : 3 ≤ N) : (cycleGraph N).egirth = N := by
  haveI : NeZero N := ⟨by omega⟩
  apply le_antisymm
  · obtain ⟨w, p, hp, hlen⟩ := cycleGraph_hasCycleOfLength N hN
    calc (cycleGraph N).egirth ≤ (p.length : ℕ∞) := egirth_le_length hp
      _ = (N : ℕ∞) := by rw [hlen]
  · rw [le_egirth]
    intro a w hw
    rw [cycleGraph_cycle_length_eq hN hw]

/-- **`cycleGraph N` has girth exactly `N`** (for `N ≥ 3`), the `ℕ`-valued form. -/
theorem cycleGraph_girth {N : ℕ} (hN : 3 ≤ N) : (cycleGraph N).girth = N := by
  rw [SimpleGraph.girth, cycleGraph_egirth hN, ENat.toNat_coe]

/-- **Sharpness of the girth-lifting bound.**  For every `t ≥ 1`, the lower bound
`2t + 2` in `bipartite_girth_ge_of_forbidden` is *attained*: the even cycle graph
`cycleGraph (2t + 2)` is bipartite, contains no `C_{2m}` for `2 ≤ m ≤ t` (indeed no
cycle at all except the Hamiltonian `(2t+2)`-cycle), yet contains a cycle of length
exactly `2t + 2`.  Hence the girth-lifting lower bound cannot be improved. -/
theorem bipartite_girth_lifting_sharp (t : ℕ) (ht : 1 ≤ t) :
    ∃ (V : Type) (G : SimpleGraph V),
      IsBipartite G ∧
      (∀ m, 2 ≤ m → m ≤ t → ¬ HasCycleOfLength G (2 * m)) ∧
      HasCycleOfLength G (2 * t + 2) := by
  refine ⟨Fin (2 * t + 2), cycleGraph (2 * t + 2), ?_, ?_, ?_⟩
  · exact cycleGraph_isBipartite_of_even (2 * t + 2) ⟨t + 1, by ring⟩
  · intro m hm2 hmt
    rw [cycleGraph_hasCycleOfLength_iff (by omega)]
    omega
  · rw [cycleGraph_hasCycleOfLength_iff (by omega)]

/-- **Sharpness of `bipartite_C4C6_free_girth_ge_eight`.**  The `t = 3` instance:
a bipartite graph with no `C₄` and no `C₆` but containing a `C₈` really exists —
`cycleGraph 8` — so the girth bound `8` for `C₄,C₆`-free bipartite graphs is best
possible, and `C₈` is genuinely the smallest cycle such graphs can be forced to
contain. -/
theorem bipartite_C4C6_free_girth_eight_sharp :
    ∃ (V : Type) (G : SimpleGraph V),
      IsBipartite G ∧ ¬ HasCycleOfLength G 4 ∧ ¬ HasCycleOfLength G 6 ∧
      HasCycleOfLength G 8 := by
  obtain ⟨V, G, hbip, hforb, hc8⟩ := bipartite_girth_lifting_sharp 3 (by norm_num)
  refine ⟨V, G, hbip, ?_, ?_, ?_⟩
  · have := hforb 2 (by norm_num) (by norm_num); simpa using this
  · have := hforb 3 (by norm_num) (by norm_num); simpa using this
  · simpa using hc8

end Sharpness

end Erdos1080OQ03
