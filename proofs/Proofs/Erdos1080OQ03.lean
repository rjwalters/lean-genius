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
four cross edges present.  The two lemmas below establish this equivalence,
discharging the `c4_free_iff_no_K22` placeholder that the parent problem file
(`Erdos1080Problem.lean`) still carries as a `sorry`.

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

end Erdos1080OQ03
