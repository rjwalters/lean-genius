/-
# Door-incidence ⟹ max-degree ≤ 2: the abstract bridge for n ≥ 2 Tucker

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's Lemma and Borsuk–Ulam
from abstract door-counting").

## Where this sits

The companion file `SpernerTuckerPathFollowing.lean` isolates the combinatorial
heart of the Freund–Todd / Prescott–Su path-following proof of Tucker's lemma:
on a finite simple graph of **maximum degree ≤ 2** (a disjoint union of paths and
cycles), the number of degree-1 vertices is even, so an odd number of *boundary*
endpoints forces an *interior* endpoint — a complementary simplex.

That engine takes the hypothesis `∀ v, G.degree v ≤ 2` as a **black box**.  But the
whole point of the parent's "door-counting" framing is that this bound is not an
accident: it comes from the *door incidence structure*.  The vertices of `G` are
the **almost-complementary simplices**; the edges are shared **doors**
(complementary facets).  The geometric facts that make `G` a paths-and-cycles
graph are precisely:

* each almost-complementary simplex has **at most two** doors, and
* each door is shared by **at most two** simplices.

This file closes exactly that gap, fully abstractly.  Given any finite
*door-incidence relation* `inc : V → D → Prop` (`inc v d` = "simplex `v` has door
`d`") satisfying those two `≤ 2` bounds, the induced graph

> `v ~ w  ⟺  v ≠ w ∧ they share a door`

has maximum degree ≤ 2 (`doorGraph_degree_le_two`).  The proof is a clean counting
injection: the neighbours of `v` inject into the doors of `v` (each neighbour is
reached through a shared door, and a single door cannot connect `v` to two
distinct neighbours without being incident to three simplices).

Chaining this with the handshaking lemma gives the full **Tucker-from-door-
counting** statement, self-contained over an arbitrary finite incidence relation:

* `doorGraph_even_endpoints` — the number of degree-1 vertices (path endpoints) is
  even;
* `tucker_door_count` — door structure + an **odd** number of boundary endpoints
  ⟹ an **odd** number of interior (complementary) simplices — the quantitative
  Tucker statement, the analogue of the parent `sperner_parity`;
* `exists_complementary_simplex` — hence at least one complementary simplex exists.

This realizes the OQ's title literally: the `degree ≤ 2` hypothesis of the
path-following engine is *derived from abstract door-counting*, not assumed.

Self-contained: imports only Mathlib.  0 sorries, 0 axioms
(`propext` / `Classical.choice` / `Quot.sound` only — NO `ofReduceBool`).
-/
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic

namespace SpernerTuckerDoorGraph

open Finset SimpleGraph

variable {V D : Type*} [Fintype V] [Fintype D] [DecidableEq V]
  (inc : V → D → Prop) [DecidableRel inc]

/-- The **almost-complementary-simplex graph** induced by a door-incidence
relation `inc`.  Two simplices are adjacent when they are distinct and share a
door (a complementary facet). -/
def doorGraph : SimpleGraph V where
  Adj v w := v ≠ w ∧ ∃ d, inc v d ∧ inc w d
  symm := by
    rintro v w ⟨hne, d, hv, hw⟩
    exact ⟨hne.symm, d, hw, hv⟩
  loopless := by
    rintro v ⟨hne, _⟩
    exact hne rfl

instance : DecidableRel (doorGraph inc).Adj := fun v w =>
  decidable_of_iff (v ≠ w ∧ ∃ d, inc v d ∧ inc w d) Iff.rfl

/-- **The door-counting degree bound.**  If every door is incident to at most two
simplices and every simplex has at most two doors, then the almost-complementary
graph has maximum degree ≤ 2 — it is a disjoint union of paths and cycles, exactly
the hypothesis the path-following engine needs.

Proof: the neighbours of `v` inject into the doors of `v`.  Each neighbour `w` is
reached through some shared door `g w` with `inc v (g w)` and `inc w (g w)`.  This
map is injective on neighbours: if two distinct neighbours `w₁ ≠ w₂` shared the
same door `d`, then `v, w₁, w₂` would be three distinct simplices all incident to
`d`, contradicting the ≤ 2 bound on door incidences.  Hence
`degree v ≤ #(doors of v) ≤ 2`. -/
theorem doorGraph_degree_le_two
    (hdoor : ∀ d, #{v | inc v d} ≤ 2)
    (hsimplex : ∀ v, #{d | inc v d} ≤ 2)
    (v : V) : (doorGraph inc).degree v ≤ 2 := by
  classical
  refine le_trans ?_ (hsimplex v)
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  rcases isEmpty_or_nonempty D with hD | hD
  · -- No doors at all: `v` has no neighbours.
    have : (doorGraph inc).neighborFinset v = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro w hw
      rw [SimpleGraph.mem_neighborFinset] at hw
      obtain ⟨_, d, _, _⟩ := hw
      exact hD.false d
    rw [this]; exact Nat.zero_le _
  · haveI : Nonempty D := hD
    -- The shared-door witness for each neighbour.
    set s := (doorGraph inc).neighborFinset v with hs
    have key : ∀ w ∈ s, ∃ d, inc v d ∧ inc w d := by
      intro w hw
      rw [hs, SimpleGraph.mem_neighborFinset] at hw
      exact hw.2
    let g : V → D := fun w =>
      if h : ∃ d, inc v d ∧ inc w d then h.choose else Classical.arbitrary D
    -- `g` lands in the doors of `v`.
    have hmem : ∀ w ∈ s, g w ∈ ({d | inc v d} : Finset D) := by
      intro w hw
      have hex : ∃ d, inc v d ∧ inc w d := key w hw
      simp only [g, dif_pos hex, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hex.choose_spec.1
    -- `g` is injective on the neighbours.
    have hinj : Set.InjOn g s := by
      intro w₁ hw₁ w₂ hw₂ heq
      rw [Finset.mem_coe] at hw₁ hw₂
      have hex₁ : ∃ d, inc v d ∧ inc w₁ d := key w₁ hw₁
      have hex₂ : ∃ d, inc v d ∧ inc w₂ d := key w₂ hw₂
      -- The shared door reached from each neighbour.
      have hg₁ : inc v (g w₁) ∧ inc w₁ (g w₁) := by
        simp only [g, dif_pos hex₁]; exact hex₁.choose_spec
      have hg₂ : inc v (g w₂) ∧ inc w₂ (g w₂) := by
        simp only [g, dif_pos hex₂]; exact hex₂.choose_spec
      set d := g w₁ with hd
      -- After `set`, `heq : d = g w₂` and `hg₁ : inc v d ∧ inc w₁ d`.
      have hvd : inc v d := hg₁.1
      have hw₁d : inc w₁ d := hg₁.2
      have hw₂d : inc w₂ d := by rw [heq]; exact hg₂.2
      -- `v ≠ w₁`, `v ≠ w₂` since neighbours.
      have hadj₁ : (doorGraph inc).Adj v w₁ := by
        rw [← SimpleGraph.mem_neighborFinset, ← hs]; exact hw₁
      have hadj₂ : (doorGraph inc).Adj v w₂ := by
        rw [← SimpleGraph.mem_neighborFinset, ← hs]; exact hw₂
      have hvw₁ : v ≠ w₁ := hadj₁.ne
      have hvw₂ : v ≠ w₂ := hadj₂.ne
      by_contra hne
      -- Three distinct simplices `{v, w₁, w₂}` incident to door `d`.
      have hsub : ({v, w₁, w₂} : Finset V) ⊆ ({u | inc u d} : Finset V) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hx with rfl | rfl | rfl
        · exact hvd
        · exact hw₁d
        · exact hw₂d
      have hcard3 : ({v, w₁, w₂} : Finset V).card = 3 := by
        rw [Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              push_neg; exact ⟨hvw₁, hvw₂⟩),
            Finset.card_insert_of_notMem (by
              simp only [Finset.mem_singleton]; exact hne),
            Finset.card_singleton]
      have := Finset.card_le_card hsub
      rw [hcard3] at this
      exact absurd (this.trans (hdoor d)) (by norm_num)
    -- Injection ⟹ card neighbours ≤ card doors of `v`.
    exact Finset.card_le_card_of_injOn g hmem hinj

/-- **Handshaking on the door graph.**  Under the two door-incidence bounds the
number of degree-1 vertices — the *path endpoints* of the almost-complementary
graph — is even. -/
theorem doorGraph_even_endpoints
    (hdoor : ∀ d, #{v | inc v d} ≤ 2)
    (hsimplex : ∀ v, #{d | inc v d} ≤ 2) :
    Even #{v | (doorGraph inc).degree v = 1} := by
  classical
  have hdeg := doorGraph_degree_le_two inc hdoor hsimplex
  have hset : ({v | (doorGraph inc).degree v = 1} : Finset V)
      = ({v | Odd ((doorGraph inc).degree v)} : Finset V) := by
    apply Finset.filter_congr
    intro v _
    rw [Nat.odd_iff]
    have := hdeg v
    omega
  rw [hset]
  exact (doorGraph inc).even_card_odd_degree_vertices

/-- **Tucker's lemma from abstract door-counting (quantitative form).**  Let `B`
be a "boundary" predicate on the simplices.  Under the two door-incidence bounds,
if an **odd** number of path endpoints lie on the boundary, then an **odd** number
of path endpoints are *interior* — the genuinely complementary simplices.

This is the door-counting analogue of the parent `sperner_parity` (`#panchromatic
≡ #boundary-doors mod 2`): the antipodal boundary condition supplies the odd
boundary count (via the inductive lower-dimensional Tucker statement) and the door
structure supplies everything else. -/
theorem tucker_door_count {B : V → Prop} [DecidablePred B]
    (hdoor : ∀ d, #{v | inc v d} ≤ 2)
    (hsimplex : ∀ v, #{d | inc v d} ≤ 2)
    (hbdry : Odd #{v | (doorGraph inc).degree v = 1 ∧ B v}) :
    Odd #{v | (doorGraph inc).degree v = 1 ∧ ¬ B v} := by
  classical
  have heven : Even #{v | (doorGraph inc).degree v = 1} :=
    doorGraph_even_endpoints inc hdoor hsimplex
  have e1 : #(({v | (doorGraph inc).degree v = 1} : Finset V).filter B)
      = #{v | (doorGraph inc).degree v = 1 ∧ B v} := by rw [Finset.filter_filter]
  have e2 : #(({v | (doorGraph inc).degree v = 1} : Finset V).filter (fun a => ¬ B a))
      = #{v | (doorGraph inc).degree v = 1 ∧ ¬ B v} := by rw [Finset.filter_filter]
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := ({v | (doorGraph inc).degree v = 1} : Finset V)) (p := B)
  rw [e1, e2] at hsplit
  rw [Nat.even_iff] at heven
  rw [Nat.odd_iff] at hbdry ⊢
  omega

/-- **Existence form.**  Under the door-incidence bounds, an odd number of boundary
endpoints forces an *interior* degree-1 vertex — a complementary simplex.  This is
Tucker's lemma proved through the abstract door-counting engine. -/
theorem exists_complementary_simplex {B : V → Prop} [DecidablePred B]
    (hdoor : ∀ d, #{v | inc v d} ≤ 2)
    (hsimplex : ∀ v, #{d | inc v d} ≤ 2)
    (hbdry : Odd #{v | (doorGraph inc).degree v = 1 ∧ B v}) :
    ∃ v, (doorGraph inc).degree v = 1 ∧ ¬ B v := by
  classical
  have hodd : Odd #{v | (doorGraph inc).degree v = 1 ∧ ¬ B v} :=
    tucker_door_count inc hdoor hsimplex hbdry
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hodd.pos
  rw [Finset.mem_filter] at hv
  exact ⟨v, hv.2⟩

/-- **Sharp degree formula: degree = number of shared doors.**  `doorGraph_degree_le_two`
bounds the degree by `2` via the doors of `v`.  Under two clean geometric facts —
each door joins at most two simplices (`hdoor`) and two distinct simplices share at
most one door (`hpair`) — the bound is in fact an *equality* with the number of `v`'s
**shared** doors (doors some *other* simplex also carries):

> `(doorGraph inc).degree v = #{ d | inc v d ∧ ∃ w ≠ v, inc w d }`.

The map "neighbour `w` ↦ the door it shares with `v`" is a bijection onto the shared
doors: it lands in the shared doors and is injective by `hdoor` (a door joining `v` to
two neighbours would touch three simplices), and surjective by `hpair` (the door's
other endpoint is a neighbour whose shared door is forced to be that very door).

This turns "`v` is a path endpoint" (`degree v = 1`) into the purely local door
statement "`v` has exactly one shared door", which is the interface the geometric
construction of `inc` targets. -/
theorem doorGraph_degree_eq_shared
    (hdoor : ∀ d, #{v | inc v d} ≤ 2)
    (hpair : ∀ d d' : D, ∀ v w : V, v ≠ w →
      inc v d → inc w d → inc v d' → inc w d' → d = d')
    (v : V) :
    (doorGraph inc).degree v = #{d | inc v d ∧ ∃ w, w ≠ v ∧ inc w d} := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  set s := (doorGraph inc).neighborFinset v with hs
  -- Each neighbour shares a door with `v`.
  have key : ∀ w ∈ s, ∃ d, inc v d ∧ inc w d := by
    intro w hw
    rw [hs, SimpleGraph.mem_neighborFinset] at hw
    exact hw.2
  -- Each neighbour is distinct from `v`.
  have hne : ∀ w ∈ s, v ≠ w := by
    intro w hw
    rw [hs, SimpleGraph.mem_neighborFinset] at hw
    exact hw.1
  rcases isEmpty_or_nonempty D with hD | hD
  · -- No doors: no neighbours and no shared doors.
    have h1 : s = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro w hw; obtain ⟨d, _, _⟩ := key w hw; exact hD.false d
    have h2 : ({d | inc v d ∧ ∃ w, w ≠ v ∧ inc w d} : Finset D) = ∅ :=
      Finset.eq_empty_of_isEmpty _
    rw [h1, h2, Finset.card_empty, Finset.card_empty]
  · haveI : Nonempty D := hD
    -- The shared-door witness map.
    let g : V → D := fun w =>
      if h : ∃ d, inc v d ∧ inc w d then h.choose else Classical.arbitrary D
    have hgspec : ∀ w ∈ s, inc v (g w) ∧ inc w (g w) := by
      intro w hw
      have hex := key w hw
      simp only [g, dif_pos hex]; exact hex.choose_spec
    refine Finset.card_bij (fun w _ => g w) ?_ ?_ ?_
    · -- lands in the shared doors
      intro w hw
      obtain ⟨hv, hw'⟩ := hgspec w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hv, w, (hne w hw).symm, hw'⟩
    · -- injective: a shared door of two neighbours touches three simplices
      intro w₁ h₁ w₂ h₂ heq
      dsimp only at heq
      obtain ⟨hv₁, hw₁⟩ := hgspec w₁ h₁
      obtain ⟨_, hw₂⟩ := hgspec w₂ h₂
      rw [heq] at hw₁
      by_contra hww
      have hsub : ({v, w₁, w₂} : Finset V) ⊆ ({u | inc u (g w₂)} : Finset V) := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hx with rfl | rfl | rfl
        · exact (hgspec w₂ h₂).1
        · exact hw₁
        · exact hw₂
      have hcard3 : ({v, w₁, w₂} : Finset V).card = 3 := by
        rw [Finset.card_insert_of_notMem (by
              simp only [Finset.mem_insert, Finset.mem_singleton]
              push_neg; exact ⟨hne w₁ h₁, hne w₂ h₂⟩),
            Finset.card_insert_of_notMem (by
              simp only [Finset.mem_singleton]; exact hww),
            Finset.card_singleton]
      have := Finset.card_le_card hsub
      rw [hcard3] at this
      exact absurd (this.trans (hdoor (g w₂))) (by norm_num)
    · -- surjective: the door's other endpoint is a neighbour, with that very shared door
      intro d hd
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd
      obtain ⟨hvd, w, hwv, hwd⟩ := hd
      have hws : w ∈ s := by
        rw [hs, SimpleGraph.mem_neighborFinset]
        exact ⟨hwv.symm, d, hvd, hwd⟩
      refine ⟨w, hws, ?_⟩
      obtain ⟨hvg, hwg⟩ := hgspec w hws
      exact hpair (g w) d v w hwv.symm hvg hwg hvd hwd

end SpernerTuckerDoorGraph
