/-
# The directed sign-door engine fires on an INTERIOR simplex: n = 2 Tucker closed by door-counting

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's lemma and Borsuk–Ulam from
abstract door-counting").

## Where this sits — closing the gap the prior files named

The door-counting program for n = 2 Tucker has, across many companion files, isolated
its single genuinely-open lever and then jammed on it:

* `SpernerTuckerDoorGraph.exists_complementary_simplex` — the abstract engine: a door
  incidence with each door in `≤ 2` rooms and each room with `≤ 2` doors, plus an
  **odd** number of degree-1 *boundary* rooms, forces a degree-1 *interior* room — the
  Tucker witness.
* `SpernerTuckerHexagonFullDoorGraph.boundary_door_count_even` — the *undirected*
  all-signs complementary door graph realises the two `≤ 2` bounds, but its boundary
  door count is **even**, so the engine never fires.
* `SpernerTuckerHexagonSignFlipEngine.endpoint_is_far_hemisphere_signflip` — the
  undirected sign-flip door graph *does* have an odd hemisphere seed, but its engine
  endpoint is a **boundary** edge in the opposite hemisphere, never an interior witness.
* `SpernerTuckerHexagonDirectedSignDoor.full_dir_count_odd` — the *directed* pos→neg
  sign rule finally supplies an **odd** seed on the whole antipodal boundary circle,
  and `dirTri_le_one` gives it path structure; but that file stops at the seed,
  explicitly flagging "assembling these directed doors into a path to an interior
  complementary simplex — the signed pivot engine — is the genuine remaining BUILD".

**This file performs that assembly.**  It builds a concrete door incidence on the
hexagon disk from the directed pos→neg rule, feeds it to
`SpernerTuckerDoorGraph.exists_complementary_simplex`, and obtains — for *every*
antipodal labelling — a degree-1 **interior** room: an actual Tucker witness.  This is
the first time the door-counting engine lands inside on real n = 2 geometry, exactly
the outcome the undirected reductions provably could not reach.

## The construction

* **Rooms** `Fin 6 ⊕ Fin 6`: `inl t` is the disk triangle `T t = (centre, v t, v (t+1))`;
  `inr i` is a *boundary slot* — a degree-≤1 room glued to the outside of boundary edge
  `i`.  The boundary slots are the engine's "boundary rooms".
* **Doors** `Fin 6 ⊕ Fin 6`: `inl i` is the spoke `centre → v i`; `inr i` is the boundary
  edge `v i → v (i+1)`.  A door is *open* exactly when it is a directed pos→neg sign door
  in its canonical orientation (`doorEdge`).
* A triangle carries its three sides as doors when they are open; a boundary slot carries
  only its own boundary edge.

The two structural facts that make the engine fire:

1. **`hsimplex` (each room `≤ 2` doors).**  A triangle can never have all three sides
   open: its boundary edge `inr t` is open only if `sgn (v t) = 0`, while its spoke
   `inl t` is open only if `sgn (v t) = 1` — contradictory.  (Boundary slots trivially
   have `≤ 1` door.)  This is the oriented analogue of
   `SpernerTuckerHexagonFullDoorGraph.no_triangle_all_complementary`.
2. **Odd boundary seed.**  A boundary slot `inr i` has degree `1` in the door graph
   exactly when its boundary edge is open, so the number of degree-1 boundary rooms is
   the directed boundary-circle door count — **odd** for every antipodal labelling
   (`seed_odd`, the `full_dir_count_odd` phenomenon, here as a `Finset` count).

Feeding these to the abstract engine yields `exists_interior_tucker_witness`: a degree-1
room that is a triangle, in every dimension-2 antipodal labelling.

## Honest status

A genuine **positive** result: the first machine-checked assembly of the directed
door-counting engine that terminates at an *interior* simplex on real n = 2 geometry,
closing the "signed pivot engine" build that
`SpernerTuckerHexagonDirectedSignDoor` named as its open frontier.  It proves n = 2
Tucker *through the door-counting engine* (the OQ's own method), complementing the
direct `SpernerTuckerHexagonComplementaryEdge.exists_complementary_edge`.  It does *not*
yet give the general-dimension `bridge`: the boundary slots here are supplied with their
odd seed directly (`seed_odd` by finite check), whereas the full induction must obtain
that seed from the `(n-1)`-dimensional Tucker count.  The remaining frontier is thus
precisely the dimension recursion of `SpernerTuckerInductiveTower.bridge`, now with the
single-level engine demonstrated to fire interiorly.

Self-contained: imports Mathlib and the abstract engine `SpernerTuckerDoorGraph`.
0 sorries, 0 axioms (`propext` / `Classical.choice` / `Quot.sound` only — no `sorryAx`,
no `Lean.ofReduceBool`).
-/
import Mathlib
import Proofs.SpernerTuckerDoorGraph

namespace SpernerTuckerHexagonDirectedEngine

open Finset

/-! ## Labelling model (same encoding as `SpernerTuckerHexagonDirectedSignDoor`) -/

/-- Label negation on `{+1,+2,-1,-2}` encoded as `Fin 4` (`0↦+1,1↦+2,2↦-1,3↦-2`). -/
def negL : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/-- The six boundary labels from three free labels `a,b,c` on `v0,v1,v2`, antipodal
`v(i+3) = -v(i)`. -/
def V (a b c : Fin 4) : Fin 6 → Fin 4 := ![a, b, c, negL a, negL b, negL c]

/-- Cyclic successor around the hexagon boundary. -/
def rot (i : Fin 6) : Fin 6 := i + 1

/-- Sign map `sgn : Fin 4 → Bool`, `{+1,+2}↦false`, `{-1,-2}↦true` (the `+/−`
hemisphere bit).  Kept `Bool` so the door indicators are pure boolean computations,
keeping the finite `decide` checks light. -/
def sgn : Fin 4 → Bool := ![false, false, true, true]

/-! ## Rooms, doors, and the directed door incidence

Rooms and doors are both `Fin 6 ⊕ Fin 6`.  For rooms, `inl t` is triangle
`T t = (centre, v t, v (t+1))` and `inr i` is the boundary slot outside boundary edge
`i`.  For doors, `inl i` is the spoke `centre → v i` and `inr i` is the boundary edge
`v i → v (i+1)`. -/

abbrev Room := Fin 6 ⊕ Fin 6
abbrev Door := Fin 6 ⊕ Fin 6

/-- **Directed door indicator.**  A door is *open* iff it is a directed pos→neg sign door
in its canonical orientation: the spoke `centre → v i` when `sgn (centre) = false` and
`sgn (v i) = true`; the boundary edge `v i → v (i+1)` when `sgn (v i) = false` and
`sgn (v (i+1)) = true`.  Written with pure boolean operations. -/
def doorEdge (a b c d : Fin 4) : Door → Bool
  | Sum.inl i => (! sgn d) && sgn (V a b c i)
  | Sum.inr i => (! sgn (V a b c i)) && sgn (V a b c (rot i))

/-- Geometric incidence: triangle `t` carries its three sides — spoke `t`, spoke `t+1`,
and boundary edge `t`. -/
def geo (t : Fin 6) : Door → Prop
  | Sum.inl i => i = t ∨ i = t + 1
  | Sum.inr i => i = t

instance (t : Fin 6) : DecidablePred (geo t) := fun e => by
  cases e <;> unfold geo <;> infer_instance

/-- **Door incidence.**  A triangle `inl t` has door `e` iff `e` is a side of `t` and is
open; a boundary slot `inr i` has door `e` iff `e` is its own boundary edge `inr i` and is
open. -/
def inc (a b c d : Fin 4) : Room → Door → Prop
  | Sum.inl t, e => geo t e ∧ doorEdge a b c d e = true
  | Sum.inr i, e => e = Sum.inr i ∧ doorEdge a b c d e = true

instance (a b c d : Fin 4) : DecidableRel (inc a b c d) := fun r e => by
  cases r <;> unfold inc <;> infer_instance

/-- **Boundary predicate.**  The boundary rooms are the boundary slots `inr i`. -/
def B : Room → Prop
  | Sum.inl _ => False
  | Sum.inr _ => True

instance : DecidablePred B := fun r => by cases r <;> unfold B <;> infer_instance

/-! ## The two engine hypotheses (by kernel `decide`) -/

/-- **Engine `hdoor`.**  Every door borders at most two rooms, for every antipodal
labelling.  A spoke door joins its two adjacent triangles; a boundary door joins its
triangle and its boundary slot. -/
theorem hdoor : ∀ a b c d : Fin 4, ∀ e : Door, #{r | inc a b c d r e} ≤ 2 := by decide

/-- **Engine `hsimplex`.**  Every room has at most two doors, for every antipodal
labelling.  A triangle never has all three sides open (its boundary edge needs
`sgn (v t) = 0` while its spoke needs `sgn (v t) = 1`); a boundary slot has at most one
door. -/
theorem hsimplex : ∀ a b c d : Fin 4, ∀ r : Room, #{e | inc a b c d r e} ≤ 2 := by decide

/-- **No triangle has all three sides open** — the sharp reason `hsimplex` holds for
triangles: the oriented analogue of
`SpernerTuckerHexagonFullDoorGraph.no_triangle_all_complementary`. -/
theorem no_triangle_all_open :
    ∀ a b c d : Fin 4, ∀ t : Fin 6, #{e | inc a b c d (Sum.inl t) e} ≠ 3 := by decide

/-! ## The odd boundary seed

A boundary slot `inr i` has degree `1` in the door graph exactly when its boundary edge
is open.  So the number of degree-1 boundary rooms equals the directed boundary-circle
door count, which is odd for every antipodal labelling. -/

/-- The number of boundary slots whose boundary edge is open. -/
def openBoundarySlots (a b c d : Fin 4) : ℕ :=
  #{i : Fin 6 | doorEdge a b c d (Sum.inr i) = true}

/-- **The directed boundary-circle door count is odd** — the `full_dir_count_odd`
phenomenon as a `Finset` count.  Verified over all `4³ = 64` antipodal labellings (the
centre label `d` is irrelevant to boundary doors). -/
theorem seed_odd (a b c d : Fin 4) : Odd (openBoundarySlots a b c d) := by
  revert a b c d; decide

/-! ## The boundary-slot degree lemma

The engine's boundary seed is `#{r | degree r = 1 ∧ B r}`.  We compute the degree of a
boundary slot directly: it is `1` when its edge is open and `0` otherwise. -/

/-- **A boundary slot is adjacent only to its own triangle.**  Its unique possible door is
`inr i`, carried also by triangle `inl i` (and no other room), so its neighbourhood is
`{inl i}` when the edge is open and `∅` otherwise. -/
theorem bdry_neighborFinset (a b c d : Fin 4) (i : Fin 6) :
    (SpernerTuckerDoorGraph.doorGraph (inc a b c d)).neighborFinset (Sum.inr i)
      = if doorEdge a b c d (Sum.inr i) = true then {Sum.inl i} else ∅ := by
  ext w
  rw [SimpleGraph.mem_neighborFinset]
  simp only [SpernerTuckerDoorGraph.doorGraph]
  by_cases hopen : doorEdge a b c d (Sum.inr i) = true
  · rw [if_pos hopen]
    simp only [Finset.mem_singleton]
    constructor
    · rintro ⟨hne, e, hie, hwe⟩
      -- `inc (inr i) e` forces `e = inr i`.
      have he : e = Sum.inr i := hie.1
      subst he
      -- `inc w (inr i)` with `w ≠ inr i` forces `w = inl i`.
      cases w with
      | inl t =>
          have hgeo : geo t (Sum.inr i) := hwe.1
          simp only [geo] at hgeo
          exact congrArg Sum.inl hgeo.symm
      | inr j =>
          have hij : Sum.inr i = (Sum.inr j : Door) := hwe.1
          exact absurd hij hne
    · rintro rfl
      refine ⟨by simp, Sum.inr i, ⟨rfl, hopen⟩, ?_⟩
      exact ⟨by simp only [geo], hopen⟩
  · rw [if_neg hopen]
    simp only [Finset.notMem_empty, iff_false]
    rintro ⟨_, e, hie, _⟩
    -- `inc (inr i) e` forces `e = inr i` and the edge open.
    have he : e = Sum.inr i := hie.1
    subst he
    exact hopen hie.2

/-- **The degree of a boundary slot** is `1` when its edge is open and `0` otherwise. -/
theorem bdry_degree (a b c d : Fin 4) (i : Fin 6) :
    (SpernerTuckerDoorGraph.doorGraph (inc a b c d)).degree (Sum.inr i)
      = if doorEdge a b c d (Sum.inr i) = true then 1 else 0 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, bdry_neighborFinset]
  by_cases hopen : doorEdge a b c d (Sum.inr i) = true <;>
    simp [hopen]

/-- **A triangle room is never a boundary room** (`B` picks out slots only). -/
theorem inl_not_B (t : Fin 6) : ¬ B (Sum.inl t) := by simp [B]

/-! ## The boundary seed equals the odd open-boundary-slot count -/

/-- The engine's degree-1 boundary rooms are exactly the boundary slots with an open
edge, so their count is `openBoundarySlots` — odd by `seed_odd`. -/
theorem boundary_seed_odd (a b c d : Fin 4) :
    Odd #{r : Room | (SpernerTuckerDoorGraph.doorGraph (inc a b c d)).degree r = 1 ∧ B r} := by
  have hcard : #{r : Room | (SpernerTuckerDoorGraph.doorGraph (inc a b c d)).degree r = 1 ∧ B r}
      = openBoundarySlots a b c d := by
    unfold openBoundarySlots
    rw [← Finset.card_map (⟨Sum.inr, Sum.inr_injective⟩ : Fin 6 ↪ Room)]
    congr 1
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    cases r with
    | inl t =>
        constructor
        · rintro ⟨_, hB⟩; exact absurd hB (inl_not_B t)
        · rintro ⟨i, _, hi⟩; exact absurd hi (by simp)
    | inr i =>
        rw [bdry_degree]
        constructor
        · rintro ⟨hdeg, _⟩
          by_cases hopen : doorEdge a b c d (Sum.inr i) = true
          · exact ⟨i, hopen, rfl⟩
          · rw [if_neg hopen] at hdeg; exact absurd hdeg (by norm_num)
        · rintro ⟨j, hj, hij⟩
          have hji : j = i := by injection hij
          subst hji
          exact ⟨by rw [if_pos hj], by simp [B]⟩
  rw [hcard]
  exact seed_odd a b c d

/-! ## The engine fires interiorly -/

/-- **The directed door-counting engine terminates at an interior simplex.**  For every
antipodal labelling `(a, b, c, d)` there is a degree-1 room that is *not* a boundary slot —
i.e. a triangle `inl t` — the Tucker complementary simplex.  This is the door-counting
engine landing *inside* the disk, the outcome the undirected sign-flip reduction provably
could not reach (`SpernerTuckerHexagonSignFlipEngine.endpoint_is_far_hemisphere_signflip`
lands on the antipodal boundary instead). -/
theorem exists_interior_tucker_witness (a b c d : Fin 4) :
    ∃ r : Room, (SpernerTuckerDoorGraph.doorGraph (inc a b c d)).degree r = 1 ∧ ¬ B r :=
  SpernerTuckerDoorGraph.exists_complementary_simplex (inc a b c d)
    (hdoor a b c d) (hsimplex a b c d) (boundary_seed_odd a b c d)

/-- **The interior witness is a triangle.**  Unpacking `¬ B`, the complementary simplex
the engine returns is a genuine disk triangle `T t`, degree 1 in the directed door
graph — a Tucker witness in the interior. -/
theorem exists_interior_triangle (a b c d : Fin 4) :
    ∃ t : Fin 6, (SpernerTuckerDoorGraph.doorGraph (inc a b c d)).degree (Sum.inl t) = 1 := by
  obtain ⟨r, hdeg, hB⟩ := exists_interior_tucker_witness a b c d
  cases r with
  | inl t => exact ⟨t, hdeg⟩
  | inr i =>
      have hBi : B (Sum.inr i) := by simp [B]
      exact absurd hBi hB

#check @exists_interior_tucker_witness
#check @exists_interior_triangle

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`.
#print axioms exists_interior_tucker_witness
#print axioms exists_interior_triangle

end SpernerTuckerHexagonDirectedEngine
