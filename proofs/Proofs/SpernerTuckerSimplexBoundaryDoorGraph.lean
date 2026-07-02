/-
# The raw door graph of `∂Δ^{n+1}` is the complete graph `K_{n+2}` — in every dimension

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's Lemma and Borsuk–Ulam from
abstract door-counting").

## Where this sits

`SpernerTuckerSimplexBoundaryPseudomanifold.lean` fixes a concrete `n = 3` model of the
boundary of the 4-simplex `∂Δ⁴` and discharges the engine's geometric inputs `hdoor`
(pseudomanifold: each door borders `≤ 2` top cells) and `hpair` (two distinct top cells
share `≤ 1` door) by kernel `decide`, then runs the engine's degree formula
(`SpernerTuckerDoorGraph.doorGraph_degree_eq_shared`) to compute the raw door graph as the
complete graph `K₅` (every tetrahedron has degree `4`).  That file *also* generalizes the
pseudomanifold bound `hdoor` (and its sharp `= 2` closed form) to every dimension with no
`decide` — but leaves the pairing bound `hpair` and the degree computation pinned to the
single `n = 3` instance.

This file removes that last per-dimension `decide`.  It models `∂Δ^{n+1}` for **every** `n`
and proves `hdoor`, `hpair`, and the degree formula uniformly, showing the raw door graph of
`∂Δ^{n+1}` is the complete graph `K_{n+2}` (`doorGraph_eq_top`, `simplex_degree : degree i
= n + 1`).  So the whole `∂Δ⁴` computation of the sibling file is now the `n = 3` case of a
theorem, not a stand-alone kernel check.

## The model

Vertices `{0,…,n+1} = Fin (n+2)`.  Top cells are the `n+2` facets `Sᵢ = {0,…,n+1} \ {i}`
(the facet opposite vertex `i`), indexed by `Tet n := Fin (n+2)`.  Doors are the `n`-faces;
each `n`-face omits exactly **two** vertices, so we encode a door by the 2-element set of
vertices it omits: `Door n := {s : Finset (Fin (n+2)) // s.card = 2}`.  The incidence is

> `inc i d  ⟺  i ∈ (the omitted pair of d)`,

i.e. the facet `Sᵢ` opposite `i` carries the `n`-face `d` iff `i` is one of the two vertices
`d` omits.

## What this file proves (all 0 axioms — `propext` / `Classical.choice` / `Quot.sound`
only, NO `decide`/`native_decide`/`ofReduceBool`, and no per-dimension case split)

* `hdoor`             — every door borders at most two top cells (pseudomanifold), all `n`;
* `card_incidence_eq` — in fact **exactly two** (`∂Δ^{n+1}` is closed), all `n`;
* `hpair`             — two distinct top cells share at most one door, all `n`;
* `doorGraph_eq_top`  — the raw door graph is the **complete graph** `⊤ = K_{n+2}`: any two
  distinct top cells `Sᵢ, Sⱼ` share the door omitting `{i,j}`;
* `simplex_degree`    — hence every top cell has degree `n + 1`, uniformly in `n`
  (the sibling file's `K₅` is the `n = 3` case);
* `card_shared_doors` — running the engine's degree formula backwards, each top cell has
  exactly `n + 1` shared doors, all `n` — a dimension-free count obtained for free from
  `doorGraph_degree_eq_shared` and the complete-graph degree, with no manual bijection.

Self-contained: imports Mathlib and the abstract engine.  0 sorries, 0 axioms.
-/
import Mathlib
import Proofs.SpernerTuckerDoorGraph

namespace SpernerTuckerSimplexBoundaryDoorGraph

open Finset SimpleGraph SpernerTuckerDoorGraph

variable {n : ℕ}

/-! ## The `∂Δ^{n+1}` incidence, uniformly in `n` -/

/-- The `n+2` top cells of `∂Δ^{n+1}`, indexed by the vertex each one omits: `Sᵢ` is the
facet opposite vertex `i`. -/
abbrev Tet (n : ℕ) := Fin (n + 2)

/-- The doors (`n`-faces) of `∂Δ^{n+1}`, encoded by the 2-element set of vertices they omit.
Every `n`-face of the `(n+1)`-simplex boundary omits exactly two vertices. -/
abbrev Door (n : ℕ) := {s : Finset (Fin (n + 2)) // s.card = 2}

/-- **Incidence.**  The facet `Sᵢ` opposite vertex `i` carries the door `d` iff `i` is one of
the two vertices `d` omits. -/
def inc (i : Tet n) (d : Door n) : Prop := i ∈ d.val

instance : DecidableRel (@inc n) := fun i d => by unfold inc; infer_instance

/-! ## The pseudomanifold inputs, dimension-free -/

/-- **Exact incidence: `∂Δ^{n+1}` is a closed pseudomanifold.**  Every door borders
*exactly two* top cells — the two whose omitted vertices are precisely the door's pair.  In
every dimension, no `decide`. -/
theorem card_incidence_eq (d : Door n) : #{i | inc i d} = 2 := by
  have he : ({i | inc i d} : Finset (Fin (n + 2))) = d.val := by
    ext i
    simp only [mem_filter, mem_univ, true_and, inc]
  rw [he]; exact d.property

/-- **Engine `hdoor` (the pseudomanifold `≤ 2` bound) for `∂Δ^{n+1}`, all `n`.** -/
theorem hdoor : ∀ d : Door n, #{i | inc i d} ≤ 2 :=
  fun d => (card_incidence_eq d).le

/-- **Engine `hpair`: two distinct top cells share at most one door.**  If distinct facets
`Sᵢ, Sⱼ` both carry doors `d` and `d'`, then `i, j` lie in both omitted pairs; two vertices
determine a 2-element set, so `d` and `d'` both omit exactly `{i, j}` and coincide.
Dimension-free. -/
theorem hpair : ∀ d d' : Door n, ∀ i j : Tet n, i ≠ j →
    inc i d → inc j d → inc i d' → inc j d' → d = d' := by
  intro d d' i j hij hid hjd hid' hjd'
  have hcard : ({i, j} : Finset (Fin (n + 2))).card = 2 := Finset.card_pair hij
  have hsub : ({i, j} : Finset (Fin (n + 2))) ⊆ d.val := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hid
    · exact hjd
  have hsub' : ({i, j} : Finset (Fin (n + 2))) ⊆ d'.val := by
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hid'
    · exact hjd'
  have hd : d.val = ({i, j} : Finset (Fin (n + 2))) :=
    (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, d.property])).symm
  have hd' : d'.val = ({i, j} : Finset (Fin (n + 2))) :=
    (Finset.eq_of_subset_of_card_le hsub' (by rw [hcard, d'.property])).symm
  exact Subtype.ext (hd.trans hd'.symm)

/-! ## The raw door graph is the complete graph `K_{n+2}` -/

/-- **The raw door graph of `∂Δ^{n+1}` is the complete graph.**  Any two distinct top cells
`Sᵢ, Sⱼ` share the door omitting the pair `{i, j}`, so the almost-complementary graph on the
top cells is `⊤ = K_{n+2}` — in every dimension.  (The sibling file computes the `n = 3`
case, `K₅`, by `decide`.) -/
theorem doorGraph_eq_top : doorGraph (@inc n) = ⊤ := by
  ext i j
  simp only [top_adj]
  constructor
  · rintro ⟨hne, -⟩
    exact hne
  · intro hne
    refine ⟨hne, ⟨{i, j}, Finset.card_pair hne⟩, ?_, ?_⟩
    · show i ∈ ({i, j} : Finset (Fin (n + 2)))
      exact mem_insert_self i {j}
    · show j ∈ ({i, j} : Finset (Fin (n + 2)))
      exact mem_insert_of_mem (mem_singleton_self j)

/-- **Every top cell of `∂Δ^{n+1}` has degree `n + 1`.**  Immediate from `doorGraph_eq_top`:
in `K_{n+2}` each vertex is adjacent to the other `n + 1`.  This is the dimension-free lift of
the sibling file's `simplex_degree` (`= 4` for `∂Δ⁴`). -/
theorem simplex_degree (i : Tet n) : (doorGraph (@inc n)).degree i = n + 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hnb : (doorGraph (@inc n)).neighborFinset i = univ.erase i := by
    ext w
    rw [SimpleGraph.mem_neighborFinset, mem_erase]
    have hadj : (doorGraph (@inc n)).Adj i w ↔ i ≠ w := by
      rw [doorGraph_eq_top]; exact top_adj i w
    rw [hadj]
    constructor
    · intro h
      exact ⟨fun hw => h hw.symm, mem_univ _⟩
    · intro h
      exact fun hiw => h.1 hiw.symm
  rw [hnb, Finset.card_erase_of_mem (mem_univ i), Finset.card_univ, Fintype.card_fin]
  omega

/-- **Shared-door count, dimension-free and for free from the engine.**  Running the engine's
sharp degree formula `doorGraph_degree_eq_shared` (which needs only `hdoor` and `hpair`)
backwards through `simplex_degree` shows every top cell of `∂Δ^{n+1}` has exactly `n + 1`
shared doors — every one of its `n + 1` `n`-faces is shared with the unique other top cell
across it (`∂Δ^{n+1}` is closed).  No manual counting bijection. -/
theorem card_shared_doors (i : Tet n) :
    #{d : Door n | inc i d ∧ ∃ w, w ≠ i ∧ inc w d} = n + 1 := by
  have h := doorGraph_degree_eq_shared (@inc n) hdoor hpair i
  rw [simplex_degree] at h
  convert h.symm using 3

end SpernerTuckerSimplexBoundaryDoorGraph
