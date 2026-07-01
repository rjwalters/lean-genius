/-
Erdős Problem #1018 — OQ-01 → OQ-01-OQ-01 → OQ-01-OQ-01-OQ-01 → OQ-01-OQ-01-OQ-01-OQ-01:
Degeneracy bounds the *list* chromatic number (choosability), not just the ordinary
chromatic number, and the split-graph witness keeps the bound tight.

The parent (`Erdos1018OQ01OQ01OQ01`) proves the classical greedy bound
`k`-degenerate ⟹ `(k+1)`-colourable, sharp via the complete split graph `S_{n,k}`.
This file strengthens the *upper* half of that statement along the strongest
natural axis: from ordinary colouring to **list colouring** (choosability).

**List colouring.** A graph is `k`-*choosable* when, for **every** assignment of a
palette `L v` of `≥ k` colours to each vertex `v`, one can pick `c v ∈ L v` making
`c` a proper colouring. This is strictly stronger than `k`-colourability: taking
every `L v` equal to a fixed `k`-element set recovers ordinary colouring
(`colorable_of_choosable`), but many graphs are `k`-colourable yet **not**
`k`-choosable. The least such `k` is the *list chromatic number* `χ_ℓ(G) ≥ χ(G)`.

**1. Choosability bound (`degenerate_choosable`).** Every `k`-degenerate graph is
`(k+1)`-choosable. The greedy argument of the parent goes through *verbatim* with an
arbitrary per-vertex palette in place of the global colour set `Fin (k+1)`: extract a
within-degree-`≤ k` vertex `v`, list-colour the rest by induction, then `v`'s palette
`L v` has `≥ k+1` colours while its `≤ k` already-coloured neighbours forbid at most
`k` of them, so a free colour remains **in `L v`**. Since the palette is adversarial,
this is genuinely stronger than the parent's fixed-colour greedy bound — it says
`χ_ℓ(G) ≤ k+1`, hence a fortiori `χ(G) ≤ k+1`.

**2. Tightness (`splitGraph_not_choosable`, `splitGraph_choosability`).** For `k < n`
the split graph `S_{n,k}` is `k`-degenerate (grandparent) hence `(k+1)`-choosable, but
it is **not** `k`-choosable: it is not even `k`-colourable (parent), and every
`k`-choosable graph is `k`-colourable. So `χ_ℓ(S_{n,k}) = k+1` and the choosability
bound is attained exactly by the same extremal witness that makes the edge bound and
the chromatic bound tight.

Net picture of Erdős #1018's degeneracy parameter: `k`-degenerate ⟹
`|E| ≤ k·n` **and** `χ_ℓ ≤ k+1` (so `χ ≤ k+1`), all three realised simultaneously and
sharply by `S_{n,k}`.

**Status**: VERIFIED, 0 axioms. Builds on `Erdos1018OQ01OQ01OQ01`.
Reference: https://erdosproblems.com/1018
-/

import Mathlib
import Proofs.Erdos1018OQ01OQ01OQ01

open Finset
open Erdos1018OQ01OQ01 (IsKDegenerate splitGraph splitGraph_kDegenerate)
open Erdos1018OQ01OQ01OQ01 (splitGraph_not_colorable)

namespace Erdos1018OQ01OQ01OQ01OQ01

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### List colouring (choosability) -/

/-- A finite graph `G` is **`k`-choosable** when, for every assignment of a palette
`L v` with at least `k` colours to each vertex `v` (colours drawn from an arbitrary
type `α`), there is a proper colouring `c` with `c v ∈ L v` for all `v`. The palette
is adversarial: `k`-choosability must hold for *every* such `L`, which is why it is
strictly stronger than `k`-colourability. -/
def IsChoosable (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ {α : Type} [DecidableEq α] (L : V → Finset α), (∀ v, k ≤ (L v).card) →
    ∃ c : V → α, (∀ v, c v ∈ L v) ∧ ∀ u w, G.Adj u w → c u ≠ c w

/-! ### Part 1 — greedy list colouring: `k`-degenerate ⟹ `(k+1)`-choosable -/

/-- **Core greedy list-colouring step.** For an arbitrary palette assignment `L` with
`|L v| ≥ k+1` everywhere and every vertex set `T`, there is a global assignment
`c : V → α` that is a proper colouring on `T` respecting the palettes on `T`. Strong
induction on `T`: extract a within-degree-`≤ k` vertex `v` of `T`, colour `T.erase v`
by induction, then choose for `v` a colour of `L v` avoided by its (at most `k`)
neighbours in `T` — such a colour exists because `|L v| ≥ k+1 >` the number of
forbidden colours. This is the parent's `exists_proper_coloring_on` with the fixed
colour set `Fin (k+1)` replaced by the adversarial per-vertex palette. -/
theorem exists_list_coloring_on {k : ℕ} (h : IsKDegenerate G k)
    {α : Type} [DecidableEq α] (L : V → Finset α) (hL : ∀ v, k + 1 ≤ (L v).card) :
    ∀ T : Finset V, ∃ c : V → α,
      (∀ v ∈ T, c v ∈ L v) ∧ ∀ u ∈ T, ∀ w ∈ T, G.Adj u w → c u ≠ c w := by
  have hLne : ∀ v, (L v).Nonempty := fun v => Finset.card_pos.mp (by have := hL v; omega)
  intro T
  induction T using Finset.strongInduction with
  | _ T ih =>
    rcases T.eq_empty_or_nonempty with hT | hT
    · -- empty `T`: any global function works (both requirements are vacuous)
      refine ⟨fun v => (hLne v).choose, ?_, ?_⟩
      · intro v hv; rw [hT] at hv; exact absurd hv (notMem_empty v)
      · intro u hu; rw [hT] at hu; exact absurd hu (notMem_empty u)
    · obtain ⟨v, hvT, hvdeg⟩ := h T hT
      obtain ⟨c', hc'mem, hc'proper⟩ := ih (T.erase v) (Finset.erase_ssubset hvT)
      -- colours used by `v`'s neighbours inside `T`
      set N : Finset V := T.filter (fun w => G.Adj v w) with hN
      set forbidden : Finset α := N.image c' with hforb
      have hforb_card : forbidden.card ≤ k := le_trans Finset.card_image_le hvdeg
      -- a free colour exists *inside `L v`*: `L v` has `≥ k+1` colours, `forbidden ≤ k`
      have hpos : (L v \ forbidden).Nonempty := by
        rw [Finset.sdiff_nonempty]
        intro hsub
        have := Finset.card_le_card hsub
        have := hL v
        omega
      obtain ⟨col, hcolmem⟩ := hpos
      rw [Finset.mem_sdiff] at hcolmem
      obtain ⟨hcolLv, hcolforb⟩ := hcolmem
      -- extend the colouring by giving `v` the free colour `col`
      refine ⟨fun x => if x = v then col else c' x, ?_, ?_⟩
      · -- palette membership on `T`
        intro x hx
        by_cases hxv : x = v
        · subst hxv; simpa using hcolLv
        · simp only [if_neg hxv]; exact hc'mem x (mem_erase.mpr ⟨hxv, hx⟩)
      · -- properness on `T`
        intro u hu w hw hadj
        have huw : u ≠ w := G.ne_of_adj hadj
        by_cases huv : u = v
        · -- `u = v`, so `w ≠ v` is a neighbour of `v` in `T`; its colour is forbidden
          have hwv : w ≠ v := fun hh => huw (huv.trans hh.symm)
          have hvw : G.Adj v w := huv ▸ hadj
          have hwN : w ∈ N := by rw [hN]; exact mem_filter.mpr ⟨hw, hvw⟩
          have hwf : c' w ∈ forbidden := by rw [hforb]; exact mem_image_of_mem c' hwN
          simp only [if_pos huv, if_neg hwv]
          intro hh; apply hcolforb; rw [hh]; exact hwf
        · by_cases hwv : w = v
          · -- symmetric case `w = v`
            have hvu : G.Adj v u := hwv ▸ G.symm hadj
            have huN : u ∈ N := by rw [hN]; exact mem_filter.mpr ⟨hu, hvu⟩
            have huf : c' u ∈ forbidden := by rw [hforb]; exact mem_image_of_mem c' huN
            simp only [if_neg huv, if_pos hwv]
            intro hh; apply hcolforb; rw [← hh]; exact huf
          · -- both `≠ v`: fall back to the inductive colouring on `T.erase v`
            simp only [if_neg huv, if_neg hwv]
            exact hc'proper u (mem_erase.mpr ⟨huv, hu⟩) w (mem_erase.mpr ⟨hwv, hw⟩) hadj

/-- **Choosability bound.** A `k`-degenerate graph is `(k+1)`-choosable, i.e.
`χ_ℓ(G) ≤ k+1`. This strengthens the parent's greedy bound `degenerate_colorable`
(`χ(G) ≤ k+1`) to the list setting: the same argument works against an adversarial
palette because only the *count* `≥ k+1` of available colours is used, never their
identity. -/
theorem degenerate_choosable {k : ℕ} (h : IsKDegenerate G k) : IsChoosable G (k + 1) := by
  intro α _inst L hL
  obtain ⟨c, hcmem, hcproper⟩ := exists_list_coloring_on G h L hL univ
  exact ⟨c, fun v => hcmem v (mem_univ v),
    fun u w hadj => hcproper u (mem_univ u) w (mem_univ w) hadj⟩

/-- **Choosability generalises ordinary colouring.** Every `k`-choosable graph is
`k`-colourable: instantiate the adversarial palette with the constant `k`-element set
`Fin k`. Thus `χ ≤ χ_ℓ`, and `degenerate_choosable` really is a strengthening of the
parent's chromatic bound. -/
theorem colorable_of_choosable {k : ℕ} (h : IsChoosable G k) : G.Colorable k := by
  obtain ⟨c, _hcmem, hcproper⟩ :=
    h (fun _ : V => (univ : Finset (Fin k))) (fun v => by simp)
  exact ⟨SimpleGraph.Coloring.mk c (fun {u w} hadj => hcproper u w hadj)⟩

/-! ### Part 2 — tightness: the split graph is not `k`-choosable -/

/-- **Tightness (lower bound).** For `k < n` the split graph `S_{n,k}` is *not*
`k`-choosable. It is not even `k`-colourable (parent `splitGraph_not_colorable`, via
its `(k+1)`-clique), and every `k`-choosable graph is `k`-colourable, so it cannot be
`k`-choosable either. -/
theorem splitGraph_not_choosable {n k : ℕ} (hk : k < n) :
    ¬ IsChoosable (splitGraph n k) k := by
  intro h
  exact splitGraph_not_colorable hk (colorable_of_choosable (splitGraph n k) h)

/-- **List chromatic number of the split graph.** For `k < n`, `S_{n,k}` is
`(k+1)`-choosable (it is `k`-degenerate, Part 1) but not `k`-choosable (Part 2). So
`χ_ℓ(S_{n,k}) = k+1` exactly: the choosability bound `degenerate_choosable` is sharp,
refining the parent's `splitGraph_chromatic` (`χ = k+1`) on the same witness. -/
theorem splitGraph_choosability {n k : ℕ} (hk : k < n) :
    IsChoosable (splitGraph n k) (k + 1) ∧ ¬ IsChoosable (splitGraph n k) k :=
  ⟨degenerate_choosable (splitGraph n k) (splitGraph_kDegenerate n k),
    splitGraph_not_choosable hk⟩

end Erdos1018OQ01OQ01OQ01OQ01

