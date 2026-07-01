/-
Erdős Problem #1018 — OQ-01 → OQ-01-OQ-01 → OQ-01-OQ-01-OQ-01:
Degeneracy bounds the chromatic number (greedy colouring), and the split-graph
witness makes the bound tight.

The grandparent (`Erdos1018OQ01`) extracts a dense induced subgraph from an edge
count; the parent (`Erdos1018OQ01OQ01`) pins the *edge* side of the degeneracy
threshold (`k`-degenerate ⟹ `≤ k·n` edges, sharp via the complete split graph
`S_{n,k}`). This file turns the same degeneracy hypothesis into the classical
*colouring* consequence, on the other structural axis:

**1. Greedy colouring (`degenerate_colorable`).** Every `k`-degenerate graph is
`(k+1)`-colourable. Proof by strong induction on the vertex set using exactly the
degeneracy hypothesis: pick a vertex `v` of within-degree `≤ k`, colour the rest
by induction, then `v` sees at most `k` colours among its `≤ k` neighbours, so one
of the `k+1` colours is free. No degeneracy ordering is materialised — the
low-degree vertex is produced afresh from `IsKDegenerate` at each step, and the
colouring is built as a single global function `V → Fin (k+1)`.

**2. Tightness (`splitGraph_not_colorable`, `splitGraph_chromatic`).** For
`k < n` the split graph `S_{n,k}` — which is `k`-degenerate (parent file) — is
**not** `k`-colourable: its `k` universal vertices together with any one
independent vertex form a `(k+1)`-clique, and a `(k+1)`-clique blocks any
`k`-colouring (pigeonhole). Hence `S_{n,k}` is `(k+1)`-colourable but not
`k`-colourable, so the greedy bound `χ ≤ k+1` is attained exactly.

Together with the parent's edge bound this gives the full sharp picture of Erdős
#1018's degeneracy parameter: `k`-degenerate ⟹ `≤ k·n` edges **and** `χ ≤ k+1`,
both realised simultaneously by `S_{n,k}`.

**Status**: VERIFIED, 0 axioms. Builds on `Erdos1018OQ01OQ01`.
Reference: https://erdosproblems.com/1018
-/

import Mathlib
import Proofs.Erdos1018OQ01OQ01

open Finset
open Erdos1018OQ01 (degOn)
open Erdos1018OQ01OQ01 (IsKDegenerate splitGraph splitGraph_adj splitGraph_kDegenerate
  card_lt_le card_lt_eq)

namespace Erdos1018OQ01OQ01OQ01

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ### Part 1 — greedy colouring: `k`-degenerate ⟹ `(k+1)`-colourable -/

/-- **Core greedy step.** For every vertex set `T` there is a global colouring
`c : V → Fin (k+1)` that is proper on `T` (adjacent vertices of `T` get distinct
colours). Strong induction on `T`: extract a within-degree-`≤ k` vertex `v` of
`T`, colour `T.erase v` by induction, and give `v` a colour avoided by its
(at most `k`) neighbours in `T`. -/
theorem exists_proper_coloring_on {k : ℕ} (h : IsKDegenerate G k) :
    ∀ T : Finset V, ∃ c : V → Fin (k + 1),
      ∀ u ∈ T, ∀ w ∈ T, G.Adj u w → c u ≠ c w := by
  intro T
  induction T using Finset.strongInduction with
  | _ T ih =>
    rcases T.eq_empty_or_nonempty with hT | hT
    · exact ⟨fun _ => 0, by intro u hu; rw [hT] at hu; exact absurd hu (notMem_empty u)⟩
    · obtain ⟨v, hvT, hvdeg⟩ := h T hT
      obtain ⟨c', hc'⟩ := ih (T.erase v) (Finset.erase_ssubset hvT)
      -- colours used by `v`'s neighbours inside `T`
      set N : Finset V := T.filter (fun w => G.Adj v w) with hN
      set forbidden : Finset (Fin (k + 1)) := N.image c' with hforb
      have hforb_card : forbidden.card ≤ k :=
        le_trans Finset.card_image_le hvdeg
      -- a free colour exists: `forbidden` cannot exhaust `Fin (k+1)`
      have hne : forbidden ≠ (univ : Finset (Fin (k + 1))) := by
        intro he
        rw [he, Finset.card_univ, Fintype.card_fin] at hforb_card
        omega
      obtain ⟨col, _, hcol⟩ :=
        Finset.exists_of_ssubset
          (Finset.ssubset_iff_subset_ne.mpr ⟨forbidden.subset_univ, hne⟩)
      -- extend the colouring by giving `v` the free colour `col`
      refine ⟨fun x => if x = v then col else c' x, ?_⟩
      intro u hu w hw hadj
      have huw : u ≠ w := G.ne_of_adj hadj
      by_cases huv : u = v
      · -- `u = v`, so `w ≠ v`; `w` is a neighbour of `v` in `T`, colour ≠ `col`
        have hwv : w ≠ v := fun h => huw (huv.trans h.symm)
        have hvw : G.Adj v w := huv ▸ hadj
        have hwN : w ∈ N := mem_filter.mpr ⟨hw, hvw⟩
        have hwf : c' w ∈ forbidden := mem_image_of_mem c' hwN
        simp only [if_pos huv, if_neg hwv]
        intro h; apply hcol; rw [h]; exact hwf
      · by_cases hwv : w = v
        · -- symmetric: `w = v`, `u` is a neighbour of `v` in `T`
          have hvu : G.Adj v u := hwv ▸ G.symm hadj
          have huN : u ∈ N := mem_filter.mpr ⟨hu, hvu⟩
          have huf : c' u ∈ forbidden := mem_image_of_mem c' huN
          simp only [if_neg huv, if_pos hwv]
          intro h; apply hcol; rw [← h]; exact huf
        · -- both `≠ v`: fall back to the inductive colouring on `T.erase v`
          simp only [if_neg huv, if_neg hwv]
          exact hc' u (mem_erase.mpr ⟨huv, hu⟩) w (mem_erase.mpr ⟨hwv, hw⟩) hadj

/-- **Greedy bound.** A `k`-degenerate graph is `(k+1)`-colourable, i.e.
`χ(G) ≤ k+1`. This is the colouring counterpart of the parent's edge bound
`|E| ≤ k·n`, obtained from the same `IsKDegenerate` hypothesis. -/
theorem degenerate_colorable {k : ℕ} (h : IsKDegenerate G k) : G.Colorable (k + 1) := by
  obtain ⟨c, hc⟩ := exists_proper_coloring_on G h univ
  exact ⟨SimpleGraph.Coloring.mk c (fun {u w} hadj => hc u (mem_univ u) w (mem_univ w) hadj)⟩

/-! ### Part 2 — tightness: the split graph needs exactly `k+1` colours -/

/-- The `k` universal vertices `{w : w.val < k}` of `S_{n,k}` together with a
single independent vertex `p` (`k ≤ p.val`) form a `(k+1)`-clique. -/
lemma splitGraph_isClique {n k : ℕ} (p : Fin n) (hp : k ≤ (p : ℕ)) :
    (splitGraph n k).IsClique
      (insert p (univ.filter (fun w : Fin n => (w : ℕ) < k)) : Finset (Fin n)) := by
  intro a ha b hb hab
  simp only [coe_insert, coe_filter, mem_univ, true_and, Set.mem_insert_iff,
    Set.mem_setOf_eq] at ha hb
  rw [splitGraph_adj]
  refine ⟨hab, ?_⟩
  -- at least one of `a`, `b` lies in the universal part (value `< k`)
  rcases ha with rfl | ha
  · rcases hb with rfl | hb
    · exact absurd rfl hab
    · exact Or.inr hb
  · exact Or.inl ha

/-- The `(k+1)`-clique above genuinely has `k+1` vertices: `p` is not in the
universal part, and the universal part has exactly `k` vertices (needs `k ≤ n`). -/
lemma splitGraph_clique_card {n k : ℕ} (hk : k < n) (p : Fin n) (hp : k ≤ (p : ℕ)) :
    (insert p (univ.filter (fun w : Fin n => (w : ℕ) < k)) : Finset (Fin n)).card = k + 1 := by
  have hpnotmem : p ∉ (univ.filter (fun w : Fin n => (w : ℕ) < k)) := by
    simp only [mem_filter, mem_univ, true_and]; omega
  rw [card_insert_of_notMem hpnotmem, card_lt_eq n k (le_of_lt hk)]

/-- **Tightness (lower bound).** For `k < n` the split graph `S_{n,k}` is *not*
`k`-colourable: it contains a `(k+1)`-clique, and a `(k+1)`-clique cannot be
`k`-coloured (two of its `k+1` vertices would share a colour by pigeonhole, yet
they are adjacent). -/
theorem splitGraph_not_colorable {n k : ℕ} (hk : k < n) :
    ¬ (splitGraph n k).Colorable k := by
  -- pick the independent-part vertex `⟨k, hk⟩`
  have hp : k ≤ ((⟨k, hk⟩ : Fin n) : ℕ) := le_rfl
  have hclique := splitGraph_isClique ⟨k, hk⟩ hp
  have hcard := splitGraph_clique_card hk ⟨k, hk⟩ hp
  intro hcol
  -- a `(k+1)`-clique forces the chromatic number to be `≥ k+1`
  have : k + 1 ≤ k :=
    hcard ▸ (hclique.card_le_of_colorable hcol)
  omega

/-- **Chromatic number of the split graph.** For `k < n`, `S_{n,k}` is
`(k+1)`-colourable (it is `k`-degenerate, Part 1) but not `k`-colourable
(Part 2). So `χ(S_{n,k}) = k+1` exactly, and the greedy bound
`degenerate_colorable` is sharp. -/
theorem splitGraph_chromatic {n k : ℕ} (hk : k < n) :
    (splitGraph n k).Colorable (k + 1) ∧ ¬ (splitGraph n k).Colorable k :=
  ⟨degenerate_colorable (splitGraph n k) (splitGraph_kDegenerate n k),
    splitGraph_not_colorable hk⟩

end Erdos1018OQ01OQ01OQ01
