import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-
# Girth-6 Planar Graphs are 3-Colorable (OQ-03)

## The Open Question

The parent entry `euler-polyhedral-oq-01` lists as its third open question:

> *Girth-6 planar graphs (E ≤ 3V/2 − 3): are they 3-colorable? (Grötzsch's
> theorem, not formalized)*

The **full** Grötzsch theorem — every *triangle-free* (girth ≥ 4) planar graph
is 3-colorable — is genuinely deep and requires discharging-style arguments;
it remains unformalized in Lean 4.  The literal question posed, however,
restricts to **girth ≥ 6**, and that weak form has a clean, fully
elementary affirmative answer via **2-degeneracy**, which we formalize here.

## The Mathematics

A planar graph `G` with girth ≥ 6 satisfies the face–edge double count
`6F ≤ 2E`, which combined with Euler's formula gives `2E ≤ 3V − 6`
(this is `edge_bound_girth6` in the parent file).  The key point is that this
bound is **hereditary**: every subgraph induced on a vertex subset `W` is still
planar with girth ≥ 6, so it too has few edges.  Counting neighbours *inside*
`W`, every nonempty `W` satisfies

  `∑_{v ∈ W} dᵥ(W) = 2·e(W) < 3·|W|`

(the strict `< 3|W|` form absorbs both the cyclic case `2e ≤ 3|W|−6` and the
forest case `2e ≤ 2|W|−2`).  Averaging then yields a vertex `v ∈ W` with at
most `2` neighbours inside `W`.  This is exactly the statement that `G` is
**2-degenerate**, and a 2-degenerate graph is 3-colorable by greedy coloring.

## What This File Contributes

The parent file `EulerPolyhedralOQ01.lean` records the colouring step only
*schematically* (`six_colorable_from_degeneracy` reduces to `5 + 1 = 6`).  The
core contribution here is a **genuine** `SimpleGraph.Colorable` proof of the
greedy-coloring / degeneracy theorem:

* `proper_coloring_on_finset` — greedy coloring by strong induction on a
  vertex subset (the heart of the argument).
* `colorable_of_degenerate` — **`k`-degenerate ⟹ `G.Colorable (k+1)`**, a real
  `SimpleGraph.Colorable` statement (not an encoded numeral).
* `exists_low_degree_in_subset` — the averaging lemma turning an edge/degree
  bound into a low-degree witness.
* `girth6_planar_three_colorable` — **girth-6 planar ⟹ `G.Colorable 3`**, the
  affirmative answer to the open question (with the hereditary edge bound made
  explicit as the precise content of "planar with girth ≥ 6").
* `girth6_exists_low_degree_vertex` — the global degeneracy witness
  (`∃ v, G.degree v ≤ 2`) proved from `2E ≤ 3V − 6` via the handshaking lemma,
  mirroring the parent's `exists_low_degree_vertex` (degree ≤ 5).

Everything is `sorry`-free and `axiom`-free.

## References
- Grötzsch (1959). "Ein Dreifarbensatz für dreikreisfreie Netze auf der Kugel."
- Diestel, "Graph Theory" (5th ed.), §5.1 (degeneracy and greedy coloring),
  §6.5 (Grötzsch's theorem).
- Parent entry: `euler-polyhedral-oq-01` (`EulerPolyhedralOQ01.lean`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace EulerPolyhedralGirth6

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ============================================================
-- PART 1: Averaging — a low-degree witness inside any subset
-- ============================================================

/-- The number of neighbours of `v` lying inside the vertex subset `W`. -/
def degIn (G : SimpleGraph V) [DecidableRel G.Adj] (W : Finset V) (v : V) : ℕ :=
  (W.filter (fun w => G.Adj v w)).card

/-- **Averaging.**  If the total number of in-subset incidences is strictly less
    than `(k+1)·|W|`, some vertex of `W` has at most `k` neighbours inside `W`.

    This is the engine that converts the (hereditary) edge bound of a girth-6
    planar graph into a degeneracy witness: with `∑ degIn < 3|W|` and `k = 2`
    we obtain a vertex of in-degree ≤ 2. -/
theorem exists_low_degree_in_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (W : Finset V) (hW : W.Nonempty) (k : ℕ)
    (hsum : ∑ v ∈ W, degIn G W v < (k + 1) * W.card) :
    ∃ v ∈ W, degIn G W v ≤ k := by
  by_contra h
  push_neg at h
  -- Every vertex of `W` has in-degree ≥ k+1, so the sum is ≥ (k+1)·|W|.
  have hlb : W.card • (k + 1) ≤ ∑ v ∈ W, degIn G W v :=
    Finset.card_nsmul_le_sum W _ (k + 1) (fun v hv => h v hv)
  simp only [smul_eq_mul] at hlb
  -- Contradiction with the strict upper bound.
  have : (k + 1) * W.card ≤ ∑ v ∈ W, degIn G W v := by
    rw [mul_comm]; exact hlb
  omega

-- ============================================================
-- PART 2: Greedy coloring — the degeneracy theorem
-- ============================================================

/-- **Greedy coloring on a subset.**  If `G` is `k`-degenerate — i.e. every
    nonempty vertex subset has a vertex with at most `k` neighbours inside that
    subset — then for *every* subset `W` there is a `(k+1)`-coloring of `V` that
    is proper on `W`.

    The proof is the classical greedy argument, by strong induction on `|W|`:
    delete a low-degree vertex `v`, colour the rest by induction, then give `v`
    one of the `k+1` colours avoided by its (≤ `k`) coloured neighbours. -/
theorem proper_coloring_on_finset (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hdeg : ∀ W : Finset V, W.Nonempty → ∃ v ∈ W, degIn G W v ≤ k) :
    ∀ W : Finset V, ∃ c : V → Fin (k + 1),
      ∀ u ∈ W, ∀ w ∈ W, G.Adj u w → c u ≠ c w := by
  intro W
  induction W using Finset.strongInductionOn with
  | _ W IH =>
    rcases W.eq_empty_or_nonempty with hW | hW
    · -- Empty subset: any constant colouring is vacuously proper.
      exact ⟨fun _ => 0, by simp [hW]⟩
    · -- Pick a low-degree vertex `v` of `W`.
      obtain ⟨v, hvW, hvdeg⟩ := hdeg W hW
      have hsub : W.erase v ⊂ W := Finset.erase_ssubset hvW
      obtain ⟨c', hc'⟩ := IH (W.erase v) hsub
      -- Colours used by the in-`W` neighbours of `v`.
      set Nv := W.filter (fun w => G.Adj v w) with hNv
      set used := Nv.image c' with hused
      have hused_card : used.card ≤ k := le_trans (Finset.card_image_le) hvdeg
      -- A free colour exists, since `|used| ≤ k < k + 1 = |Fin (k+1)|`.
      have hfree : ∃ col : Fin (k + 1), col ∉ used := by
        by_contra hc
        push_neg at hc
        have hsubset : (Finset.univ : Finset (Fin (k + 1))) ⊆ used :=
          fun x _ => hc x
        have := Finset.card_le_card hsubset
        simp only [Finset.card_univ, Fintype.card_fin] at this
        omega
      obtain ⟨col, hcol⟩ := hfree
      refine ⟨Function.update c' v col, ?_⟩
      intro u hu w hw huw
      -- Case analysis on whether `u`, `w` equal the freshly coloured vertex `v`.
      by_cases huv : u = v
      · subst huv
        -- u = v.  Then w ≠ v (Adj is irreflexive) and w is a coloured neighbour.
        have hwv : w ≠ u := (G.ne_of_adj huw).symm
        have hwNv : w ∈ Nv := by
          rw [hNv]; exact Finset.mem_filter.mpr ⟨hw, huw⟩
        have : c' w ∈ used := by rw [hused]; exact Finset.mem_image_of_mem c' hwNv
        rw [Function.update_self, Function.update_of_ne hwv]
        intro hbad; exact hcol (hbad ▸ this)
      · by_cases hwv : w = v
        · subst hwv
          -- w = v.  Then u ≠ v and u is a coloured neighbour (Adj is symmetric).
          have huNv : u ∈ Nv := by
            rw [hNv]; exact Finset.mem_filter.mpr ⟨hu, G.adj_symm huw⟩
          have : c' u ∈ used := by rw [hused]; exact Finset.mem_image_of_mem c' huNv
          rw [Function.update_self, Function.update_of_ne huv]
          intro hbad; exact hcol (hbad ▸ this)
        · -- Neither is `v`: both lie in `W.erase v`, use the inductive colouring.
          rw [Function.update_of_ne huv, Function.update_of_ne hwv]
          exact hc' u (Finset.mem_erase.mpr ⟨huv, hu⟩) w
            (Finset.mem_erase.mpr ⟨hwv, hw⟩) huw

/-- **Degeneracy ⟹ colorability.**  A `k`-degenerate finite graph is
    `(k+1)`-colorable.  This is a genuine `SimpleGraph.Colorable` statement,
    obtained by specialising `proper_coloring_on_finset` to the full vertex set
    and packaging the resulting colouring as a `SimpleGraph.Coloring`. -/
theorem colorable_of_degenerate (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (hdeg : ∀ W : Finset V, W.Nonempty → ∃ v ∈ W, degIn G W v ≤ k) :
    G.Colorable (k + 1) := by
  obtain ⟨c, hc⟩ := proper_coloring_on_finset G k hdeg Finset.univ
  exact ⟨Coloring.mk c (fun {u w} huw =>
    hc u (Finset.mem_univ u) w (Finset.mem_univ w) huw)⟩

-- ============================================================
-- PART 3: Application — girth-6 planar graphs are 3-colorable
-- ============================================================

/-- **Main result (open question OQ-03).**  A planar graph of girth ≥ 6 is
    3-colorable.

    The hypothesis `h_hereditary` is exactly the (hereditary) content of
    "planar with girth ≥ 6": every nonempty induced subgraph on `W` has
    `2·e(W) = ∑_{v∈W} dᵥ(W) < 3|W|`, the strict average-degree-below-3 bound
    that follows from `6F ≤ 2E` + Euler's formula on each subgraph (cyclic case
    `2e ≤ 3|W| − 6`, forest case `2e ≤ 2|W| − 2`, both `< 3|W|`).

    From it, `exists_low_degree_in_subset` (with `k = 2`) shows `G` is
    2-degenerate, and `colorable_of_degenerate` upgrades that to a real
    3-colouring. -/
theorem girth6_planar_three_colorable (G : SimpleGraph V) [DecidableRel G.Adj]
    (h_hereditary : ∀ W : Finset V, W.Nonempty →
      ∑ v ∈ W, degIn G W v < 3 * W.card) :
    G.Colorable 3 := by
  have hdeg : ∀ W : Finset V, W.Nonempty → ∃ v ∈ W, degIn G W v ≤ 2 := by
    intro W hW
    exact exists_low_degree_in_subset G W hW 2 (by
      have := h_hereditary W hW
      simpa using this)
  -- `colorable_of_degenerate` with `k = 2` gives `Colorable (2 + 1) = Colorable 3`.
  exact colorable_of_degenerate G 2 hdeg

-- ============================================================
-- PART 4: The global degeneracy witness (mirrors the parent)
-- ============================================================

/-- **Global degeneracy witness.**  In a planar graph of girth ≥ 6 (edge bound
    `2E ≤ 3V − 6`) there is a vertex of degree ≤ 2.

    This mirrors the parent file's `exists_low_degree_vertex` (which gives a
    degree-≤ 5 vertex from the *general* planar bound `E ≤ 3V − 6`) and is
    proved the same way: if every degree were ≥ 3, the handshaking lemma would
    force `2E ≥ 3V`, contradicting `2E ≤ 3V − 6`. -/
theorem girth6_exists_low_degree_vertex (G : SimpleGraph V) [DecidableRel G.Adj]
    (hV : 3 ≤ Fintype.card V)
    (h_girth6 : 2 * (G.edgeFinset.card : ℤ) ≤ 3 * Fintype.card V - 6) :
    ∃ v : V, G.degree v ≤ 2 := by
  by_contra h
  push_neg at h
  -- Every vertex has degree ≥ 3.
  have hsum_lower : 3 * Fintype.card V ≤ ∑ v, G.degree v := by
    calc 3 * Fintype.card V
        = ∑ _v : V, 3 := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
      _ ≤ ∑ v, G.degree v := Finset.sum_le_sum (fun v _ => h v)
  have hshake := G.sum_degrees_eq_twice_card_edges
  -- So 3V ≤ 2E, contradicting 2E ≤ 3V − 6.
  have hcast : (3 : ℤ) * Fintype.card V ≤ 2 * G.edgeFinset.card := by
    have : (3 * Fintype.card V : ℤ) ≤ ((∑ v, G.degree v : ℕ) : ℤ) := by exact_mod_cast hsum_lower
    rw [hshake] at this; push_cast at this ⊢; linarith
  linarith

end EulerPolyhedralGirth6
