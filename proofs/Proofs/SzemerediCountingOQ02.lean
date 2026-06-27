/-
  Hypergraph Counting Lemma — Tripartite 3-Graph Framework

  A self-contained counting layer for tripartite 3-uniform hypergraphs,
  the setting of the Nagle–Rödl–Schacht (2006) counting lemma. It is the
  3-graph companion to the graph counting infrastructure in
  `SzemerediCounting.lean` and builds conceptually on the hypergraph
  regularity definitions in `SzemerediHypergraphCore.lean`.

  A tripartite 3-graph on parts `α`, `β`, `γ` is an adjacency predicate
  `adj a b c`, meaning the triple `(a, b, c)` is a hyperedge. This is the
  natural model for the counting lemma because a "labeled copy" of the
  single-hyperedge pattern is exactly an edge.

  ## What is proven here (no axioms, no sorries)

  * `edgeCount_le` — at most `|α|·|β|·|γ|` hyperedges.
  * `density_nonneg`, `density_le_one` — the density lives in `[0, 1]`.
  * `edgeCount_eq_density_mul` — the **exact counting identity** for the
    single-hyperedge pattern: the number of labeled copies equals
    `d · |α|·|β|·|γ|`. This is the counting lemma's main term `d^{e(F)}·∏|Vᵢ|`
    in the base case `e(F) = 1`, holding with *zero* error.
  * `sum_degA` — vertex degrees on the first part sum to the edge count.
  * `edgeCount_sq_le` — the **Cauchy–Schwarz "cherry" inequality**
    `e(H)² ≤ |α| · ∑_a deg(a)²`. Bounding the number of "cherries"
    (pairs of edges sharing a first-coordinate vertex) from below by the
    edge count is the deterministic engine behind every regularity-based
    counting argument; the density-increment / defect form of the counting
    lemma is exactly this inequality applied to vertex subsets.
  * `cherryCount` / `cherryCount_eq_sum_sq_degA` — the **exact `e(F) = 2`
    enumeration**: the number of labeled cherries (ordered edge pairs sharing
    a first coordinate) equals `∑_a deg(a)²` with no error term.
  * `edgeCount_sq_le_cherryCount` — the cherry inequality rendered as an
    explicit two-edge count: `e(H)² ≤ |α| · cherryCount(H)`.
  * `edgeCount_mono`, `edgeCount_complete`, `edgeCount_empty`,
    `density_empty` — structural sanity lemmas.

  ## What remains open (the genuine NRS content)

  The full counting lemma states that an *ε-regular* tripartite 3-graph of
  density `d` contains `(1 ± f(ε))·d^{e(F)}·∏|Vᵢ|` labeled copies of any
  fixed 3-graph `F`, with `f(ε) → 0`. For patterns with `e(F) ≥ 2` this is
  research-level: it requires *relative* (Gowers/Rödl–Skokan) regularity —
  density conditioned on the underlying 2-graph skeleton — and an inductive
  argument over the hypergraph dimension. The exact identity proven here is
  the `e(F) = 1` base case; the cherry inequality is the second-moment tool
  that the regularity step iterates. See the follow-up notes in
  `SzemerediHypergraphCore.lean`.

  References:
  - Nagle, B., Rödl, V., Schacht, M. (2006). "The counting lemma for
    regular k-uniform hypergraphs." Random Structures & Algorithms 28(2).
  - Gowers, W.T. (2007). "Hypergraph regularity and the multidimensional
    Szemerédi theorem." Annals of Mathematics 166(3).
-/
import Mathlib

namespace Szemeredi.HypergraphCounting

open Finset Classical

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: TRIPARTITE 3-GRAPHS AND THEIR EDGE COUNT
-- ═══════════════════════════════════════════════════════════════════

/-- A tripartite 3-uniform hypergraph on parts `α`, `β`, `γ`: the predicate
    `adj a b c` says the triple `(a, b, c)` is a hyperedge. -/
structure Tri3Graph (α β γ : Type*) where
  adj : α → β → γ → Prop

namespace Tri3Graph

/-- The number of vertex triples, `|α|·|β|·|γ|`. -/
def vertexTriples (α β γ : Type*) [Fintype α] [Fintype β] [Fintype γ] : ℕ :=
  Fintype.card α * Fintype.card β * Fintype.card γ

theorem card_vertexTriples :
    Fintype.card (α × β × γ) = vertexTriples α β γ := by
  unfold vertexTriples
  rw [Fintype.card_prod, Fintype.card_prod]; ring

/-- The hyperedges of `H`, viewed as triples in `α × β × γ`. -/
noncomputable def edgeFinset (H : Tri3Graph α β γ) : Finset (α × β × γ) :=
  univ.filter (fun p => H.adj p.1 p.2.1 p.2.2)

/-- The number of (labeled) hyperedges. -/
noncomputable def edgeCount (H : Tri3Graph α β γ) : ℕ := H.edgeFinset.card

/-- The edge count never exceeds the number of vertex triples. -/
theorem edgeCount_le (H : Tri3Graph α β γ) :
    H.edgeCount ≤ vertexTriples α β γ := by
  simp only [edgeCount, edgeFinset]
  calc (univ.filter (fun p => H.adj p.1 p.2.1 p.2.2)).card
      ≤ (univ : Finset (α × β × γ)).card := Finset.card_filter_le _ _
    _ = vertexTriples α β γ := by rw [Finset.card_univ, card_vertexTriples]

-- ═══════════════════════════════════════════════════════════════════
-- PART II: DENSITY AND THE EXACT MAIN-TERM IDENTITY
-- ═══════════════════════════════════════════════════════════════════

/-- The edge density `d(H) = e(H) / (|α|·|β|·|γ|) ∈ ℚ`. -/
noncomputable def density (H : Tri3Graph α β γ) : ℚ :=
  (H.edgeCount : ℚ) / (vertexTriples α β γ : ℚ)

theorem density_nonneg (H : Tri3Graph α β γ) : 0 ≤ H.density := by
  unfold density; positivity

theorem density_le_one (H : Tri3Graph α β γ) : H.density ≤ 1 := by
  unfold density
  rcases Nat.eq_zero_or_pos (vertexTriples α β γ) with h | h
  · simp [h]
  · rw [div_le_one (by exact_mod_cast h)]
    exact_mod_cast H.edgeCount_le

/-- **Exact counting lemma, base case `e(F) = 1`.** The number of labeled
    copies of the single-hyperedge pattern equals `d · |α|·|β|·|γ|`. This is
    the counting lemma's main term, holding here with no error term. -/
theorem edgeCount_eq_density_mul (H : Tri3Graph α β γ)
    (h : 0 < vertexTriples α β γ) :
    (H.edgeCount : ℚ) = H.density * (vertexTriples α β γ : ℚ) := by
  have hb : (vertexTriples α β γ : ℚ) ≠ 0 := by exact_mod_cast h.ne'
  unfold density
  rw [div_mul_cancel₀ _ hb]

-- ═══════════════════════════════════════════════════════════════════
-- PART III: DEGREES AND THE CAUCHY–SCHWARZ CHERRY INEQUALITY
-- ═══════════════════════════════════════════════════════════════════

/-- The degree of a first-part vertex `a`: the number of hyperedges whose
    first coordinate is `a`. -/
noncomputable def degA (H : Tri3Graph α β γ) (a : α) : ℕ :=
  (H.edgeFinset.filter (fun p => p.1 = a)).card

/-- First-part degrees sum to the edge count: `∑_a deg(a) = e(H)`. -/
theorem sum_degA (H : Tri3Graph α β γ) :
    ∑ a : α, H.degA a = H.edgeCount := by
  simp only [degA, edgeCount]
  rw [Finset.card_eq_sum_card_fiberwise (s := H.edgeFinset) (t := (univ : Finset α))
    (f := fun p => p.1) (fun x _ => Finset.mem_univ _)]

/-- **Cauchy–Schwarz cherry inequality.** The squared edge count is bounded by
    `|α|` times the sum of squared first-part degrees:
    `e(H)² ≤ |α| · ∑_a deg(a)²`. Equivalently, the number of "cherries"
    (ordered pairs of edges sharing a first-coordinate vertex) is at least
    `e(H)² / |α|`. This second-moment bound is the engine of regularity-based
    counting and removal arguments. -/
theorem edgeCount_sq_le (H : Tri3Graph α β γ) :
    (H.edgeCount : ℚ) ^ 2 ≤ (Fintype.card α : ℚ) * ∑ a : α, (H.degA a : ℚ) ^ 2 := by
  have key := sq_sum_le_card_mul_sum_sq (s := (univ : Finset α))
    (f := fun a => (H.degA a : ℚ))
  rw [Finset.card_univ] at key
  have hs : (∑ a : α, (H.degA a : ℚ)) = (H.edgeCount : ℚ) := by
    rw [← Nat.cast_sum, sum_degA]
  rw [hs] at key
  exact key

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: THE CHERRY PATTERN — EXACT e(F) = 2 ENUMERATION
-- ═══════════════════════════════════════════════════════════════════

/-- A **cherry**: an ordered pair of hyperedges sharing the same first-part
    vertex. Cherries are exactly the labeled copies of the two-hyperedge
    pattern that glues two triples at their `α`-coordinate — the first pattern
    with `e(F) = 2`. Counting them is the next case past the exact base term. -/
noncomputable def cherryFinset (H : Tri3Graph α β γ) :
    Finset ((α × β × γ) × (α × β × γ)) :=
  (H.edgeFinset ×ˢ H.edgeFinset).filter (fun p => p.1.1 = p.2.1)

/-- The number of cherries (ordered edge pairs sharing a first coordinate). -/
noncomputable def cherryCount (H : Tri3Graph α β γ) : ℕ := H.cherryFinset.card

/-- The cherries centred at `a` are exactly the ordered pairs of `a`-edges. -/
theorem cherryFinset_filter (H : Tri3Graph α β γ) (a : α) :
    H.cherryFinset.filter (fun p => p.1.1 = a)
      = (H.edgeFinset.filter (fun q => q.1 = a)) ×ˢ
        (H.edgeFinset.filter (fun q => q.1 = a)) := by
  ext p
  simp only [cherryFinset, Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, hcen⟩, ha⟩
    exact ⟨⟨h1, ha⟩, h2, hcen ▸ ha⟩
  · rintro ⟨⟨h1, ha1⟩, h2, ha2⟩
    exact ⟨⟨⟨h1, h2⟩, ha1.trans ha2.symm⟩, ha1⟩

/-- **Cherry enumeration identity.** The number of cherries equals the sum of
    squared first-part degrees: `cherryCount(H) = ∑_a deg(a)²`. This makes the
    right-hand side of the Cauchy–Schwarz bound a genuine combinatorial count
    of two-edge configurations. -/
theorem cherryCount_eq_sum_sq_degA (H : Tri3Graph α β γ) :
    H.cherryCount = ∑ a : α, (H.degA a) ^ 2 := by
  rw [cherryCount,
    Finset.card_eq_sum_card_fiberwise (s := H.cherryFinset) (t := (univ : Finset α))
      (f := fun p => p.1.1) (fun p _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [cherryFinset_filter, Finset.card_product, degA, pow_two]

/-- **Cauchy–Schwarz cherry inequality, enumerated form.** The squared edge
    count is at most `|α|` times the number of cherries:
    `e(H)² ≤ |α| · cherryCount(H)`. Combined with `cherryCount_eq_sum_sq_degA`,
    this is the second-moment statement `e(H)² ≤ |α| · ∑_a deg(a)²` rendered as a
    bound on an explicit count of two-edge patterns. -/
theorem edgeCount_sq_le_cherryCount (H : Tri3Graph α β γ) :
    (H.edgeCount : ℚ) ^ 2 ≤ (Fintype.card α : ℚ) * (H.cherryCount : ℚ) := by
  have hcast : (H.cherryCount : ℚ) = ∑ a : α, (H.degA a : ℚ) ^ 2 := by
    rw [cherryCount_eq_sum_sq_degA, Nat.cast_sum]
    simp [Nat.cast_pow]
  rw [hcast]
  exact H.edgeCount_sq_le

-- ═══════════════════════════════════════════════════════════════════
-- PART V: STRUCTURAL LEMMAS
-- ═══════════════════════════════════════════════════════════════════

/-- Adding hyperedges can only increase the edge count. -/
theorem edgeCount_mono {H₁ H₂ : Tri3Graph α β γ}
    (h : ∀ a b c, H₁.adj a b c → H₂.adj a b c) :
    H₁.edgeCount ≤ H₂.edgeCount := by
  apply Finset.card_le_card
  intro p hp
  simp only [edgeFinset, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
  exact h _ _ _ hp

/-- The complete tripartite 3-graph: every triple is a hyperedge. -/
def complete (α β γ : Type*) : Tri3Graph α β γ := ⟨fun _ _ _ => True⟩

/-- The empty tripartite 3-graph: no hyperedges. -/
def empty (α β γ : Type*) : Tri3Graph α β γ := ⟨fun _ _ _ => False⟩

/-- The complete 3-graph realizes every vertex triple as an edge. -/
theorem edgeCount_complete :
    (complete α β γ).edgeCount = vertexTriples α β γ := by
  have hset : (complete α β γ).edgeFinset = (univ : Finset (α × β × γ)) := by
    ext p; simp [edgeFinset, complete]
  rw [edgeCount, hset, Finset.card_univ, card_vertexTriples]

/-- The empty 3-graph has no edges. -/
theorem edgeCount_empty :
    (empty α β γ).edgeCount = 0 := by
  have hset : (empty α β γ).edgeFinset = (∅ : Finset (α × β × γ)) := by
    ext p; simp [edgeFinset, empty]
  rw [edgeCount, hset, Finset.card_empty]

/-- The empty 3-graph has density `0`. -/
theorem density_empty :
    (empty α β γ).density = 0 := by
  rw [density, edgeCount_empty]; simp

end Tri3Graph

end Szemeredi.HypergraphCounting
