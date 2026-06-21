/-
  Hall's theorem for balanced bipartite graphs: the one-sided condition suffices.

  Open Question: halls-theorem-oq-02
  ("Hall's perfect matching theorem, bipartite, global Hall condition")
  Parent gallery entry: halls-theorem-oq-01 (the full biconditional, necessity direction).

  ## Context

  The parent `HallsTheoremOQ01.lean` (`namespace HallsTheoremOQ01`) proves the two textbook
  biconditionals:

  * `hall_marriage` : Hall's condition **on `p₁`** ↔ ∃ a matching saturating `p₁`;
  * `hall_perfect`  : the **global** Hall condition (every `s : Set V`) ↔ ∃ a perfect matching.

  Mathlib's perfect-matching theorem `exists_isPerfectMatching_of_forall_ncard_le` likewise
  requires the *global* condition `∀ s : Set V, s.ncard ≤ N(s).ncard`, which silently forces
  `p₁ ∪ p₂ = univ` and `p₁.ncard = p₂.ncard`. In practice one almost always has a **balanced**
  bipartition (`p₁.ncard = p₂.ncard`) and only wants to check Hall's condition on the *one* side
  `p₁`. This file supplies exactly that strengthening, absent from both Mathlib and the parent:

  > **In a balanced finite bipartite graph, the one-sided Hall condition on `p₁` already produces
  > a matching that saturates BOTH sides** — and hence a perfect matching whenever the two parts
  > cover the vertex set.

  The mechanism is a counting argument on top of the parent's `hall_marriage`: a matching
  saturating `p₁` injects `p₁` into `p₂` via the matched-partner map; since the parts are
  balanced and `p₂` is finite, that injection is a bijection onto `p₂`, so every vertex of `p₂`
  is matched as well.

  ## Sorries: 0   Axioms: 0
-/
import Mathlib
import Proofs.HallsTheoremOQ01

open Set Function

namespace HallsTheoremOQ02

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {p₁ p₂ : Set V}

/-- **Balanced one-sided Hall ⟹ a matching saturating both sides.**

For a locally finite bipartite graph `G` with parts `p₁`, `p₂`, if the parts are balanced
(`p₁.ncard = p₂.ncard`, with `p₂` finite) and Hall's condition holds **on `p₁`**, then there is a
matching `M` whose vertex set contains *both* `p₁` and `p₂`. Thus, in the balanced case, checking
Hall's condition on a single side is enough to saturate the other side for free. -/
theorem isMatching_saturating_both_of_balanced
    [G.LocallyFinite] (h₁ : G.IsBipartiteWith p₁ p₂)
    (hfin₂ : p₂.Finite) (hbal : p₁.ncard = p₂.ncard)
    (hall : ∀ s ⊆ p₁, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard) :
    ∃ M : G.Subgraph, p₁ ⊆ M.verts ∧ p₂ ⊆ M.verts ∧ M.IsMatching := by
  classical
  -- A matching saturating `p₁`, from the parent's `hall_marriage`.
  obtain ⟨M, hp₁, hM⟩ := (HallsTheoremOQ01.hall_marriage h₁).mp hall
  -- The matched-partner map: each `v ∈ M.verts` has a unique `M`-neighbour `φ v`.
  let φ : V → V := fun v => if h : v ∈ M.verts then (hM h).choose else v
  have hadj : ∀ v ∈ M.verts, M.Adj v (φ v) := by
    intro v hv
    show M.Adj v (if h : v ∈ M.verts then (hM h).choose else v)
    rw [dif_pos hv]
    exact (hM hv).choose_spec.1
  -- `φ` maps `p₁` into `p₂` (partners of `p₁`-vertices lie in `p₂` by bipartiteness).
  have hmaps : ∀ v ∈ p₁, φ v ∈ p₂ := fun v hv =>
    h₁.mem_of_mem_adj hv (M.adj_sub (hadj v (hp₁ hv)))
  -- `φ` lands in `M.verts` (a partner is an endpoint of an `M`-edge).
  have hvert : ∀ v ∈ p₁, φ v ∈ M.verts := fun v hv => (hadj v (hp₁ hv)).snd_mem
  -- `φ` is injective on `p₁` (distinct vertices get distinct partners).
  have hinj : Set.InjOn φ p₁ := by
    intro u hu v hv huv
    have hu' := hadj u (hp₁ hu)
    have hv' := hadj v (hp₁ hv)
    rw [huv] at hu'
    exact hM.eq_of_adj_right hu' hv'
  -- The image `φ '' p₁` is a subset of `p₂` of the same cardinality, hence equals `p₂`.
  have himg_sub : φ '' p₁ ⊆ p₂ := by
    rintro w ⟨v, hv, rfl⟩; exact hmaps v hv
  have hcard : (φ '' p₁).ncard = p₂.ncard := by
    rw [Set.ncard_image_of_injOn hinj, hbal]
  have himg_eq : φ '' p₁ = p₂ :=
    Set.eq_of_subset_of_ncard_le himg_sub (le_of_eq hcard.symm) hfin₂
  -- Therefore `p₂ ⊆ M.verts`.
  have hp₂ : p₂ ⊆ M.verts := by
    rw [← himg_eq]
    rintro w ⟨v, hv, rfl⟩; exact hvert v hv
  exact ⟨M, hp₁, hp₂, hM⟩

/-- **Balanced one-sided Hall ⟹ a perfect matching (when the parts cover `V`).**

If, in addition to the balanced one-sided Hall hypotheses, the two parts cover the whole vertex
set (`p₁ ∪ p₂ = univ`), then the saturating matching is in fact a **perfect** matching. This is
the practical bipartite perfect-matching criterion: balance the sides, verify Hall on one side. -/
theorem exists_isPerfectMatching_of_balanced
    [G.LocallyFinite] (h₁ : G.IsBipartiteWith p₁ p₂)
    (hfin₂ : p₂.Finite) (hbal : p₁.ncard = p₂.ncard) (hcover : p₁ ∪ p₂ = Set.univ)
    (hall : ∀ s ⊆ p₁, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard) :
    ∃ M : G.Subgraph, M.IsPerfectMatching := by
  obtain ⟨M, hp₁, hp₂, hM⟩ := isMatching_saturating_both_of_balanced h₁ hfin₂ hbal hall
  refine ⟨M, hM, ?_⟩
  rw [Subgraph.isSpanning_iff]
  rw [Set.eq_univ_iff_forall]
  intro v
  have : v ∈ p₁ ∪ p₂ := by rw [hcover]; exact Set.mem_univ v
  rcases this with hv | hv
  · exact hp₁ hv
  · exact hp₂ hv

end HallsTheoremOQ02
