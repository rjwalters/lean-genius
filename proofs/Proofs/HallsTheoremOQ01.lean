/-
Hall's Marriage Theorem for bipartite graphs: the full biconditional

Source: Open question from the halls-theorem gallery family
Status: VERIFIED (0 axioms, 0 sorries)

Hall's marriage theorem characterises exactly when a (locally finite) bipartite
graph `G` with parts `p₁`, `p₂` admits a matching saturating one side `p₁`: such a
matching exists **iff** Hall's condition holds, i.e. every subset `s ⊆ p₁` has at
least as many neighbours as it has vertices,

    s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard.

Mathlib proves only the hard, *sufficiency* direction
(`SimpleGraph.exists_isMatching_of_forall_ncard_le` : Hall's condition ⟹ a matching,
and the perfect-matching analogue `exists_isPerfectMatching_of_forall_ncard_le`).
The *necessity* direction — that any saturating matching forces Hall's condition —
is absent from Mathlib. We supply it as a standalone, graph-agnostic fact and
assemble the textbook biconditionals.

Novel content (absent from Mathlib):

  * `ncard_le_ncard_biUnion_neighborSet_of_isMatching` :
        a matching saturating `s` injects `s` into its neighbourhood, hence
        `s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard`  (necessity of Hall's condition)
  * `ncard_le_of_isPerfectMatching` : the global form, for a perfect matching
  * `hall_marriage`  : Hall's condition ↔ ∃ a matching saturating `p₁`
  * `hall_perfect`   : the global Hall condition ↔ ∃ a perfect matching
  * `exists_violating_of_no_matching` : the contrapositive "deficiency" form —
        no saturating matching ⟹ some `s ⊆ p₁` violates Hall's condition

The necessity argument is the elementary half of Hall's theorem: send each `v ∈ s`
to its unique matched partner `φ v`. Distinct vertices receive distinct partners
(the matching axiom), and a partner of `v` is a `G`-neighbour of `v` (the matching
is a subgraph), so `φ` injects `s` into `⋃ x ∈ s, G.neighborSet x`; an injection
into a finite set does not increase `ncard`. (For an infinite `s` the bound is
vacuous: `s.ncard = 0`.)
-/
import Mathlib

open Set Function

namespace HallsTheoremOQ01

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {p₁ p₂ : Set V}

/-- **Necessity of Hall's condition.** If `M` is a matching whose vertex set contains
`s`, then `s` injects into its `G`-neighbourhood via the matched-partner map, so
`s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard`. This holds in *any* graph (no
bipartiteness needed) and is the easy converse to Mathlib's
`exists_isMatching_of_forall_ncard_le`. -/
theorem ncard_le_ncard_biUnion_neighborSet_of_isMatching
    [G.LocallyFinite] {M : G.Subgraph} (hM : M.IsMatching)
    {s : Set V} (hs : s ⊆ M.verts) :
    s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard := by
  classical
  -- the matched-partner function: each `v ∈ M.verts` has a unique `M`-neighbour `φ v`
  let φ : V → V := fun v => if h : v ∈ M.verts then (hM h).choose else v
  have hadj : ∀ v ∈ M.verts, M.Adj v (φ v) := by
    intro v hv
    show M.Adj v (if h : v ∈ M.verts then (hM h).choose else v)
    rw [dif_pos hv]
    exact (hM hv).choose_spec.1
  -- `φ v` is a `G`-neighbour of `v`, hence lands in the neighbourhood of `s`
  have hmem : ∀ v ∈ s, φ v ∈ ⋃ x ∈ s, G.neighborSet x := by
    intro v hv
    exact Set.mem_biUnion hv ((G.mem_neighborSet v (φ v)).mpr (M.adj_sub (hadj v (hs hv))))
  -- distinct vertices get distinct partners: `φ` is injective on `s`
  have hinj : Set.InjOn φ s := by
    intro u hu v hv huv
    have hu' := hadj u (hs hu)
    have hv' := hadj v (hs hv)
    rw [huv] at hu'
    exact hM.eq_of_adj_right hu' hv'
  rcases Set.finite_or_infinite s with hsfin | hsinf
  · exact Set.ncard_le_ncard_of_injOn φ hmem hinj
      (hsfin.biUnion fun x _ => (G.neighborSet x).toFinite)
  · simp [hsinf.ncard]

/-- The global form of necessity: a **perfect** matching forces Hall's condition for
*every* set `s` (a perfect matching saturates all of `V`). -/
theorem ncard_le_of_isPerfectMatching
    [G.LocallyFinite] {M : G.Subgraph} (hM : M.IsPerfectMatching) (s : Set V) :
    s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard :=
  ncard_le_ncard_biUnion_neighborSet_of_isMatching hM.1
    (by rw [Subgraph.isSpanning_iff.mp hM.2]; exact subset_univ s)

/-- **Hall's Marriage Theorem (bipartite form).** For a locally finite bipartite graph
`G` with parts `p₁`, `p₂`, a matching saturating `p₁` exists **iff** Hall's condition
holds on `p₁`. The forward direction is Mathlib's
`exists_isMatching_of_forall_ncard_le`; the converse is the necessity lemma above. -/
theorem hall_marriage [G.LocallyFinite] (h₁ : G.IsBipartiteWith p₁ p₂) :
    (∀ s ⊆ p₁, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard) ↔
      ∃ M : G.Subgraph, p₁ ⊆ M.verts ∧ M.IsMatching := by
  constructor
  · intro h₂
    exact exists_isMatching_of_forall_ncard_le h₁ h₂
  · rintro ⟨M, hp, hM⟩ s hs
    exact ncard_le_ncard_biUnion_neighborSet_of_isMatching hM (hs.trans hp)

/-- **Hall's Marriage Theorem (perfect-matching form).** For a locally finite bipartite
graph, a perfect matching exists **iff** the global Hall condition holds (`s.ncard ≤
neighbourhood.ncard` for every `s`). Forward is Mathlib's
`exists_isPerfectMatching_of_forall_ncard_le`; the converse is `ncard_le_of_isPerfectMatching`. -/
theorem hall_perfect [G.LocallyFinite] (h₁ : G.IsBipartiteWith p₁ p₂) :
    (∀ s : Set V, s.ncard ≤ (⋃ x ∈ s, G.neighborSet x).ncard) ↔
      ∃ M : G.Subgraph, M.IsPerfectMatching := by
  constructor
  · intro h₂
    exact exists_isPerfectMatching_of_forall_ncard_le h₁ h₂
  · rintro ⟨M, hM⟩ s
    exact ncard_le_of_isPerfectMatching hM s

/-- **Deficiency / contrapositive form.** If `G` admits *no* matching saturating `p₁`,
then Hall's condition must fail somewhere: some `s ⊆ p₁` has strictly fewer neighbours
than vertices. This is the practical "obstruction" certificate complementing the
existence statement. -/
theorem exists_violating_of_no_matching [G.LocallyFinite] (h₁ : G.IsBipartiteWith p₁ p₂)
    (hno : ¬ ∃ M : G.Subgraph, p₁ ⊆ M.verts ∧ M.IsMatching) :
    ∃ s ⊆ p₁, (⋃ x ∈ s, G.neighborSet x).ncard < s.ncard := by
  by_contra hcon
  push_neg at hcon
  exact hno ((hall_marriage h₁).mp hcon)

end HallsTheoremOQ01
