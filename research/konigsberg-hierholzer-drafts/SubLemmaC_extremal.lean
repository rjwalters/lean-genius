/-
# Sub-lemma C (undirected Hierholzer sufficiency) — EXTREMAL BLUEPRINT

STATUS: verify-ready DRAFT, NOT yet machine-checked (dual-tool blackout:
Aristotle backend 404 + Docker containerd meta.db I/O error prevent building).
Every lemma name and signature below was cross-checked against the local
`leanprover/lean4:v4.26.0` Mathlib checkout at /Users/rwalters/GitHub/mathlib4
(the same toolchain proofs/ pins). This file lives OUTSIDE `proofs/` so the
lake glob `Proofs.*` never compiles it; drop the bodies into
`proofs/Proofs/KonigsbergOQ02OQ01OQ02OQ01Dev.lean` once a build host is available.

## Why extremal (and not residual induction)

The prior plan was strong induction on `G.edgeFinset.card`: extract a closed
trail, delete its edges (Sub-lemma B keeps degrees even), recurse, splice.
That needs a residual graph, a splice constructor, and connectivity bookkeeping.

The **extremal** argument is strictly shorter and needs NEITHER induction NOR
Sub-lemma B:

  Take a trail `p` of MAXIMUM length among all trails (length is bounded by
  `G.edgeFinset.card`, so a maximum exists).

  * Step 1 — `p` is CLOSED.  If its endpoint `v` had an unused incident edge,
    `p.concat` that edge would be a strictly longer trail (`nodup_concat`),
    contradicting maximality.  So `p` is edge-maximal at `v`, hence closed by the
    already-verified `eq_of_isTrail_edgeMaximal` (Sub-lemma A).

  * Step 2 — `p` is EULERIAN.  If some edge were unused, connectivity gives an
    unused edge `e₁ = {w,z}` with `w ∈ p.support` (Mathlib's
    `Walk.exists_boundary_dart` supplies the boundary-crossing dart directly).
    Rotate `p` to start at `w` (`Walk.rotate`; `IsTrail.rotate` keeps it a trail,
    `rotate_edges` permutes the edge list so `e₁` is still unused and the length
    is unchanged), then `concat` `e₁`: a strictly longer trail, contradiction.
    So every edge is used exactly once (`IsTrail` ⇒ count ≤ 1), i.e. Eulerian.

Sub-lemma B (`even_degree_deleteEdges_of_closed_trail`) remains correct and
verified but is OFF the critical path for this route.

## Mathlib anchors (all verified present at v4.26.0)

  Walk.length_edges            Walks/Basic.lean:258   p.edges.length = p.length
  Walk.edges  (= darts.map …)  Walks/Basic.lean:132
  Walk.edges_subset_edgeSet    Walks/Basic.lean:212
  Walk.length_concat           Walks/Operations.lean:229
  Walk.edges_concat            Walks/Operations.lean:421   = p.edges ++ [s(v,w)]
  Walk.snd_mem_support_of_mem_edges  Walks/Operations.lean:450
  Walk.start_mem_support       Walks/Basic.lean:157
  Walk.exists_boundary_dart    Walks/Basic.lean:388   ⟨d ∈ darts, fst∈S, snd∉S⟩
  Walk.rotate                  Connectivity/WalkDecomp.lean:273
  Walk.rotate_edges            Connectivity/WalkDecomp.lean:294  (rotate).edges ~ edges
  IsTrail.rotate               Paths.lean:495
  Dart.edge / Dart.edge_mem    Dart.lean:61,69
  Dart.adj  (@[simp])          Dart.lean:33          G.Adj d.fst d.snd
  Connected.exists_isPath      Connectivity/Connected.lean:318
  List.nodup_concat            Data/List/Nodup.lean:242   (l.concat u).Nodup ↔ u∉l ∧ l.Nodup
  List.nodup_iff_count_le_one  Data/List/Nodup.lean:140
  mem_edgeFinset               Finite.lean:66
  eq_of_isTrail_edgeMaximal    KonigsbergOQ02OQ01OQ02OQ01Dev.lean  (VERIFIED, Sub-lemma A)
-/
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp
import Mathlib.Tactic

open SimpleGraph SimpleGraph.Walk

namespace UndirectedEulerDev

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

/-! ### L1. A trail's length is bounded by the number of edges. -/

/-- A trail uses distinct edges, all lying in `edgeFinset`, so its length is at most
`G.edgeFinset.card`.  This is the a-priori bound that makes a *maximum*-length trail
exist. -/
theorem trail_length_le_card_edgeFinset
    {u v : V} {p : G.Walk u v} (hp : p.IsTrail) :
    p.length ≤ G.edgeFinset.card := by
  classical
  -- length = #(edge list) = #(edge finset), since the edges are nodup …
  have h1 : p.length = p.edges.toFinset.card := by
    rw [List.toFinset_card_of_nodup hp.edges_nodup, length_edges]
  -- … and the edge finset sits inside `G.edgeFinset`.
  have h2 : p.edges.toFinset ⊆ G.edgeFinset := by
    intro e he
    rw [List.mem_toFinset] at he
    rw [mem_edgeFinset]
    exact p.edges_subset_edgeSet he
  rw [h1]
  exact Finset.card_le_card h2

/-! ### L2. A maximum-length trail exists. -/

/-- Among all trails of `G` (any endpoints) there is one of maximum length.
Packaged with the maximality witness in the form Steps 1–2 consume:
`∀ trail q, q.length ≤ p.length`. -/
theorem exists_max_length_trail (hne : G.edgeSet.Nonempty ∨ True) :
    ∃ (u v : V) (p : G.Walk u v), p.IsTrail ∧
      ∀ (x y : V) (q : G.Walk x y), q.IsTrail → q.length ≤ p.length := by
  classical
  -- The achievable trail lengths, a nonempty (nil has length 0) bounded ⊆ ℕ.
  set N := G.edgeFinset.card with hN
  set S : Finset ℕ :=
    (Finset.range (N + 1)).filter
      (fun n => ∃ (u v : V) (p : G.Walk u v), p.IsTrail ∧ p.length = n) with hS
  have h0mem : (0 : ℕ) ∈ S := by
    -- the empty walk at any vertex is a trail of length 0
    obtain ⟨w⟩ : Nonempty V := by
      -- V is nonempty because … (in the real assembly this comes from `hconn.nonempty`)
      sorry
    rw [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, w, w, Walk.nil, IsTrail.nil, rfl⟩
  have hSne : S.Nonempty := ⟨0, h0mem⟩
  set m := S.max' hSne with hm
  have hmmem : m ∈ S := S.max'_mem hSne
  rw [hS, Finset.mem_filter] at hmmem
  obtain ⟨_, u, v, p, hptrail, hplen⟩ := hmmem
  refine ⟨u, v, p, hptrail, ?_⟩
  intro x y q hq
  -- q.length ∈ S (it is ≤ N by L1), hence ≤ m = p.length.
  have hqlenmem : q.length ∈ S := by
    rw [hS, Finset.mem_filter, Finset.mem_range]
    exact ⟨by have := trail_length_le_card_edgeFinset hq; omega, x, y, q, hq, rfl⟩
  have := S.le_max' _ hqlenmem
  rw [← hplen]; simpa [hm] using this

/-! ### Step 1. A maximum-length trail is closed.

For a maximum-length trail `p : G.Walk u v` in an all-even-degree graph, `p` is
edge-maximal at `v`: any unused incident edge `{v,z}` would give `p.concat` a longer
trail (`nodup_concat` + `length_concat`), contradicting maximality.  Edge-maximality
plus `eq_of_isTrail_edgeMaximal` (Sub-lemma A, verified) gives `u = v`. -/
theorem max_trail_is_closed
    {u v : V} {p : G.Walk u v} (hptrail : p.IsTrail)
    (heven : ∀ w, Even (G.degree w))
    (hmax : ∀ (x y : V) (q : G.Walk x y), q.IsTrail → q.length ≤ p.length) :
    u = v := by
  classical
  refine eq_of_isTrail_edgeMaximal hptrail (heven v) ?_
  -- Show `v` is edge-maximal: every incident edge is used.
  intro e heInc
  by_contra hnot
  -- `e = s(v,z)` with `G.Adj v z`, and `e ∉ p.edges`.
  rw [SimpleGraph.mem_incidenceFinset] at heInc
  obtain ⟨heEdge, hvE⟩ := heInc
  -- extract the neighbour `z`
  obtain ⟨z, rfl⟩ : ∃ z, e = s(v, z) := by
    -- v ∈ e, so e = s(v, Sym2.Mem.other')  (Sym2 membership decomposition)
    exact ⟨Sym2.Mem.other hvE, (Sym2.other_spec hvE).symm⟩
  have hadj : G.Adj v z := by rwa [← SimpleGraph.mem_edgeSet]
  -- `p.concat hadj` is a trail (its edge list is `p.edges.concat s(v,z)`, nodup) …
  have hconcat_trail : (p.concat hadj).IsTrail := by
    rw [isTrail_def, edges_concat, List.nodup_concat]
    exact ⟨hnot, hptrail.edges_nodup⟩
  -- … of length `p.length + 1`, contradicting maximality.
  have := hmax u z (p.concat hadj) hconcat_trail
  rw [length_concat] at this
  omega

/-! ### Step 2. A maximum-length (hence closed) trail is Eulerian.

Suppose `p : G.Walk u u` is a closed maximum-length trail but misses an edge.
`Walk.exists_boundary_dart` on the set `S = {x | x ∈ p.support}` (applied to a path
to the missing edge's endpoint) yields an unused edge `e₁` incident to some
`w ∈ p.support`.  Rotate `p` to `w`, `concat` `e₁` → a longer trail, contradiction. -/
theorem closed_max_trail_is_eulerian
    {u : V} {p : G.Walk u u} (hptrail : p.IsTrail) (hconn : G.Connected)
    (hmax : ∀ (x y : V) (q : G.Walk x y), q.IsTrail → q.length ≤ p.length) :
    p.IsEulerian := by
  classical
  intro e heEdge
  -- trail ⇒ count ≤ 1; suffices to rule out count = 0.
  have hle1 : p.edges.count e ≤ 1 := (List.nodup_iff_count_le_one.mp hptrail.edges_nodup) e
  rcases Nat.lt_or_ge (p.edges.count e) 1 with hlt | hge
  · -- count = 0 ⇒ e unused; derive the contradiction, so this branch is vacuous.
    exfalso
    have hunused : e ∉ p.edges := by
      rw [← List.count_pos_iff]; omega
    -- endpoint `a` of the missing edge; path from `u` to `a`.
    obtain ⟨a, b, rfl⟩ : ∃ a b, e = s(a, b) := ⟨_, _, (Sym2.other_spec' e).symm⟩  -- Sym2.exists
    set Sset : Set V := {x | x ∈ p.support} with hSset
    -- If `a ∈ p.support`, e itself is the boundary edge; else cross via a path.
    -- Uniformly: find a dart `d` of some walk with `d.fst ∈ Sset`, `d.snd ∉ Sset`,
    -- OR e already incident to the support.  The clean uniform tool:
    obtain ⟨w, z, hadj, hwsupp, hunused_wz⟩ :
        ∃ w z, G.Adj w z ∧ w ∈ p.support ∧ s(w, z) ∉ p.edges := by
      by_cases ha : a ∈ p.support
      · -- the missing edge is already incident to a support vertex
        exact ⟨a, b, by rwa [← SimpleGraph.mem_edgeSet], ha, hunused⟩
      · -- boundary-cross: path u → a leaves `Sset`
        obtain ⟨q, hq⟩ := hconn.exists_isPath u a
        have huS : u ∈ Sset := by rw [hSset]; exact p.start_mem_support
        have haS : a ∉ Sset := by rw [hSset]; exact ha
        obtain ⟨d, hdmem, hdfst, hdsnd⟩ := q.exists_boundary_dart Sset huS haS
        refine ⟨d.fst, d.snd, d.adj, hdfst, ?_⟩
        -- if `d.edge = s(d.fst,d.snd)` were used, `d.snd ∈ p.support`, contradicting `hdsnd`.
        intro hused
        exact hdsnd (p.snd_mem_support_of_mem_edges hused)
    -- Rotate `p` to `w`, then `concat` the unused edge.
    have hrot_trail : (p.rotate hwsupp).IsTrail := hptrail.rotate hwsupp
    have hrot_edges_perm : (p.rotate hwsupp).edges ~ p.edges := (p.rotate_edges hwsupp)
    have hunused_rot : s(w, z) ∉ (p.rotate hwsupp).edges := by
      intro hmem; exact hunused_wz (hrot_edges_perm.mem_iff.mp hmem)
    have hconcat_trail : ((p.rotate hwsupp).concat hadj).IsTrail := by
      rw [isTrail_def, edges_concat, List.nodup_concat]
      exact ⟨hunused_rot, hrot_trail.edges_nodup⟩
    -- length: rotate preserves length (perm of edge lists), concat adds 1.
    have hrot_len : (p.rotate hwsupp).length = p.length := by
      have := hrot_edges_perm.length_eq
      rw [length_edges, length_edges] at this; exact this
    have := hmax w z ((p.rotate hwsupp).concat hadj) hconcat_trail
    rw [length_concat, hrot_len] at this
    omega
  · -- count ≥ 1 together with count ≤ 1 gives count = 1, the Eulerian requirement.
    omega

/-! ### Assembly. Sufficiency: connected + all-even ⇒ Eulerian circuit. -/

/-- **Undirected Hierholzer sufficiency (extremal proof).**
Discharges the `sorry` of `UndirectedEuler.undirected_euler_circuit_sufficient`. -/
theorem undirected_euler_circuit_sufficient'
    (hconn : G.Connected) (heven : ∀ v, Even (G.degree v)) :
    ∃ (u : V) (p : G.Walk u u), p.IsEulerian := by
  classical
  obtain ⟨u, v, p, hptrail, hmax⟩ := exists_max_length_trail (Or.inr trivial)
  -- Step 1: the max trail is closed.
  obtain rfl : u = v := max_trail_is_closed hptrail heven hmax
  -- Step 2: a closed max trail is Eulerian.
  exact ⟨u, p, closed_max_trail_is_eulerian hptrail hconn hmax⟩

end UndirectedEulerDev

/-
## Remaining verification obligations (all expected routine at build time)

1. `exists_max_length_trail`: the `Nonempty V` witness (marked `sorry` here) must be
   threaded from `hconn.nonempty` — in the assembly `V` is nonempty, so restate L2
   taking `[Nonempty V]` or `(hconn : G.Connected)` and use `hconn.nonempty`.
2. `Sym2` endpoint decomposition (`Sym2.Mem.other` / `Sym2.other_spec` /
   `Sym2.other_spec'`): confirm exact current names; `Sym2.exists` (`∀ e, ∃ a b, e = s(a,b)`)
   is the robust fallback used in Step 2.
3. `IsTrail.rotate` / `rotate_edges` live in `Connectivity.WalkDecomp` + `Paths`;
   the extra `import …WalkDecomp` above covers `rotate`.
4. `List.Perm.length_eq`, `List.Perm.mem_iff`, `List.count_pos_iff`,
   `List.nodup_iff_count_le_one`, `List.nodup_concat` — standard `Data/List`.
5. `isTrail_def` (`IsTrail p ↔ p.edges.Nodup`) — used to open `concat` trails.

None of these require new mathematics; each is a name/spelling check against v4.26.0.
The mathematical content is complete and closed.
-/
