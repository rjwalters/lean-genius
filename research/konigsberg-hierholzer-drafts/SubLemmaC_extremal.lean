/-
# Sub-lemma C (undirected Hierholzer sufficiency) — EXTREMAL BLUEPRINT

STATUS: verify-ready DRAFT, NOT yet machine-checked (dual-tool blackout:
Aristotle backend 404 + Docker containerd meta.db I/O error prevent building).
Every lemma name and signature below was cross-checked against the local
`leanprover/lean4:v4.26.0` Mathlib checkout at /Users/rwalters/GitHub/mathlib4
(the same toolchain proofs/ pins). This file lives OUTSIDE `proofs/` so the
lake glob `Proofs.*` never compiles it; drop the bodies into
`proofs/Proofs/KonigsbergOQ02OQ01OQ02OQ01Dev.lean` once a build host is available.

CORRECTIONS (this pass — three bugs an inspection-only "verify-ready" tag missed,
each fixed against the actual v4.26.0 source, not from memory):
  * `Walk.rotate_edges` returns `~r` (`List.IsRotated`), NOT `~` (`List.Perm`).
    The membership step uses `IsRotated.mem_iff` directly; the length step goes
    through `.perm` (`IsRotated.perm : l ~r l' → l ~ l'`) then `.length_eq`.
    Mathlib's own `Paths.lean:497` uses this exact idiom:
    `rw [isTrail_def, (c.rotate_edges h).perm.nodup_iff]`.
  * Decomposing an arbitrary `e : Sym2 V` into `∃ a b, e = s(a,b)` cannot use
    `Sym2.other_spec'` (which needs a membership proof); it is `Sym2.exists.mp ⟨e, rfl⟩`
    (`Sym2.«exists» : (∃ x, f x) ↔ ∃ x y, f s(x,y)`, Sym2.lean:155).
  * L2's `Nonempty V` witness (was a `sorry`) is now a proper `[Nonempty V]`
    hypothesis, discharged in the assembly by `hconn.nonempty`.

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
  Walk.rotate_edges            Connectivity/WalkDecomp.lean:294  (rotate).edges ~r edges  [IsRotated, not Perm!]
  IsTrail.rotate               Paths.lean:495        (hc.rotate h : (c.rotate h).IsTrail)
  IsRotated.perm               Data/List/Rotate.lean:397  l ~r l' → l ~ l'
  IsRotated.mem_iff            Data/List/Rotate.lean:403  (l ~r l') → (a∈l ↔ a∈l')
  Sym2.«exists»                Data/Sym/Sym2.lean:155  (∃x, f x) ↔ ∃ x y, f s(x,y)
  Sym2.Mem.other / other_spec  Data/Sym/Sym2.lean:353,357  s(a, Mem.other h) = z
  Dart.adj  (structure field)  Dart.lean:28          G.Adj d.fst d.snd  (@[simp] :33)
  Connected.exists_isPath      Connectivity/Connected.lean:318
  Walk.snd_mem_support_of_mem_edges  Walks/Operations.lean:450
  List.nodup_concat            Data/List/Nodup.lean:242   (l.concat u).Nodup ↔ u∉l ∧ l.Nodup
  List.nodup_iff_count_le_one  Data/List/Nodup.lean:140
  List.count_pos_iff           Data/List/Nodup.lean:147   0 < count a l ↔ a ∈ l
  isTrail_def  (@[mk_iff])      Paths.lean:67          IsTrail p ↔ p.edges.Nodup
  mem_edgeFinset               Finite.lean:66
  IsTrail.length_le_card_edgeFinset  Paths.lean:176    w.length ≤ G.edgeFinset.card  (= our old L1)
  Nat.sSup_mem                 Data/Nat/Lattice.lean:148   s.Nonempty → BddAbove s → sSup s ∈ s
  le_csSup                     Order/ConditionallyCompleteLattice/Basic.lean:185   BddAbove s → a∈s → a ≤ sSup s
  eq_of_isTrail_edgeMaximal    KonigsbergOQ02OQ01OQ02OQ01Dev.lean  (VERIFIED, Sub-lemma A)
-/
import Mathlib.Combinatorics.SimpleGraph.Trails
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp
import Mathlib.Tactic

open SimpleGraph SimpleGraph.Walk

namespace UndirectedEulerDev

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [Fintype V] [DecidableRel G.Adj]

/-! ### L1 + L2. A maximum-length trail exists.

L1 (a trail's length is bounded by `G.edgeFinset.card`) is exactly Mathlib's
`SimpleGraph.Walk.IsTrail.length_le_card_edgeFinset` (`Paths.lean:176`), so we no
longer hand-roll it — the library proof is literally the one we had written.  Given
that a-priori bound, the achievable trail lengths form a nonempty (`nil` has length 0)
bounded-above subset of `ℕ`, hence attain their supremum (`Nat.sSup_mem`,
`Data/Nat/Lattice.lean:148`); a witnessing trail of that supremal length is the
maximum, with `le_csSup` (`ConditionallyCompleteLattice/Basic.lean:185`) discharging
the universal bound. -/

/-- Among all trails of `G` (any endpoints) there is one of maximum length.
Packaged with the maximality witness in the form Steps 1–2 consume:
`∀ trail q, q.length ≤ p.length`.

Formulated over the `Set ℕ` of achievable lengths and closed by `Nat.sSup_mem` /
`le_csSup`; this avoids `Finset.filter` on the undecidable predicate
`∃ u v p, p.IsTrail ∧ p.length = n`, removing the only elaboration risk the earlier
`Finset.max'` draft carried. -/
theorem exists_max_length_trail [Nonempty V] :
    ∃ (u v : V) (p : G.Walk u v), p.IsTrail ∧
      ∀ (x y : V) (q : G.Walk x y), q.IsTrail → q.length ≤ p.length := by
  classical
  -- The achievable trail lengths as a `Set ℕ` — no decidability instance needed.
  have hTne :
      {n | ∃ (u v : V) (p : G.Walk u v), p.IsTrail ∧ p.length = n}.Nonempty := by
    -- the empty walk at any vertex is a trail of length 0
    obtain ⟨w⟩ := (inferInstance : Nonempty V)
    exact ⟨0, w, w, Walk.nil, IsTrail.nil, rfl⟩
  -- Every trail length is ≤ |E| (Mathlib `IsTrail.length_le_card_edgeFinset`).
  have hTbdd :
      BddAbove {n | ∃ (u v : V) (p : G.Walk u v), p.IsTrail ∧ p.length = n} := by
    refine ⟨G.edgeFinset.card, ?_⟩
    rintro n ⟨u, v, p, hp, rfl⟩
    exact hp.length_le_card_edgeFinset
  -- The supremum is attained: a trail of maximal length exists.
  obtain ⟨u, v, p, hptrail, hplen⟩ := Nat.sSup_mem hTne hTbdd
  refine ⟨u, v, p, hptrail, ?_⟩
  intro x y q hq
  -- q.length ∈ T, so q.length ≤ sSup T = p.length.
  rw [hplen]
  exact le_csSup hTbdd ⟨x, y, q, hq, rfl⟩

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
    -- v ∈ e, so e = s(v, Sym2.Mem.other hvE)  (Sym2 membership decomposition; the
    -- noncomputable `Mem.other` is fine here — the goal is a Prop, no data escapes).
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
    obtain ⟨a, b, rfl⟩ : ∃ a b, e = s(a, b) := Sym2.exists.mp ⟨e, rfl⟩
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
    -- `rotate_edges` gives `~r` (IsRotated), NOT `~` (Perm); bridge with `.perm` when needed.
    have hrot_edges_rot : (p.rotate hwsupp).edges ~r p.edges := p.rotate_edges hwsupp
    have hunused_rot : s(w, z) ∉ (p.rotate hwsupp).edges := by
      intro hmem; exact hunused_wz (hrot_edges_rot.mem_iff.mp hmem)
    have hconcat_trail : ((p.rotate hwsupp).concat hadj).IsTrail := by
      rw [isTrail_def, edges_concat, List.nodup_concat]
      exact ⟨hunused_rot, hrot_trail.edges_nodup⟩
    -- length: rotate preserves length (IsRotated ⇒ Perm ⇒ equal length of edge lists), concat adds 1.
    have hrot_len : (p.rotate hwsupp).length = p.length := by
      have := hrot_edges_rot.perm.length_eq
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
  haveI : Nonempty V := hconn.nonempty
  obtain ⟨u, v, p, hptrail, hmax⟩ := exists_max_length_trail
  -- Step 1: the max trail is closed.
  obtain rfl : u = v := max_trail_is_closed hptrail heven hmax
  -- Step 2: a closed max trail is Eulerian.
  exact ⟨u, p, closed_max_trail_is_eulerian hptrail hconn hmax⟩

end UndirectedEulerDev

/-
## Verification obligations — status after the correction pass

All five items below were checked against the actual v4.26.0 source (paths/lines in
the anchor block at the top of the file), and the three that were genuinely wrong
have been FIXED in the bodies above:

1. [FIXED] `exists_max_length_trail` now takes `[Nonempty V]` (was a `sorry`); the
   assembly discharges it with `haveI : Nonempty V := hconn.nonempty`.
2. [FIXED] `Sym2` decomposition of an arbitrary edge uses `Sym2.exists.mp ⟨e, rfl⟩`
   (Sym2.lean:155); `Sym2.other_spec'` was wrong there — it needs a membership proof.
   Step 1's `∃ z, e = s(v,z)` (with `hvE : v ∈ e`) correctly uses `Sym2.Mem.other` +
   `Sym2.other_spec` (Sym2.lean:353,357).
3. [FIXED] `Walk.rotate_edges` gives `~r` (`List.IsRotated`, WalkDecomp.lean:294),
   not `~`. Membership: `IsRotated.mem_iff` (Rotate.lean:403). Length: `.perm`
   (`IsRotated.perm`, Rotate.lean:397) then `List.Perm.length_eq`. `IsTrail.rotate`
   (Paths.lean:495) confirmed; `import …WalkDecomp` covers `Walk.rotate`.
4. [CONFIRMED] `List.count_pos_iff` (Nodup.lean:147), `List.nodup_iff_count_le_one`
   (Nodup.lean:140), `List.nodup_concat` (Nodup.lean:242) — all present as used.
5. [CONFIRMED] `isTrail_def` (`@[mk_iff]`, Paths.lean:67) — used to open `concat` trails.

6. [DE-RISKED, this pass] L2 (`exists_max_length_trail`) was rebuilt to run over the
   `Set ℕ` of achievable lengths using `Nat.sSup_mem` (Data/Nat/Lattice.lean:148) +
   `le_csSup` (ConditionallyCompleteLattice/Basic.lean:185), and the hand-rolled L1
   was deleted in favour of Mathlib's `IsTrail.length_le_card_edgeFinset`
   (Paths.lean:176 — its library proof is verbatim our old L1). This removes BOTH the
   old `Finset.filter`-on-an-undecidable-predicate instance-resolution risk AND ~18
   lines of hand-rolled a-priori-bound proof. Every name/signature used was read from
   the local v4.26.0 source this session.

No new mathematics is required and no `sorry` remains in the blueprint. The only
remaining elaboration risk is the unifier picking `f := (e = ·)` in
`Sym2.exists.mp ⟨e, rfl⟩` (Step 2) — L2's decidability concern is now gone. A real
build host (currently unavailable — Docker containerd meta.db EIO + Aristotle 404,
11th consecutive session) is still needed to convert this from verify-ready to
machine-checked. The mathematical content is complete and closed.
-/
