/-
  Quantitative Triangle Removal: Packing–Covering Duality

  Parent problem: szemeredi-counting — "What are the optimal quantitative
  bounds for the triangle removal lemma?"

  The triangle removal lemma states: for every δ > 0 there is γ > 0 such that
  any n-vertex graph with ≤ γn³ triangles can be made triangle-free by deleting
  ≤ δn² edges.  The *optimal* dependence γ(δ) is a famous open problem: the only
  known lower bounds (Ruzsa–Szemerédi via Behrend) force γ(δ) to be
  super-polynomially small, and no polynomial upper bound is known.

  This file isolates the abstract combinatorial object whose behaviour the
  quantitative bounds are really measuring: the **triangle removal number**
  ρ(G) = the minimum number of edges whose deletion destroys every triangle.
  We prove the two-sided bracket that governs it for an *arbitrary* finite
  graph:

        ν(G)  ≤  ρ(G)  ≤  τ(G),

  where ν(G) is the maximum size of an edge-disjoint triangle packing and τ(G)
  is the total number of triangles.  The lower inequality is weak LP duality
  for the triangle hypergraph (a König-type packing/covering bound); the upper
  inequality is the greedy "one edge per triangle" cover.

  The whole content of the removal-lemma lower-bound constructions
  (Ruzsa–Szemerédi graphs from AP-free sets, already formalized in
  `RothTriangleRemoval.lean`) is exactly an instance of the lower bracket:
  those graphs contain ν(G) = |A|·N edge-disjoint triangles, so ρ(G) ≥ |A|·N.
  The *gap* between ν and τ — the integrality gap of this LP — is the quantity
  that makes the optimal γ(δ) super-polynomial.

  Main results:
  * `cliqueFree_deleteEdges_iff_covers` — the bridge: deleting an edge set F
    yields a triangle-free graph iff F meets every triangle (edge cover).
  * `packing_card_le_cover_card`        — WEAK DUALITY: |packing| ≤ |cover|.
  * `exists_cover_card_le_numTriangles` — greedy cover of size ≤ #triangles.
  * `packing_card_le_removalNumber`     — ν(G) ≤ ρ(G).
  * `removalNumber_le_numTriangles`     — ρ(G) ≤ τ(G).
  * `packing_le_removal_le_numTriangles`— the headline bracket ν ≤ ρ ≤ τ.

  Self-contained over Mathlib's `SimpleGraph`; 0 axioms, 0 sorries.
-/
import Mathlib

namespace Szemeredi.TriangleRemoval.Bounds

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: TRIANGLES, COVERS, AND PACKINGS
-- ═══════════════════════════════════════════════════════════════════

/-- A triangle of `G` is a 3-element clique (its three vertices are pairwise
    adjacent).  We use Mathlib's `IsNClique 3`. -/
abbrev IsTriangle (G : SimpleGraph V) (s : Finset V) : Prop := G.IsNClique 3 s

/-- An edge set `F` *covers* a triangle `s` if it contains one of the three
    edges of `s`. -/
def TriangleCoveredBy (F : Finset (Sym2 V)) (s : Finset V) : Prop :=
  ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ s(x, y) ∈ F

/-- `F` is a **triangle edge cover** of `G` if deleting its edges makes `G`
    triangle-free.  This is the quantity the removal lemma deletes. -/
def IsTriangleEdgeCover (G : SimpleGraph V) (F : Finset (Sym2 V)) : Prop :=
  (G.deleteEdges (F : Set (Sym2 V))).CliqueFree 3

/-- An **edge-disjoint triangle packing**: a finite family of triangles of `G`
    no two of which share an edge.  Two distinct triangles share an edge iff
    they share two vertices, so edge-disjointness is `|s ∩ t| ≤ 1`. -/
def IsTrianglePacking (G : SimpleGraph V) (P : Finset (Finset V)) : Prop :=
  (∀ s ∈ P, IsTriangle G s) ∧
    (P : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1)

-- ═══════════════════════════════════════════════════════════════════
-- PART II: THE BRIDGE — DELETING EDGES IS TRIANGLE-FREE IFF COVER
-- ═══════════════════════════════════════════════════════════════════

omit [Fintype V] [DecidableEq V] in
/-- Deleting the edge set `F` makes `G` triangle-free **iff** `F` contains an
    edge of every triangle of `G`.  This identifies edge covers (combinatorics)
    with triangle-freeness (the removal lemma's conclusion). -/
theorem cliqueFree_deleteEdges_iff_covers (G : SimpleGraph V)
    (F : Finset (Sym2 V)) :
    IsTriangleEdgeCover G F ↔ ∀ s, IsTriangle G s → TriangleCoveredBy F s := by
  constructor
  · -- Cover ⟹ every triangle is met.
    intro hCF s hs
    by_contra hnc
    -- `hnc`: no edge of `s` lies in `F`; show `s` survives deletion.
    simp only [TriangleCoveredBy] at hnc
    push_neg at hnc
    apply hCF s
    refine ⟨?_, hs.2⟩
    intro x hx y hy hxy
    have hGadj : G.Adj x y := hs.1 hx hy hxy
    have hnotin : s(x, y) ∉ (F : Set (Sym2 V)) := by
      simp only [Finset.mem_coe]
      exact hnc x hx y hy hxy
    rw [SimpleGraph.deleteEdges_adj]
    exact ⟨hGadj, hnotin⟩
  · -- Every triangle met ⟹ deletion is triangle-free.
    intro hcov s hs
    -- `s` is a triangle in the deleted graph; it is also a triangle of `G`.
    have hsG : IsTriangle G s := by
      refine ⟨?_, hs.2⟩
      intro x hx y hy hxy
      exact (SimpleGraph.deleteEdges_adj.1 (hs.1 hx hy hxy)).1
    obtain ⟨x, hx, y, hy, hxy, hxyF⟩ := hcov s hsG
    -- But in the deleted graph that edge is gone — contradiction with clique.
    have hadj : (G.deleteEdges (F : Set (Sym2 V))).Adj x y := hs.1 hx hy hxy
    have hnot : s(x, y) ∉ (F : Set (Sym2 V)) :=
      (SimpleGraph.deleteEdges_adj.1 hadj).2
    exact hnot (by simpa using hxyF)

-- ═══════════════════════════════════════════════════════════════════
-- PART III: WEAK DUALITY — |PACKING| ≤ |COVER|
-- ═══════════════════════════════════════════════════════════════════

omit [Fintype V] in
/-- **Weak duality for the triangle hypergraph.**  Any edge-disjoint triangle
    packing has at most as many triangles as any edge cover has edges:
    `|P| ≤ |F|`.

    Proof: each triangle in `P` is covered by some edge of `F`; assign to each
    triangle one such edge.  Two triangles assigned the same edge would share
    that edge, i.e. share two vertices, contradicting edge-disjointness.  Hence
    the assignment is injective and `|P| ≤ |F|`. -/
theorem packing_card_le_cover_card (G : SimpleGraph V)
    {P : Finset (Finset V)} {F : Finset (Sym2 V)}
    (hP : IsTrianglePacking G P) (hF : IsTriangleEdgeCover G F) :
    P.card ≤ F.card := by
  classical
  -- For each triangle of `P` choose a covering edge of `F`.
  have hcov := (cliqueFree_deleteEdges_iff_covers G F).1 hF
  have hchoose : ∀ s, s ∈ P →
      ∃ e, e ∈ F ∧ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ e = s(x, y) := by
    intro s hs
    obtain ⟨x, hx, y, hy, hxy, hmem⟩ := hcov s (hP.1 s hs)
    exact ⟨s(x, y), hmem, x, hx, y, hy, hxy, rfl⟩
  -- The choice function on the attached domain (no junk values needed).
  set f : {s // s ∈ P} → Sym2 V :=
    fun s => Classical.choose (hchoose s.1 s.2) with hf_def
  have hf_spec : ∀ s : {s // s ∈ P},
      f s ∈ F ∧ ∃ x ∈ s.1, ∃ y ∈ s.1, x ≠ y ∧ f s = s(x, y) :=
    fun s => Classical.choose_spec (hchoose s.1 s.2)
  -- `P.attach.card = P.card`, so it suffices to inject `P.attach` into `F`.
  rw [← Finset.card_attach (s := P)]
  apply Finset.card_le_card_of_injOn f
  · -- maps into `F`
    intro s _
    exact (hf_spec s).1
  · -- injective on `P.attach`
    intro a _ b _ hab
    obtain ⟨hFa, xa, hxa, ya, hya, hxya, hea⟩ := hf_spec a
    obtain ⟨hFb, xb, hxb, yb, hyb, hxyb, heb⟩ := hf_spec b
    -- The chosen edges coincide, so their endpoint pairs coincide.
    have hedge : s(xa, ya) = s(xb, yb) := by rw [← hea, ← heb, hab]
    -- Endpoints of `a`'s edge lie in `b` as well.
    have hxb_yb : xa ∈ b.1 ∧ ya ∈ b.1 := by
      rcases (Sym2.eq_iff).1 hedge with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1 ▸ hxb, h2 ▸ hyb⟩
      · exact ⟨h1 ▸ hyb, h2 ▸ hxb⟩
    -- So `a` and `b` share two distinct vertices.
    by_contra hne
    have hab' : a.1 ≠ b.1 := fun h => hne (Subtype.ext h)
    have hle : (a.1 ∩ b.1).card ≤ 1 :=
      hP.2 a.2 b.2 hab'
    have h2le : 2 ≤ (a.1 ∩ b.1).card := by
      have hxmem : xa ∈ a.1 ∩ b.1 := Finset.mem_inter.2 ⟨hxa, hxb_yb.1⟩
      have hymem : ya ∈ a.1 ∩ b.1 := Finset.mem_inter.2 ⟨hya, hxb_yb.2⟩
      have : 1 < (a.1 ∩ b.1).card :=
        Finset.one_lt_card.2 ⟨xa, hxmem, ya, hymem, hxya⟩
      omega
    omega

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: GREEDY UPPER BOUND — COVER OF SIZE ≤ #TRIANGLES
-- ═══════════════════════════════════════════════════════════════════

open Classical in
/-- The (finite) set of all triangles of `G`. -/
noncomputable def triangles (G : SimpleGraph V) : Finset (Finset V) :=
  (Finset.univ : Finset (Finset V)).filter (fun s => IsTriangle G s)

/-- The total number of triangles `τ(G)`. -/
noncomputable def numTriangles (G : SimpleGraph V) : ℕ := (triangles G).card

@[simp] theorem mem_triangles {G : SimpleGraph V} {s : Finset V} :
    s ∈ triangles G ↔ IsTriangle G s := by
  classical
  simp only [triangles, Finset.mem_filter, Finset.mem_univ, true_and]

omit [Fintype V] [DecidableEq V] in
/-- Every triangle, being a 3-clique, has an explicit edge `s(x,y)` with
    `x ≠ y` both in it. -/
theorem IsTriangle.exists_edge {G : SimpleGraph V} {s : Finset V}
    (hs : IsTriangle G s) : ∃ x ∈ s, ∃ y ∈ s, x ≠ y := by
  have h2 : 1 < s.card := by rw [hs.2]; norm_num
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 h2
  exact ⟨x, hx, y, hy, hxy⟩

/-- **Greedy cover.**  Selecting one edge from each triangle yields a triangle
    edge cover of size at most the number of triangles: `ρ(G) ≤ τ(G)` in
    witnessed form. -/
theorem exists_cover_card_le_numTriangles (G : SimpleGraph V) :
    ∃ F : Finset (Sym2 V),
      IsTriangleEdgeCover G F ∧ F.card ≤ numTriangles G := by
  classical
  -- Choose one edge per triangle.
  have hpick : ∀ s, s ∈ triangles G → ∃ e : Sym2 V,
      ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ e = s(x, y) := by
    intro s hs
    obtain ⟨x, hx, y, hy, hxy⟩ := (mem_triangles.1 hs).exists_edge
    exact ⟨s(x, y), x, hx, y, hy, hxy, rfl⟩
  set g : {s // s ∈ triangles G} → Sym2 V :=
    fun s => Classical.choose (hpick s.1 s.2) with hg_def
  have hg_spec : ∀ s : {s // s ∈ triangles G},
      ∃ x ∈ s.1, ∃ y ∈ s.1, x ≠ y ∧ g s = s(x, y) :=
    fun s => Classical.choose_spec (hpick s.1 s.2)
  refine ⟨(triangles G).attach.image g, ?_, ?_⟩
  · -- It is a cover: every triangle's chosen edge is included.
    rw [cliqueFree_deleteEdges_iff_covers]
    intro s hs
    have hsmem : s ∈ triangles G := mem_triangles.2 hs
    obtain ⟨x, hx, y, hy, hxy, hgeq⟩ := hg_spec ⟨s, hsmem⟩
    refine ⟨x, hx, y, hy, hxy, ?_⟩
    rw [← hgeq]
    exact Finset.mem_image.2 ⟨⟨s, hsmem⟩, Finset.mem_attach _ _, rfl⟩
  · -- Size bound: image of an `attach` is no bigger than `#triangles`.
    calc ((triangles G).attach.image g).card
        ≤ (triangles G).attach.card := Finset.card_image_le
      _ = (triangles G).card := Finset.card_attach
      _ = numTriangles G := rfl

-- ═══════════════════════════════════════════════════════════════════
-- PART V: THE REMOVAL NUMBER AND THE BRACKET ν ≤ ρ ≤ τ
-- ═══════════════════════════════════════════════════════════════════

/-- The **triangle removal number** `ρ(G)`: the minimum number of edges whose
    deletion makes `G` triangle-free.  This is exactly the per-graph quantity
    the triangle removal lemma bounds. -/
noncomputable def removalNumber (G : SimpleGraph V) : ℕ :=
  sInf {m | ∃ F : Finset (Sym2 V), F.card = m ∧ IsTriangleEdgeCover G F}

/-- The set of cover sizes is nonempty (the greedy cover is a member), so the
    infimum defining `ρ(G)` is attained. -/
theorem removalNumber_mem (G : SimpleGraph V) :
    ∃ F : Finset (Sym2 V), F.card = removalNumber G ∧ IsTriangleEdgeCover G F := by
  have hne : {m | ∃ F : Finset (Sym2 V), F.card = m ∧ IsTriangleEdgeCover G F}.Nonempty := by
    obtain ⟨F, hF, _⟩ := exists_cover_card_le_numTriangles G
    exact ⟨F.card, F, rfl, hF⟩
  exact Nat.sInf_mem hne

/-- **Lower bracket** `ν(G) ≤ ρ(G)`: every edge-disjoint triangle packing has
    at most `ρ(G)` triangles.  In particular the maximum packing size is a
    lower bound for the removal number. -/
theorem packing_card_le_removalNumber (G : SimpleGraph V)
    {P : Finset (Finset V)} (hP : IsTrianglePacking G P) :
    P.card ≤ removalNumber G := by
  obtain ⟨F, hFcard, hFcov⟩ := removalNumber_mem G
  calc P.card ≤ F.card := packing_card_le_cover_card G hP hFcov
    _ = removalNumber G := hFcard

/-- **Upper bracket** `ρ(G) ≤ τ(G)`: the removal number never exceeds the total
    number of triangles. -/
theorem removalNumber_le_numTriangles (G : SimpleGraph V) :
    removalNumber G ≤ numTriangles G := by
  obtain ⟨F, hFcov, hFle⟩ := exists_cover_card_le_numTriangles G
  have hmem : F.card ∈
      {m | ∃ F : Finset (Sym2 V), F.card = m ∧ IsTriangleEdgeCover G F} :=
    ⟨F, rfl, hFcov⟩
  calc removalNumber G ≤ F.card := Nat.sInf_le hmem
    _ ≤ numTriangles G := hFle

/-- **The quantitative-bounds bracket** for the triangle removal number of an
    arbitrary finite graph:

        ν(G)  ≤  ρ(G)  ≤  τ(G).

    Every edge-disjoint triangle packing lower-bounds the number of edges that
    must be removed, and the total triangle count upper-bounds it.  The optimal
    triangle removal lemma constant `γ(δ)` is governed precisely by how large
    the gap `ρ/τ` (equivalently the LP integrality gap `ν` vs. `τ`) can be —
    the quantity that Ruzsa–Szemerédi / Behrend constructions push to be
    super-polynomially small. -/
theorem packing_le_removal_le_numTriangles (G : SimpleGraph V)
    {P : Finset (Finset V)} (hP : IsTrianglePacking G P) :
    P.card ≤ removalNumber G ∧ removalNumber G ≤ numTriangles G :=
  ⟨packing_card_le_removalNumber G hP, removalNumber_le_numTriangles G⟩

-- ═══════════════════════════════════════════════════════════════════
-- PART VI: SHARPNESS — A TRIANGLE-FREE GRAPH HAS ρ = 0
-- ═══════════════════════════════════════════════════════════════════

omit [Fintype V] [DecidableEq V] in
/-- For a triangle-free graph the empty edge set is already a cover, so its
    removal number is `0` — the bracket bottoms out at `ν = ρ = τ = 0`. -/
theorem removalNumber_eq_zero_of_cliqueFree (G : SimpleGraph V)
    (hG : G.CliqueFree 3) : removalNumber G = 0 := by
  have hcov : IsTriangleEdgeCover G (∅ : Finset (Sym2 V)) := by
    unfold IsTriangleEdgeCover
    have : G.deleteEdges (∅ : Set (Sym2 V)) = G := by
      simp [SimpleGraph.deleteEdges_empty]
    rw [Finset.coe_empty, this]
    exact hG
  have hmem : (0 : ℕ) ∈
      {m | ∃ F : Finset (Sym2 V), F.card = m ∧ IsTriangleEdgeCover G F} :=
    ⟨∅, Finset.card_empty, hcov⟩
  exact Nat.le_zero.1 (Nat.sInf_le hmem)

end Szemeredi.TriangleRemoval.Bounds
