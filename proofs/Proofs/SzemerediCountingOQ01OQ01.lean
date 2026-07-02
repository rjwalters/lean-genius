/-
  Packing–Covering Duality for K_r-Freeness: the bracket ν_r ≤ ρ_r ≤ τ_r

  Parent entry: `szemeredi-counting-oq-01`
  (`Proofs/SzemerediCountingOQ01.lean`) proves, for the *triangle* (K₃) case,
  the two-sided bracket governing the triangle removal number:

        ν(G)  ≤  ρ(G)  ≤  τ(G),

  where ν is the maximum edge-disjoint triangle packing, ρ the minimum number of
  edges whose deletion destroys every triangle, and τ the total triangle count.

  This entry generalizes that whole bracket from K₃ to an **arbitrary clique
  size** `K_r` (`r ≥ 2`).  For a fixed `r` we prove, for every finite graph:

        ν_r(G)  ≤  ρ_r(G)  ≤  τ_r(G),

  where
    * `ρ_r(G)` (`rRemovalNumber`) is the minimum number of edges whose deletion
      makes `G` `K_r`-free — the per-graph quantity the `K_r`-removal lemma bounds;
    * `τ_r(G)` (`numRCliques`) is the total number of `K_r`'s;
    * `ν_r(G)` is witnessed by any **edge-disjoint** `K_r`-packing.

  ## A correction to the "shared-vertex bound"

  One might be tempted (as the problem note suggests) to define edge-disjointness
  of `K_r`'s by the shared-vertex bound `|s ∩ t| ≤ r − 2`.  That is **incorrect**
  for `r ≥ 4`: two `r`-cliques share an *edge* iff they share **two** vertices, so
  the genuine edge-disjointness condition is `|s ∩ t| ≤ 1`, uniformly in `r`.
  (The two conditions coincide only at `r = 3`, where `r − 2 = 1`, which is why the
  triangle parent could write either.)  The weak-duality injection below needs
  exactly `|s ∩ t| ≤ 1`: two cliques assigned the same covering edge share both of
  its endpoints, i.e. share two vertices — a contradiction only under `|s∩t| ≤ 1`.
  Using `r − 2` for `r ≥ 4` would let two edge-sharing cliques be double-counted and
  the bracket would be false.  We therefore adopt `|s ∩ t| ≤ 1`.

  ## Main results (0 sorry, 0 axiom)
  * `cliqueFree_deleteEdges_iff_rCovers` — the bridge: `G.deleteEdges F` is
    `K_r`-free iff `F` contains an edge of every `K_r` of `G`.
  * `rPacking_card_le_cover_card`        — WEAK DUALITY: |packing| ≤ |cover|.
  * `exists_cover_card_le_numRCliques`   — greedy cover of size ≤ #`K_r`'s.
  * `rPacking_card_le_rRemovalNumber`    — ν_r(G) ≤ ρ_r(G).
  * `rRemovalNumber_le_numRCliques`      — ρ_r(G) ≤ τ_r(G).
  * `rPacking_le_removal_le_numRCliques` — the headline bracket ν_r ≤ ρ_r ≤ τ_r.
  * `rRemovalNumber_eq_zero_of_cliqueFree` — sharpness: `K_r`-free ⟹ ρ_r = 0.

  Self-contained over Mathlib's `SimpleGraph`; imports only `Mathlib`.
-/
import Mathlib

namespace Szemeredi.CliqueRemoval.Bounds

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: r-CLIQUES, COVERS, AND PACKINGS
-- ═══════════════════════════════════════════════════════════════════

/-- An edge set `F` *covers* a clique `s` if it contains one of `s`'s edges. -/
def RCliqueCoveredBy (F : Finset (Sym2 V)) (s : Finset V) : Prop :=
  ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ s(x, y) ∈ F

/-- `F` is a **`K_r` edge cover** of `G` if deleting its edges makes `G`
    `K_r`-free.  This is the quantity a `K_r`-removal lemma deletes. -/
def IsRCliqueEdgeCover (r : ℕ) (G : SimpleGraph V) (F : Finset (Sym2 V)) : Prop :=
  (G.deleteEdges (F : Set (Sym2 V))).CliqueFree r

/-- An **edge-disjoint `K_r`-packing**: a finite family of `r`-cliques of `G`
    no two of which share an edge.  Two distinct cliques share an edge iff they
    share two vertices, so edge-disjointness is `|s ∩ t| ≤ 1` — for every `r`. -/
def IsRCliquePacking (r : ℕ) (G : SimpleGraph V) (P : Finset (Finset V)) : Prop :=
  (∀ s ∈ P, G.IsNClique r s) ∧
    (P : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1)

-- ═══════════════════════════════════════════════════════════════════
-- PART II: THE BRIDGE — DELETING EDGES IS K_r-FREE IFF COVER
-- ═══════════════════════════════════════════════════════════════════

omit [Fintype V] [DecidableEq V] in
/-- Deleting the edge set `F` makes `G` `K_r`-free **iff** `F` contains an edge
    of every `r`-clique of `G`.  This identifies edge covers (combinatorics)
    with `K_r`-freeness (a removal lemma's conclusion). -/
theorem cliqueFree_deleteEdges_iff_rCovers (r : ℕ) (G : SimpleGraph V)
    (F : Finset (Sym2 V)) :
    IsRCliqueEdgeCover r G F ↔ ∀ s, G.IsNClique r s → RCliqueCoveredBy F s := by
  constructor
  · -- Cover ⟹ every clique is met.
    intro hCF s hs
    by_contra hnc
    simp only [RCliqueCoveredBy] at hnc
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
  · -- Every clique met ⟹ deletion is K_r-free.
    intro hcov s hs
    have hsG : G.IsNClique r s := by
      refine ⟨?_, hs.2⟩
      intro x hx y hy hxy
      exact (SimpleGraph.deleteEdges_adj.1 (hs.1 hx hy hxy)).1
    obtain ⟨x, hx, y, hy, hxy, hxyF⟩ := hcov s hsG
    have hadj : (G.deleteEdges (F : Set (Sym2 V))).Adj x y := hs.1 hx hy hxy
    have hnot : s(x, y) ∉ (F : Set (Sym2 V)) :=
      (SimpleGraph.deleteEdges_adj.1 hadj).2
    exact hnot (by simpa using hxyF)

-- ═══════════════════════════════════════════════════════════════════
-- PART III: WEAK DUALITY — |PACKING| ≤ |COVER|
-- ═══════════════════════════════════════════════════════════════════

omit [Fintype V] in
/-- **Weak duality for the `K_r` hypergraph.**  Any edge-disjoint `K_r`-packing
    has at most as many cliques as any edge cover has edges: `|P| ≤ |F|`.

    Proof: each clique in `P` is covered by some edge of `F`; assign to each
    clique one such edge.  Two cliques assigned the same edge would share that
    edge, i.e. share two vertices, contradicting edge-disjointness `|s∩t| ≤ 1`.
    Hence the assignment is injective and `|P| ≤ |F|`. -/
theorem rPacking_card_le_cover_card (r : ℕ) (G : SimpleGraph V)
    {P : Finset (Finset V)} {F : Finset (Sym2 V)}
    (hP : IsRCliquePacking r G P) (hF : IsRCliqueEdgeCover r G F) :
    P.card ≤ F.card := by
  classical
  have hcov := (cliqueFree_deleteEdges_iff_rCovers r G F).1 hF
  have hchoose : ∀ s, s ∈ P →
      ∃ e, e ∈ F ∧ ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ e = s(x, y) := by
    intro s hs
    obtain ⟨x, hx, y, hy, hxy, hmem⟩ := hcov s (hP.1 s hs)
    exact ⟨s(x, y), hmem, x, hx, y, hy, hxy, rfl⟩
  set f : {s // s ∈ P} → Sym2 V :=
    fun s => Classical.choose (hchoose s.1 s.2) with hf_def
  have hf_spec : ∀ s : {s // s ∈ P},
      f s ∈ F ∧ ∃ x ∈ s.1, ∃ y ∈ s.1, x ≠ y ∧ f s = s(x, y) :=
    fun s => Classical.choose_spec (hchoose s.1 s.2)
  rw [← Finset.card_attach (s := P)]
  apply Finset.card_le_card_of_injOn f
  · intro s _
    exact (hf_spec s).1
  · intro a _ b _ hab
    obtain ⟨hFa, xa, hxa, ya, hya, hxya, hea⟩ := hf_spec a
    obtain ⟨hFb, xb, hxb, yb, hyb, hxyb, heb⟩ := hf_spec b
    have hedge : s(xa, ya) = s(xb, yb) := by rw [← hea, ← heb, hab]
    have hxb_yb : xa ∈ b.1 ∧ ya ∈ b.1 := by
      rcases (Sym2.eq_iff).1 hedge with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1 ▸ hxb, h2 ▸ hyb⟩
      · exact ⟨h1 ▸ hyb, h2 ▸ hxb⟩
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
-- PART IV: GREEDY UPPER BOUND — COVER OF SIZE ≤ #K_r'S
-- ═══════════════════════════════════════════════════════════════════

open Classical in
/-- The (finite) set of all `r`-cliques of `G`. -/
noncomputable def rCliques (r : ℕ) (G : SimpleGraph V) : Finset (Finset V) :=
  (Finset.univ : Finset (Finset V)).filter (fun s => G.IsNClique r s)

/-- The total number of `r`-cliques `τ_r(G)`. -/
noncomputable def numRCliques (r : ℕ) (G : SimpleGraph V) : ℕ := (rCliques r G).card

@[simp] theorem mem_rCliques {r : ℕ} {G : SimpleGraph V} {s : Finset V} :
    s ∈ rCliques r G ↔ G.IsNClique r s := by
  classical
  simp only [rCliques, Finset.mem_filter, Finset.mem_univ, true_and]

omit [Fintype V] [DecidableEq V] in
/-- Every `r`-clique with `r ≥ 2` has an explicit edge `s(x,y)` with `x ≠ y`
    both in it. -/
theorem rClique_exists_edge {r : ℕ} (hr : 2 ≤ r) {G : SimpleGraph V}
    {s : Finset V} (hs : G.IsNClique r s) : ∃ x ∈ s, ∃ y ∈ s, x ≠ y := by
  have h2 : 1 < s.card := by rw [hs.2]; omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 h2
  exact ⟨x, hx, y, hy, hxy⟩

/-- **Greedy cover.**  Selecting one edge from each `r`-clique (`r ≥ 2`) yields a
    `K_r` edge cover of size at most the number of `r`-cliques. -/
theorem exists_cover_card_le_numRCliques {r : ℕ} (hr : 2 ≤ r)
    (G : SimpleGraph V) :
    ∃ F : Finset (Sym2 V),
      IsRCliqueEdgeCover r G F ∧ F.card ≤ numRCliques r G := by
  classical
  have hpick : ∀ s, s ∈ rCliques r G → ∃ e : Sym2 V,
      ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ e = s(x, y) := by
    intro s hs
    obtain ⟨x, hx, y, hy, hxy⟩ := rClique_exists_edge hr (mem_rCliques.1 hs)
    exact ⟨s(x, y), x, hx, y, hy, hxy, rfl⟩
  set g : {s // s ∈ rCliques r G} → Sym2 V :=
    fun s => Classical.choose (hpick s.1 s.2) with hg_def
  have hg_spec : ∀ s : {s // s ∈ rCliques r G},
      ∃ x ∈ s.1, ∃ y ∈ s.1, x ≠ y ∧ g s = s(x, y) :=
    fun s => Classical.choose_spec (hpick s.1 s.2)
  refine ⟨(rCliques r G).attach.image g, ?_, ?_⟩
  · rw [cliqueFree_deleteEdges_iff_rCovers]
    intro s hs
    have hsmem : s ∈ rCliques r G := mem_rCliques.2 hs
    obtain ⟨x, hx, y, hy, hxy, hgeq⟩ := hg_spec ⟨s, hsmem⟩
    refine ⟨x, hx, y, hy, hxy, ?_⟩
    rw [← hgeq]
    exact Finset.mem_image.2 ⟨⟨s, hsmem⟩, Finset.mem_attach _ _, rfl⟩
  · calc ((rCliques r G).attach.image g).card
        ≤ (rCliques r G).attach.card := Finset.card_image_le
      _ = (rCliques r G).card := Finset.card_attach
      _ = numRCliques r G := rfl

-- ═══════════════════════════════════════════════════════════════════
-- PART V: THE REMOVAL NUMBER AND THE BRACKET ν_r ≤ ρ_r ≤ τ_r
-- ═══════════════════════════════════════════════════════════════════

/-- The **`K_r` removal number** `ρ_r(G)`: the minimum number of edges whose
    deletion makes `G` `K_r`-free. -/
noncomputable def rRemovalNumber (r : ℕ) (G : SimpleGraph V) : ℕ :=
  sInf {m | ∃ F : Finset (Sym2 V), F.card = m ∧ IsRCliqueEdgeCover r G F}

/-- The set of cover sizes is nonempty (the greedy cover is a member), so the
    infimum defining `ρ_r(G)` is attained. -/
theorem rRemovalNumber_mem {r : ℕ} (hr : 2 ≤ r) (G : SimpleGraph V) :
    ∃ F : Finset (Sym2 V), F.card = rRemovalNumber r G ∧
      IsRCliqueEdgeCover r G F := by
  have hne : {m | ∃ F : Finset (Sym2 V), F.card = m ∧
      IsRCliqueEdgeCover r G F}.Nonempty := by
    obtain ⟨F, hF, _⟩ := exists_cover_card_le_numRCliques hr G
    exact ⟨F.card, F, rfl, hF⟩
  exact Nat.sInf_mem hne

/-- **Lower bracket** `ν_r(G) ≤ ρ_r(G)`: every edge-disjoint `K_r`-packing has
    at most `ρ_r(G)` cliques. -/
theorem rPacking_card_le_rRemovalNumber {r : ℕ} (hr : 2 ≤ r)
    (G : SimpleGraph V) {P : Finset (Finset V)} (hP : IsRCliquePacking r G P) :
    P.card ≤ rRemovalNumber r G := by
  obtain ⟨F, hFcard, hFcov⟩ := rRemovalNumber_mem hr G
  calc P.card ≤ F.card := rPacking_card_le_cover_card r G hP hFcov
    _ = rRemovalNumber r G := hFcard

/-- **Upper bracket** `ρ_r(G) ≤ τ_r(G)`: the removal number never exceeds the
    total number of `r`-cliques. -/
theorem rRemovalNumber_le_numRCliques {r : ℕ} (hr : 2 ≤ r) (G : SimpleGraph V) :
    rRemovalNumber r G ≤ numRCliques r G := by
  obtain ⟨F, hFcov, hFle⟩ := exists_cover_card_le_numRCliques hr G
  have hmem : F.card ∈
      {m | ∃ F : Finset (Sym2 V), F.card = m ∧ IsRCliqueEdgeCover r G F} :=
    ⟨F, rfl, hFcov⟩
  calc rRemovalNumber r G ≤ F.card := Nat.sInf_le hmem
    _ ≤ numRCliques r G := hFle

/-- **The packing–covering bracket** for the `K_r` removal number of an
    arbitrary finite graph (`r ≥ 2`):

        ν_r(G)  ≤  ρ_r(G)  ≤  τ_r(G).

    Every edge-disjoint `K_r`-packing lower-bounds the number of edges that must
    be removed to destroy all `r`-cliques, and the total `K_r` count
    upper-bounds it.  For `r = 3` this recovers the parent's triangle bracket. -/
theorem rPacking_le_removal_le_numRCliques {r : ℕ} (hr : 2 ≤ r)
    (G : SimpleGraph V) {P : Finset (Finset V)} (hP : IsRCliquePacking r G P) :
    P.card ≤ rRemovalNumber r G ∧ rRemovalNumber r G ≤ numRCliques r G :=
  ⟨rPacking_card_le_rRemovalNumber hr G hP, rRemovalNumber_le_numRCliques hr G⟩

-- ═══════════════════════════════════════════════════════════════════
-- PART VI: SHARPNESS — A K_r-FREE GRAPH HAS ρ_r = 0
-- ═══════════════════════════════════════════════════════════════════

omit [Fintype V] [DecidableEq V] in
/-- For a `K_r`-free graph the empty edge set is already a cover, so its removal
    number is `0` — the bracket bottoms out at `ν_r = ρ_r = τ_r = 0`. -/
theorem rRemovalNumber_eq_zero_of_cliqueFree (r : ℕ) (G : SimpleGraph V)
    (hG : G.CliqueFree r) : rRemovalNumber r G = 0 := by
  have hcov : IsRCliqueEdgeCover r G (∅ : Finset (Sym2 V)) := by
    unfold IsRCliqueEdgeCover
    have : G.deleteEdges (∅ : Set (Sym2 V)) = G := by
      simp [SimpleGraph.deleteEdges_empty]
    rw [Finset.coe_empty, this]
    exact hG
  have hmem : (0 : ℕ) ∈
      {m | ∃ F : Finset (Sym2 V), F.card = m ∧ IsRCliqueEdgeCover r G F} :=
    ⟨∅, Finset.card_empty, hcov⟩
  exact Nat.le_zero.1 (Nat.sInf_le hmem)

-- ═══════════════════════════════════════════════════════════════════
-- PART VII: r = 3 RECOVERS THE TRIANGLE BRACKET
-- ═══════════════════════════════════════════════════════════════════

/-- Sanity specialization: at `r = 3` the bracket is exactly the parent's
    triangle packing–covering bracket `ν ≤ ρ ≤ τ`. -/
theorem triangle_bracket (G : SimpleGraph V) {P : Finset (Finset V)}
    (hP : IsRCliquePacking 3 G P) :
    P.card ≤ rRemovalNumber 3 G ∧ rRemovalNumber 3 G ≤ numRCliques 3 G :=
  rPacking_le_removal_le_numRCliques (by norm_num) G hP

end Szemeredi.CliqueRemoval.Bounds
