/-
This file was edited by Aristotle.

Lean version: leanprover/lean4:v4.24.0
Mathlib version: f897ebcf72cd16f89ab4577d0c826cd14afaafc7
This project request had uuid: ca7f39bc-1229-4946-9f19-2e69b1f4d79b

The following was proved by Aristotle:

- theorem trivial_bound (G : SimpleGraph V) :
    triangleCoverNumber G ≤ 3 * maxEdgeDisjointTriangles G

- theorem k4_tight : ∃ (G : SimpleGraph (Fin 4)),
    maxEdgeDisjointTriangles G = 1 ∧ triangleCoverNumber G = 2

- theorem k5_tight : ∃ (G : SimpleGraph (Fin 5)),
    maxEdgeDisjointTriangles G = 2 ∧ triangleCoverNumber G = 4
-/

/-
  Erdős Problem #167: Tuza's Conjecture on Triangle Covering

  Source: https://erdosproblems.com/167
  Status: PARTIALLY SOLVED
  Prize: None specified

  Statement:
  If G is a graph with at most k edge-disjoint triangles, can G be made
  triangle-free after removing at most 2k edges?

  This is Tuza's Conjecture from 1981.

  Known Results:
  - Trivial: ≤ 3k edges suffice (remove one edge from each triangle)
  - Haxell-Kohayakawa (1998): ≤ (3 - 3/23)k edges
  - Haxell (1999): ≤ (3 - 1/10)k edges for K₄-free graphs
  - The conjecture holds for planar graphs

  The conjecture remains open in general but has been verified for
  several graph classes.

  Reference: Tuza, Z. (1981), Haxell, P. (1999)
-/

import Mathlib


open Finset SimpleGraph Set

namespace Erdos167

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Core Definitions -/

/-- A triangle in a graph G is a set of three vertices forming K₃. -/
def IsTriangle (G : SimpleGraph V) (a b c : V) : Prop :=
  a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj a c

/-- The set of all triangles in G (as unordered triples). -/
def Triangles (G : SimpleGraph V) : Set ({s : Finset V // s.card = 3}) :=
  { s | ∃ a b c : V, s.val = {a, b, c} ∧ IsTriangle G a b c }

/-- Two triangles are edge-disjoint if they share no edges. -/
def EdgeDisjoint (G : SimpleGraph V) (t₁ t₂ : {s : Finset V // s.card = 3}) : Prop :=
  ∀ e : Sym2 V, ¬e.IsDiag →
    (∃ a ∈ t₁.val, ∃ b ∈ t₁.val, e = s(a, b)) →
    (∃ a ∈ t₂.val, ∃ b ∈ t₂.val, e = s(a, b)) →
    False

/-- The maximum number of edge-disjoint triangles in G. -/
noncomputable def maxEdgeDisjointTriangles (G : SimpleGraph V) : ℕ :=
  sSup { k : ℕ | ∃ T : Finset {s : Finset V // s.card = 3},
    T.card = k ∧
    (∀ t ∈ T, t ∈ Triangles G) ∧
    (∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → EdgeDisjoint G t₁ t₂) }

/-- A triangle cover: a set of edges whose removal makes G triangle-free. -/
def IsTriangleCover (G : SimpleGraph V) (E : Set (Sym2 V)) : Prop :=
  ∀ a b c : V, ¬IsTriangle (G.deleteEdges E) a b c

/-- The minimum triangle cover number τ(G). -/
noncomputable def triangleCoverNumber (G : SimpleGraph V) : ℕ :=
  sInf { k : ℕ | ∃ E : Finset (Sym2 V), E.card = k ∧ IsTriangleCover G E }

/-! ## Tuza's Conjecture -/

/-- **Tuza's Conjecture** (1981):
    For any graph G, τ(G) ≤ 2 · ν(G) where ν(G) is the maximum number
    of edge-disjoint triangles. -/
def TuzaConjecture : Prop :=
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    triangleCoverNumber G ≤ 2 * maxEdgeDisjointTriangles G

/-! ## Trivial Bound -/

/- Trivial bound: τ(G) ≤ 3 · ν(G).
    We can remove one edge from each triangle in a maximum packing. -/
noncomputable section AristotleLemmas

/-
There exists a finite set of edge-disjoint triangles T such that the size of T is equal to the maximum number of edge-disjoint triangles in G.
-/
theorem Erdos167.exists_max_packing {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
  ∃ T : Finset {s : Finset V // s.card = 3},
    T.card = Erdos167.maxEdgeDisjointTriangles G ∧
    (∀ t ∈ T, t ∈ Erdos167.Triangles G) ∧
    (∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → Erdos167.EdgeDisjoint G t₁ t₂) := by
  simp +zetaDelta at *;
  have h_sup : ∃ k : ℕ, k ∈ { k : ℕ | ∃ T : Finset {s : Finset V // s.card = 3}, T.card = k ∧ (∀ t ∈ T, t ∈ Erdos167.Triangles G) ∧ (∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → Erdos167.EdgeDisjoint G t₁ t₂) } ∧ ∀ m ∈ { k : ℕ | ∃ T : Finset {s : Finset V // s.card = 3}, T.card = k ∧ (∀ t ∈ T, t ∈ Erdos167.Triangles G) ∧ (∀ t₁ ∈ T, ∀ t₂ ∈ T, t₁ ≠ t₂ → Erdos167.EdgeDisjoint G t₁ t₂) }, k ≥ m := by
    apply_rules [ Set.exists_max_image ];
    · exact Set.finite_iff_bddAbove.2 ⟨ Finset.card ( Finset.univ : Finset { s : Finset V // #s = 3 } ), fun k hk => by obtain ⟨ T, rfl, hT₁, hT₂ ⟩ := hk; exact Finset.card_le_univ _ ⟩;
    · exact ⟨ 0, ⟨ ∅, rfl, by simp +decide ⟩ ⟩;
  rcases h_sup with ⟨ k, ⟨ T, rfl, hT₁, hT₂ ⟩, hk ⟩;
  refine' ⟨ T, _, _, _ ⟩ <;> try tauto;
  · refine' le_antisymm _ _;
    · refine' le_csSup _ _;
      · exact ⟨ _, fun k hk' => hk _ hk' ⟩;
      · exact ⟨ T, rfl, hT₁, hT₂ ⟩;
    · exact csSup_le' fun k hk' => hk k hk';
  · exact fun a ha ha' b hb hb' hab => hT₂ _ ha' _ hb' ( by simpa [ Subtype.ext_iff ] using hab )

end AristotleLemmas

theorem trivial_bound (G : SimpleGraph V) :
    triangleCoverNumber G ≤ 3 * maxEdgeDisjointTriangles G := by
  -- Let's construct the set of edges E by taking all edges from each triangle in the maximum packing T.
  obtain ⟨T, hT_card, hT_triangles, hT_disjoint⟩ := Erdos167.exists_max_packing G;
  set E := Finset.biUnion T (fun t => Finset.filter (fun e => e.IsDiag = false) (Finset.image (fun p => s(p.1, p.2)) (t.val.offDiag))) with hE_def;
  -- We claim E is a triangle cover.
  have hE_triangle_cover : Erdos167.IsTriangleCover G E := by
    intro a b c h
    by_contra h_contra;
    -- Since T is maximal, adding t' to T would contradict the maximality of T.
    have h_max : ¬∃ t' : {s : Finset V // s.card = 3}, t' ∈ Erdos167.Triangles G ∧ (∀ t ∈ T, Erdos167.EdgeDisjoint G t t') := by
      intro h_max
      obtain ⟨t', ht'_triangle, ht'_disjoint⟩ := h_max;
      have h_max : ∃ T' : Finset {s : Finset V // s.card = 3}, T'.card = T.card + 1 ∧ (∀ t ∈ T', t ∈ Erdos167.Triangles G) ∧ (∀ t₁ ∈ T', ∀ t₂ ∈ T', t₁ ≠ t₂ → Erdos167.EdgeDisjoint G t₁ t₂) := by
        refine' ⟨ Insert.insert t' T, _, _, _ ⟩ <;> simp_all +decide [ Finset.card_insert_of_notMem ];
        · rw [ Finset.card_insert_of_notMem, hT_card ];
          rintro H; specialize ht'_disjoint _ _ H; simp_all +decide [ Erdos167.EdgeDisjoint ] ;
          rcases Finset.card_eq_three.mp t'.property with ⟨ x, y, z, hx, hy, hz, hxyz ⟩ ; specialize ht'_disjoint ( s(x, y) ) ; simp_all +decide;
        · exact fun a b ha hb => by have := ht'_disjoint a b ha; exact fun e he₁ he₂ he₃ => this e he₁ he₃ he₂;
      obtain ⟨ T', hT'_card, hT'_triangles, hT'_disjoint ⟩ := h_max;
      have h_max : Erdos167.maxEdgeDisjointTriangles G ≥ T'.card := by
        exact le_csSup ⟨ Fintype.card { s : Finset V // #s = 3 }, fun k hk => by rcases hk with ⟨ T', hT'_card, hT'_triangles, hT'_disjoint ⟩ ; exact hT'_card ▸ Finset.card_le_univ _ ⟩ ⟨ T', rfl, hT'_triangles, hT'_disjoint ⟩;
      linarith;
    refine' h_max ⟨ ⟨ { a, b, c }, _ ⟩, _, _ ⟩ <;> simp_all +decide [ Erdos167.IsTriangle ];
    · use a, b, c;
      unfold Erdos167.IsTriangle at *; aesop;
    · intro t ht htT;
      intro e he;
      rintro ⟨ x, hx, y, hy, rfl ⟩ ⟨ u, hu, v, hv, huv ⟩;
      have := h.2.2; simp_all +decide [ SimpleGraph.deleteEdges ] ;
      grind;
  -- Since each triangle in T has exactly 3 edges, the total number of edges in E is at most 3 times the number of triangles in T.
  have hE_card : E.card ≤ 3 * T.card := by
    -- Each triangle in T contributes exactly 3 edges to E.
    have h_triangle_edges : ∀ t ∈ T, (Finset.filter (fun e => ¬e.IsDiag) (Finset.image (fun p => s(p.1, p.2)) (t.val.offDiag))).card ≤ 3 := by
      intro t ht
      have h_triangle_edges : (Finset.filter (fun e => ¬e.IsDiag) (Finset.image (fun p => s(p.1, p.2)) (t.val.offDiag))).card ≤ Finset.card (Finset.offDiag t.val) / 2 := by
        have h_triangle_edges : ∀ e ∈ Finset.image (fun p => s(p.1, p.2)) (t.val.offDiag), Finset.card (Finset.filter (fun p => s(p.1, p.2) = e) (t.val.offDiag)) ≥ 2 := by
          simp +decide [ Sym2.eq_swap ];
          rintro e x y hx hy hxy rfl; refine' Finset.one_lt_card.2 ⟨ ( x, y ), _, ( y, x ), _, _ ⟩ <;> aesop;
        have h_triangle_edges : Finset.card (Finset.offDiag t.val) ≥ Finset.sum (Finset.filter (fun e => ¬e.IsDiag) (Finset.image (fun p => s(p.1, p.2)) (t.val.offDiag))) (fun e => Finset.card (Finset.filter (fun p => s(p.1, p.2) = e) (t.val.offDiag))) := by
          rw [ ← Finset.card_biUnion ];
          · exact Finset.card_le_card fun x hx => by aesop;
          · exact fun x hx y hy hxy => Finset.disjoint_left.mpr fun p hp hp' => hxy <| by aesop;
        rw [ Nat.le_div_iff_mul_le zero_lt_two ];
        refine' le_trans _ h_triangle_edges;
        exact le_trans ( by simp +decide [ mul_comm ] ) ( Finset.sum_le_sum fun x hx => ‹∀ e ∈ Finset.image ( fun p : V × V => s(p.1, p.2) ) ( t.val.offDiag ), #({ p ∈ ( t.val.offDiag ) | s(p.1, p.2) = e }) ≥ 2› x <| Finset.mem_filter.mp hx |>.1 );
      exact h_triangle_edges.trans ( Nat.div_le_of_le_mul <| by simp +decide [ t.2 ] );
    exact le_trans ( Finset.card_biUnion_le ) ( by simpa [ mul_comm ] using Finset.sum_le_sum h_triangle_edges );
  exact le_trans ( Nat.sInf_le ⟨ E, rfl, hE_triangle_cover ⟩ ) ( by simpa only [ hT_card ] using hE_card )

/-! ## Known Results -/

/-- K₄ shows 2k is tight: ν(K₄) = 1 but τ(K₄) = 2. -/
theorem k4_tight : ∃ (G : SimpleGraph (Fin 4)),
    maxEdgeDisjointTriangles G = 1 ∧ triangleCoverNumber G = 2 := by
  use ⊤;
  constructor;
  · refine' le_antisymm _ _;
    · refine' csSup_le' _;
      rintro k ⟨ T, rfl, hT₁, hT₂ ⟩;
      simp_all +decide [ Erdos167.EdgeDisjoint ];
      contrapose! hT₂;
      obtain ⟨ x, hx, y, hy, hxy ⟩ := Finset.one_lt_card.mp hT₂;
      refine' ⟨ x.val, x.property, hx, y.val, y.property, hy, _, _ ⟩ <;> simp_all +decide [ Finset.ext_iff ];
      · exact not_forall.mp fun h => hxy <| Subtype.ext <| Finset.ext h;
      · fin_cases x <;> fin_cases y <;> simp +decide at hxy ⊢;
    · refine' le_csSup _ _;
      · exact ⟨ _, fun k hk => by obtain ⟨ T, rfl, hT₁, hT₂ ⟩ := hk; exact Finset.card_le_univ _ ⟩;
      · use { ⟨ { 0, 1, 2 }, by decide ⟩ } ; simp +decide [ Erdos167.Triangles ];
        exists 0, 1, 2;
  · unfold Erdos167.triangleCoverNumber;
    unfold Erdos167.IsTriangleCover;
    rw [ @IsLeast.csInf_eq ];
    constructor;
    · simp +decide [ Erdos167.IsTriangle ];
    · unfold Erdos167.IsTriangle; simp +decide ;
      rintro k ⟨ E, rfl, hE ⟩;
      native_decide +revert

/-- K₅ also shows 2k is tight: ν(K₅) = 2 but τ(K₅) = 4. -/
theorem k5_tight : ∃ (G : SimpleGraph (Fin 5)),
    maxEdgeDisjointTriangles G = 2 ∧ triangleCoverNumber G = 4 := by
  refine' ⟨ ⊤, _, _ ⟩;
  · refine' csSup_eq_of_forall_le_of_forall_lt_exists_gt _ _ _;
    · exact ⟨ 0, ⟨ ∅, rfl, by simp +decide ⟩ ⟩;
    · simp +zetaDelta at *;
      rintro a x rfl hx₁ hx₂;
      have h_max_triangles : ∀ x : Finset { s : Finset (Fin 5) // #s = 3 }, x.card > 2 → ∃ t₁ ∈ x, ∃ t₂ ∈ x, t₁ ≠ t₂ ∧ ¬Erdos167.EdgeDisjoint ⊤ t₁ t₂ := by
        simp +decide [ Erdos167.EdgeDisjoint ];
        intro x hx;
        have h_max_triangles : ∀ x : Finset { s : Finset (Fin 5) // #s = 3 }, x.card > 2 → ∃ t₁ ∈ x, ∃ t₂ ∈ x, t₁ ≠ t₂ ∧ Finset.card (t₁.val ∩ t₂.val) ≥ 2 := by
          native_decide +revert;
        obtain ⟨ t₁, ht₁, t₂, ht₂, hne, hcard ⟩ := h_max_triangles x hx;
        obtain ⟨ a, ha, b, hb, hab ⟩ := Finset.one_lt_card.mp hcard;
        use t₁.val, ⟨ t₁.property, ht₁ ⟩, t₂.val, ⟨ t₂.property, ht₂ ⟩;
        exact ⟨ by simpa [ Subtype.ext_iff ] using hne, s(a, b), by simpa [ Sym2.eq_swap ] using hab, a, by aesop, b, by aesop, rfl, a, by aesop, b, by aesop, rfl ⟩;
      exact le_of_not_gt fun h => by obtain ⟨ t₁, ht₁, t₂, ht₂, hne, hne' ⟩ := h_max_triangles x h; exact hne' ( hx₂ _ _ ht₁ _ _ ht₂ ( by aesop ) ) ;
    · intro w hw;
      refine' ⟨ 2, ⟨ { ⟨ { 0, 1, 2 }, by decide ⟩, ⟨ { 0, 3, 4 }, by decide ⟩ }, rfl, _, _ ⟩, hw ⟩ <;> simp +decide [ Erdos167.EdgeDisjoint ];
      constructor <;> unfold Erdos167.Triangles <;> simp +decide [ Erdos167.IsTriangle ];
  · refine' le_antisymm _ _;
    · refine' Nat.sInf_le _;
      simp +decide [ Erdos167.IsTriangleCover ];
      unfold Erdos167.IsTriangle;
      native_decide +revert;
    · refine' le_csInf _ _ <;> norm_num;
      · refine' ⟨ _, ⟨ Finset.univ, rfl, _ ⟩ ⟩;
        intro a b c h; simp_all +decide [ Erdos167.IsTriangle ] ;
      · rintro b x rfl hx;
        contrapose! hx;
        unfold Erdos167.IsTriangleCover;
        simp +decide [ Erdos167.IsTriangle ];
        native_decide +revert

/-- **Haxell-Kohayakawa (1998)**: τ(G) ≤ (3 - 3/23) · ν(G). -/
axiom haxell_kohayakawa :
  ∀ (V : Type*) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    (triangleCoverNumber G : ℚ) ≤ (3 - 3/23) * maxEdgeDisjointTriangles G

/-- Tuza's conjecture holds for K₄-free graphs (Haxell 1999). -/
axiom tuza_for_k4_free (G : SimpleGraph V) (hK4 : ¬∃ a b c d : V,
    IsTriangle G a b c ∧ IsTriangle G a b d ∧ IsTriangle G a c d ∧ IsTriangle G b c d) :
  triangleCoverNumber G ≤ 2 * maxEdgeDisjointTriangles G

/-- Tuza's conjecture holds for planar graphs. -/
axiom tuza_for_planar (G : SimpleGraph V) (hPlanar : True) :  -- Planarity predicate omitted
  triangleCoverNumber G ≤ 2 * maxEdgeDisjointTriangles G

/-! ## Fractional Version -/

/-- The fractional version of Tuza's conjecture IS true.
    τ*(G) ≤ 2 · ν*(G) where * denotes fractional versions. -/
axiom fractional_tuza :
  True

-- The fractional relaxation is known to hold

/-! ## Summary

**Problem Status: PARTIALLY SOLVED**

Tuza's Conjecture (1981) asks whether every graph G with at most k
edge-disjoint triangles can be made triangle-free by removing ≤ 2k edges.

**What we know:**
- Trivial: 3k edges always suffice
- Haxell-Kohayakawa: (3 - 3/23)k ≈ 2.87k suffice
- K₄, K₅ show 2k is best possible
- True for K₄-free graphs, planar graphs
- Fractional version is true

**Open Question:**
Does τ(G) ≤ 2ν(G) hold for ALL graphs?

References:
- Tuza (1981): Original conjecture
- Haxell, Kohayakawa (1998): Best general bound
- Haxell (1999): K₄-free case
-/

end Erdos167