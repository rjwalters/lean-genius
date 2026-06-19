/-
# Erdős Problem #1104 (oq-01) — Mycielskian witnesses for triangle-free chromatic number

Erdős problem #1104 asks for the growth rate of `f(n)`, the maximum chromatic number
of a triangle-free graph on `n` vertices. The engine behind the lower-bound side is the
existence of triangle-free graphs of *arbitrarily large* chromatic number — a fact with
no entirely elementary witness family. The classical constructive source is **Mycielski's
construction** (1955): from any graph `G` it builds a graph `M(G)` that

  * stays triangle-free whenever `G` is triangle-free, and
  * has chromatic number exactly one larger: `χ(M(G)) = χ(G) + 1`.

Iterating `M` from `K₂` (chromatic number `2`) produces `C₅`, then the Grötzsch graph,
and in general triangle-free graphs of chromatic number `k` for every `k ≥ 2`.

Mathlib does **not** contain the Mycielskian. This file builds it from scratch and proves
the **full** Mycielski theorem, fully machine-checked and `sorry`-free / `axiom`-free:

  * `mycielskian_cliqueFree_three` — triangle-free is preserved by `M`;
  * `mycielskian_colorable_succ`   — `G.Colorable n → (M G).Colorable (n+1)`, via an
                                      explicit `(n+1)`-colouring (chromatic *upper* bound);
  * `mycielskian_colorable_of_succ`— `(M G).Colorable (n+1) → G.Colorable n`, Mycielski's
                                      recolouring argument (chromatic *lower* bound).

Together the last two give `χ(M(G)) = χ(G) + 1`.  The file then packages the triangle-free
witness family

  * `mycielskianIter`                  — the `k`-fold Mycielskian of a base graph;
  * `mycielskianIter_cliqueFree_three` — every iterate of a triangle-free base is
                                          triangle-free;
  * `mycielskianIter_colorable`        — the `k`-fold iterate of an `n`-colourable base
                                          is `(n + k)`-colourable.

Iterating `M` from `K₂` therefore yields triangle-free graphs of every chromatic number
`≥ 2`, the constructive engine behind the lower-bound side of Erdős #1104.

Reference: https://erdosproblems.com/1104
-/
import Mathlib

namespace Erdos1104OQ01

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-! ## The Mycielskian construction

Vertices of `M(G)` are `Option (V ⊕ V)`:
* `some (Sum.inl u)` — the *original* copy of `u`;
* `some (Sum.inr u)` — the *shadow* copy `u'`;
* `none`             — the apex vertex `z`.

Edges:
* originals are joined exactly as in `G`;
* a shadow `u'` is joined to the originals that are `G`-neighbours of `u`
  (so `u' ~ v` iff `G.Adj u v`);
* shadows form an independent set;
* the apex `z` is joined to every shadow and to nothing else.
-/

/-- Vertex type of the Mycielskian. -/
abbrev MycVertex (V : Type*) := Option (V ⊕ V)

/-- Raw (pre-symmetrisation) adjacency relation feeding `SimpleGraph.fromRel`. -/
def mycRel (G : SimpleGraph V) : MycVertex V → MycVertex V → Prop
  | some (Sum.inl u), some (Sum.inl v) => G.Adj u v
  | some (Sum.inl u), some (Sum.inr v) => G.Adj u v
  | some (Sum.inr u), some (Sum.inl v) => G.Adj u v
  | none,             some (Sum.inr _) => True
  | _,                _                => False

/-- The Mycielskian `M(G)` of a graph `G`. -/
def mycielskian (G : SimpleGraph V) : SimpleGraph (MycVertex V) :=
  SimpleGraph.fromRel (mycRel G)

/-! ### Adjacency characterisations -/

@[simp] lemma adj_orig_orig {u v : V} :
    (mycielskian G).Adj (some (Sum.inl u)) (some (Sum.inl v)) ↔ G.Adj u v := by
  rw [mycielskian, fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · simpa [mycRel] using h
    · exact (G.adj_comm v u).1 (by simpa [mycRel] using h)
  · intro h
    exact ⟨by simp [G.ne_of_adj h], Or.inl (by simpa [mycRel] using h)⟩

@[simp] lemma adj_orig_shadow {u v : V} :
    (mycielskian G).Adj (some (Sum.inl u)) (some (Sum.inr v)) ↔ G.Adj u v := by
  rw [mycielskian, fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · simpa [mycRel] using h
    · exact (G.adj_comm v u).1 (by simpa [mycRel] using h)
  · intro h
    exact ⟨by simp, Or.inl (by simpa [mycRel] using h)⟩

@[simp] lemma adj_shadow_orig {u v : V} :
    (mycielskian G).Adj (some (Sum.inr u)) (some (Sum.inl v)) ↔ G.Adj u v := by
  rw [mycielskian, fromRel_adj]
  constructor
  · rintro ⟨_, h | h⟩
    · simpa [mycRel] using h
    · exact (G.adj_comm v u).1 (by simpa [mycRel] using h)
  · intro h
    exact ⟨by simp, Or.inl (by simpa [mycRel] using h)⟩

@[simp] lemma not_adj_shadow_shadow {u v : V} :
    ¬ (mycielskian G).Adj (some (Sum.inr u)) (some (Sum.inr v)) := by
  rw [mycielskian, fromRel_adj]
  rintro ⟨_, h | h⟩ <;> simpa [mycRel] using h

@[simp] lemma adj_apex_shadow {v : V} :
    (mycielskian G).Adj none (some (Sum.inr v)) := by
  rw [mycielskian, fromRel_adj]
  exact ⟨by simp, Or.inl (by simp [mycRel])⟩

@[simp] lemma adj_shadow_apex {v : V} :
    (mycielskian G).Adj (some (Sum.inr v)) none := by
  rw [adj_comm]; exact adj_apex_shadow G

@[simp] lemma not_adj_apex_orig {v : V} :
    ¬ (mycielskian G).Adj none (some (Sum.inl v)) := by
  rw [mycielskian, fromRel_adj]
  rintro ⟨_, h | h⟩ <;> simpa [mycRel] using h

@[simp] lemma not_adj_orig_apex {v : V} :
    ¬ (mycielskian G).Adj (some (Sum.inl v)) none := by
  rw [adj_comm]; exact not_adj_apex_orig G

@[simp] lemma not_adj_apex_apex :
    ¬ (mycielskian G).Adj none none := by
  rw [mycielskian, fromRel_adj]; simp

/-! ## Triangle-free preservation -/

/-- **Mycielski preserves triangle-freeness.**  If `G` has no triangle then neither does
`M(G)`.  The apex only meets the independent shadow class, so it lies in no triangle; a
triangle therefore uses at most one shadow (shadows are independent) and projects to a
triangle of `G`. -/
theorem mycielskian_cliqueFree_three (h : G.CliqueFree 3) :
    (mycielskian G).CliqueFree 3 := by
  classical
  -- a `G`-triangle is impossible
  have gtri : ∀ x y z : V, G.Adj x y → G.Adj x z → G.Adj y z → False :=
    fun x y z hxy hxz hyz => h {x, y, z} (is3Clique_triple_iff.mpr ⟨hxy, hxz, hyz⟩)
  intro s hs
  obtain ⟨a, b, c, _, _, _, rfl⟩ := Finset.card_eq_three.mp hs.card_eq
  obtain ⟨Aab, Aac, Abc⟩ := is3Clique_triple_iff.mp hs
  rcases a with _ | (a | a) <;> rcases b with _ | (b | b) <;> rcases c with _ | (c | c) <;>
    simp_all only [adj_orig_orig, adj_orig_shadow, adj_shadow_orig, not_adj_shadow_shadow,
      adj_apex_shadow, adj_shadow_apex, not_adj_apex_orig, not_adj_orig_apex, not_adj_apex_apex] <;>
    exact gtri _ _ _ Aab Aac Abc

/-! ## Chromatic upper bound: an explicit `(n+1)`-colouring -/

/-- The Mycielskian colouring built from a colouring `C` of `G`: an original or its shadow
keep `C`'s colour (lifted along `Fin.castSucc`), and the apex takes the fresh top colour. -/
def mycColor {n : ℕ} (C : G.Coloring (Fin n)) : MycVertex V → Fin (n + 1)
  | some (Sum.inl u) => (C u).castSucc
  | some (Sum.inr u) => (C u).castSucc
  | none             => Fin.last n

/-- **Mycielski raises colourability by at most one.**  An explicit `(n+1)`-colouring of
`M(G)` from any `n`-colouring of `G`. -/
theorem mycielskian_colorable_succ {n : ℕ} (hG : G.Colorable n) :
    (mycielskian G).Colorable (n + 1) := by
  obtain ⟨C⟩ := hG
  refine ⟨Coloring.mk (mycColor G C) ?_⟩
  intro x y hxy
  rcases x with _ | (x | x) <;> rcases y with _ | (y | y) <;>
  first
    | (exfalso; simpa using hxy)
    | (simp only [mycColor, ne_eq, Fin.castSucc_inj]; exact C.valid (by simpa using hxy))
    | (simp only [mycColor]; exact (Fin.castSucc_lt_last _).ne)
    | (simp only [mycColor]; exact (Fin.castSucc_lt_last _).ne')

/-! ## Chromatic lower bound: Mycielski's recolouring argument

This is the deep half of Mycielski's theorem.  Given a proper `(n+1)`-colouring `C` of
`M(G)`, write `a := C z` for the apex colour.  Recolour `G` by

  `D u := if C u = a then C u' else C u`

(use the shadow's colour when an original wears the apex colour).  Three facts make `D` a
proper `n`-colouring of `G`:

* `D` never uses `a`: if `C u ≠ a` we keep `C u ≠ a`; otherwise `D u = C u'`, and the
  shadow `u'` is adjacent to the apex, so `C u' ≠ C z = a`;
* `D` is proper: for `G.Adj u v` the originals are adjacent in `M(G)`, so `C u ≠ C v`,
  hence they cannot *both* equal `a`; in the three remaining cases the relevant vertices
  (`u'`–`v`, `u`–`v'`, `u`–`v`) are adjacent in `M(G)`, so their colours differ;
* `D` lands in the `n`-element set `Fin (n+1) \ {a}`, giving an `n`-colouring.
-/

/-- **Mycielski lowers colourability by exactly one.**  If the Mycielskian `M(G)` is
`(n+1)`-colourable then `G` is `n`-colourable.  Combined with `mycielskian_colorable_succ`
(`G.Colorable n → (M G).Colorable (n+1)`) this pins the chromatic number exactly:
`χ(M(G)) = χ(G) + 1`. -/
theorem mycielskian_colorable_of_succ {n : ℕ}
    (h : (mycielskian G).Colorable (n + 1)) : G.Colorable n := by
  classical
  obtain ⟨C⟩ := h
  set a : Fin (n + 1) := C none with ha
  -- shadow colours all differ from the apex colour
  have hshadow : ∀ u : V, C (some (Sum.inr u)) ≠ a := fun u =>
    C.valid (adj_shadow_apex G)
  -- the recoloured map on originals
  let D : V → Fin (n + 1) := fun u =>
    if C (some (Sum.inl u)) = a then C (some (Sum.inr u)) else C (some (Sum.inl u))
  -- `D` avoids the apex colour
  have hDne : ∀ u, D u ≠ a := by
    intro u
    by_cases hu : C (some (Sum.inl u)) = a
    · simp only [D, if_pos hu]; exact hshadow u
    · simp only [D, if_neg hu]; exact hu
  -- `D` is a proper colouring of `G`
  have hDvalid : ∀ {u v : V}, G.Adj u v → D u ≠ D v := by
    intro u v huv
    have hor : C (some (Sum.inl u)) ≠ C (some (Sum.inl v)) :=
      C.valid ((adj_orig_orig G).mpr huv)
    by_cases hu : C (some (Sum.inl u)) = a <;> by_cases hv : C (some (Sum.inl v)) = a
    · exact absurd (hu.trans hv.symm) hor
    · simp only [D, if_pos hu, if_neg hv]
      exact C.valid ((adj_shadow_orig G).mpr huv)
    · simp only [D, if_neg hu, if_pos hv]
      exact C.valid ((adj_orig_shadow G).mpr huv)
    · simp only [D, if_neg hu, if_neg hv]; exact hor
  -- `D` lands in the `n`-element complement of `{a}`; transport to `Fin n`
  have hcard : Fintype.card {x : Fin (n + 1) // x ≠ a} = n := by
    simp only [ne_eq]
    rw [Fintype.card_subtype_compl]
    simp
  let e : {x : Fin (n + 1) // x ≠ a} ≃ Fin n := Fintype.equivFinOfCardEq hcard
  exact ⟨Coloring.mk (fun u => e ⟨D u, hDne u⟩) (by
    intro u v huv
    simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq]
    exact hDvalid huv)⟩

/-! ## The iterated witness family

Iterating `M` changes the vertex type, so we index the construction by a recursively
defined vertex type. -/

/-- The vertex type of the `k`-fold Mycielskian of `V`. -/
def mycVertexIter (V : Type u) : ℕ → Type u
  | 0     => V
  | k + 1 => MycVertex (mycVertexIter V k)

/-- The `k`-fold Mycielskian of a graph `G`. -/
def mycielskianIter {V : Type u} (G : SimpleGraph V) :
    (k : ℕ) → SimpleGraph (mycVertexIter V k)
  | 0     => G
  | k + 1 => mycielskian (mycielskianIter G k)

/-- Every iterate of a triangle-free base graph is triangle-free. -/
theorem mycielskianIter_cliqueFree_three {V : Type u} {G : SimpleGraph V}
    (h : G.CliqueFree 3) : ∀ k, (mycielskianIter G k).CliqueFree 3
  | 0     => h
  | k + 1 => mycielskian_cliqueFree_three _ (mycielskianIter_cliqueFree_three h k)

/-- The `k`-fold iterate of an `n`-colourable base graph is `(n + k)`-colourable. -/
theorem mycielskianIter_colorable {V : Type u} {G : SimpleGraph V} {n : ℕ}
    (hG : G.Colorable n) : ∀ k, (mycielskianIter G k).Colorable (n + k)
  | 0     => hG
  | k + 1 => by
      have := mycielskian_colorable_succ _ (mycielskianIter_colorable hG k)
      rw [Nat.add_succ]
      exact this

/-- **Witness family (constructive half).**  From any triangle-free, `n`-colourable base
graph, the Mycielskian tower yields, for every `k`, a triangle-free graph that is
`(n + k)`-colourable.  Together with the companion chromatic *lower* bound
(`χ(M(G)) = χ(G)+1`) this exhibits triangle-free graphs of every chromatic number `≥ n`. -/
theorem mycielskian_witness_family {V : Type u} {G : SimpleGraph V} {n : ℕ}
    (htf : G.CliqueFree 3) (hcol : G.Colorable n) (k : ℕ) :
    (mycielskianIter G k).CliqueFree 3 ∧ (mycielskianIter G k).Colorable (n + k) :=
  ⟨mycielskianIter_cliqueFree_three htf k, mycielskianIter_colorable hcol k⟩

/-! ## Exact colourability of the tower and a concrete witness over `K₂`

`mycielskianIter_colorable` is only the *upper* bound `χ(mycielskianIter G k) ≤ χ(G) + k`.
The matching lower bound is the iterated form of `mycielskian_colorable_of_succ`: an
`(m+k)`-colouring of the `k`-fold Mycielskian descends to an `m`-colouring of the base.
The two together pin the colourability threshold exactly, and instantiating at `K₂`
(triangle-free, chromatic number `2`) yields explicit triangle-free graphs of chromatic
number `k + 2` for every `k` — the constructive witnesses behind the lower-bound side of
Erdős #1104. -/

/-- **Lower bound for the tower.**  An `(m+k)`-colouring of the `k`-fold Mycielskian
descends to an `m`-colouring of the base graph — the iterated form of
`mycielskian_colorable_of_succ`. -/
theorem mycielskianIter_colorable_of_add {V : Type u} {G : SimpleGraph V} {m : ℕ} :
    ∀ k, (mycielskianIter G k).Colorable (m + k) → G.Colorable m
  | 0     => fun h => by simpa using h
  | k + 1 => fun h => by
      have hk : m + (k + 1) = (m + k) + 1 := by omega
      rw [hk] at h
      exact mycielskianIter_colorable_of_add k
        (mycielskian_colorable_of_succ (mycielskianIter G k) h)

/-- **Exact colourability of the tower.**  The `k`-fold Mycielskian of `G` is
`(m+k)`-colourable iff `G` itself is `m`-colourable.  Equivalently
`χ(mycielskianIter G k) = χ(G) + k`. -/
theorem mycielskianIter_colorable_iff {V : Type u} {G : SimpleGraph V} {m k : ℕ} :
    (mycielskianIter G k).Colorable (m + k) ↔ G.Colorable m :=
  ⟨mycielskianIter_colorable_of_add k, fun h => mycielskianIter_colorable h k⟩

/-! ### A concrete witness: the Mycielskian tower over `K₂` -/

/-- `K₂` (the complete graph on two vertices) is triangle-free: with only two vertices it
cannot contain a `3`-clique. -/
theorem top_fin_two_cliqueFree_three : (⊤ : SimpleGraph (Fin 2)).CliqueFree 3 := by
  intro s hs
  have h3 : s.card = 3 := hs.card_eq
  have hle : s.card ≤ Fintype.card (Fin 2) := Finset.card_le_univ s
  rw [Fintype.card_fin] at hle
  omega

/-- `K₂` is `2`-colourable: the identity colouring sends its two adjacent vertices to
distinct colours. -/
theorem top_fin_two_colorable_two : (⊤ : SimpleGraph (Fin 2)).Colorable 2 :=
  ⟨Coloring.mk id (fun {_ _} h => by simpa using h)⟩

/-- `K₂` is not `1`-colourable: its single edge forces two distinct colours, impossible in
`Fin 1`. -/
theorem top_fin_two_not_colorable_one : ¬ (⊤ : SimpleGraph (Fin 2)).Colorable 1 := by
  rintro ⟨C⟩
  exact C.valid (show (⊤ : SimpleGraph (Fin 2)).Adj 0 1 by decide) (Subsingleton.elim _ _)

/-- **Witness tower over `K₂`.**  For every `k`, the `k`-fold Mycielskian of `K₂` is
triangle-free, `(2+k)`-colourable, and *not* `(1+k)`-colourable — hence a triangle-free
graph of chromatic number exactly `k + 2`.  As `k → ∞` these realise triangle-free graphs
of arbitrarily large chromatic number, the constructive lower-bound witnesses for
Erdős #1104. -/
theorem exists_triangleFree_colorable_not_colorable (k : ℕ) :
    ∃ (W : Type) (H : SimpleGraph W),
      H.CliqueFree 3 ∧ H.Colorable (2 + k) ∧ ¬ H.Colorable (1 + k) :=
  ⟨mycVertexIter (Fin 2) k, mycielskianIter (⊤ : SimpleGraph (Fin 2)) k,
    mycielskianIter_cliqueFree_three top_fin_two_cliqueFree_three k,
    mycielskianIter_colorable top_fin_two_colorable_two k,
    fun h => top_fin_two_not_colorable_one (mycielskianIter_colorable_of_add k h)⟩

end Erdos1104OQ01
