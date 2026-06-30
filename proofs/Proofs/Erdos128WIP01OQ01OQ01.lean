import Mathlib

/-
# Erdős #128 — clique-freeness pulls back along graph homomorphisms
# (erdos-128-wip-01-oq-01-oq-01)

## The Problem

**Erdős Problem #128** ($250, OPEN). If every induced subgraph of an `n`-vertex
graph `G` on `≥ ⌊n/2⌋` vertices has more than `n²/50` edges, must `G` contain a
triangle? The constant `1/50` is conjectured optimal, witnessed by **blow-ups of
`C₅`**, which are triangle-free with induced density `> 1/50` at every scale.

The parent chain established that triangle-freeness is **hereditary** under induced
subgraphs (`Erdos128WIP01.lean`) and, more sharply, that triangle-freeness pulls
back along **arbitrary graph homomorphisms** (`triangleFree_of_hom` in
`Erdos128WIP01OQ01.lean`), so blow-ups of `C₅` are triangle-free at every scale.

This file lifts that homomorphism-pullback principle from triangles to **`K_r`-cliques
of every order `r`**, and shows the triangle theory is the case `r = 3`.

## Result

Working in a self-contained re-declaration of the parent's `Graph` objects:

1. `cliqueFree_of_hom` — **`K_r`-freeness pulls back along homomorphisms**, for every
   `r`. If there is a graph homomorphism `f : G → H` and `H` has no `r`-clique, then
   neither does `G`. (Irreflexivity of `H` makes the images of a `G`-clique distinct,
   hence a genuine `H`-clique.) The parent `triangleFree_of_hom` is the case `r = 3`.

2. `hasClique_mono` / `cliqueFree_mono` — clique-freeness is **monotone in the order**:
   a smaller clique sits inside a larger one, so `K_m`-freeness forces `K_r`-freeness
   for every `r ≥ m`. In particular triangle-free (`K_3`-free) ⟹ `K_r`-free for all
   `r ≥ 3`.

3. `hasTriangle_iff_hasClique_three` and `triangleFree_iff_cliqueFree_three` — the
   **bridge** identifying the parent's `hasTriangle` / `triangleFree` with the `r = 3`
   case of the clique predicates, recovering `triangleFree_of_hom` as a corollary.

4. `blowup_cliqueFree` — every blow-up of a `K_r`-free graph is `K_r`-free.

5. `C5_cliqueFree` — `C₅` has no `r`-clique for any `r ≥ 3`, and hence
   `blowup_C5_cliqueFree` — **every blow-up of `C₅` is `K_r`-free for all `r ≥ 3`**, at
   every size. This is the clique-order-uniform strengthening of the extremal
   construction's triangle-freeness.

## Summary: 0 sorries, 0 axioms, no `native_decide`. Self-contained over Mathlib.
-/

set_option linter.unusedVariables false

namespace Erdos128WIP01OQ01OQ01

/-- A simple graph on `n` vertices. -/
structure Graph (n : ℕ) where
  adj : Fin n → Fin n → Prop
  symm : ∀ u v, adj u v → adj v u
  irrefl : ∀ v, ¬ adj v v

/-- `G` contains a triangle: three distinct, mutually adjacent vertices. -/
def Graph.hasTriangle {n : ℕ} (G : Graph n) : Prop :=
  ∃ u v w : Fin n, u ≠ v ∧ v ≠ w ∧ u ≠ w ∧
    G.adj u v ∧ G.adj v w ∧ G.adj u w

/-- `G` is triangle-free. -/
def Graph.triangleFree {n : ℕ} (G : Graph n) : Prop := ¬ G.hasTriangle

/-- `G` contains an **`r`-clique**: an injective family of `r` vertices that are
    pairwise adjacent. The injection records the `r` distinct vertices; pairwise
    adjacency of distinct indices is the clique condition. -/
def Graph.hasClique {n : ℕ} (G : Graph n) (r : ℕ) : Prop :=
  ∃ s : Fin r → Fin n, Function.Injective s ∧ ∀ i j, i ≠ j → G.adj (s i) (s j)

/-- `G` is **`K_r`-free**: it has no `r`-clique. -/
def Graph.cliqueFree {n : ℕ} (G : Graph n) (r : ℕ) : Prop := ¬ G.hasClique r

/-- A **graph homomorphism** `f : G → H`: it carries adjacent vertices to adjacent
    vertices. (No injectivity or surjectivity is required.) -/
def IsHom {n k : ℕ} (G : Graph n) (H : Graph k) (f : Fin n → Fin k) : Prop :=
  ∀ u v, G.adj u v → H.adj (f u) (f v)

/-- **`K_r`-freeness pulls back along graph homomorphisms.** If there is a
    homomorphism `f : G → H` and `H` is `K_r`-free, then so is `G`.

    Given an `r`-clique `s` of `G`, the composite `f ∘ s` is an `r`-clique of `H`:
    its entries are pairwise adjacent because `f` preserves edges, and they are
    distinct because `H` is irreflexive — two equal images would be an `H`-loop. This
    generalises `triangleFree_of_hom` (the case `r = 3`) from the parent file. -/
theorem cliqueFree_of_hom {n k r : ℕ} (G : Graph n) (H : Graph k) (f : Fin n → Fin k)
    (hf : IsHom G H f) (hH : H.cliqueFree r) : G.cliqueFree r := by
  rintro ⟨s, hinj, hadj⟩
  apply hH
  refine ⟨f ∘ s, ?_, ?_⟩
  · intro a b hab
    simp only [Function.comp_apply] at hab
    by_contra hne
    have hedge := hf (s a) (s b) (hadj a b hne)
    rw [hab] at hedge
    exact H.irrefl (f (s b)) hedge
  · intro i j hij
    simp only [Function.comp_apply]
    exact hf (s i) (s j) (hadj i j hij)

/-- **Clique-freeness is monotone in the order.** A `K_r`-clique restricts to a
    `K_m`-clique whenever `m ≤ r` (take the first `m` of its `r` vertices), so the
    existence of an `r`-clique entails an `m`-clique. -/
theorem hasClique_mono {n : ℕ} (G : Graph n) {m r : ℕ} (hmr : m ≤ r)
    (h : G.hasClique r) : G.hasClique m := by
  obtain ⟨s, hinj, hadj⟩ := h
  refine ⟨s ∘ Fin.castLE hmr, hinj.comp (Fin.castLE_injective hmr), ?_⟩
  intro i j hij
  simp only [Function.comp_apply]
  exact hadj _ _ (fun heq => hij (Fin.castLE_injective hmr heq))

/-- **`K_m`-freeness forces `K_r`-freeness for every `r ≥ m`.** Contrapositive of
    `hasClique_mono`: if there were an `r`-clique it would contain an `m`-clique. -/
theorem cliqueFree_mono {n : ℕ} (G : Graph n) {m r : ℕ} (hmr : m ≤ r)
    (h : G.cliqueFree m) : G.cliqueFree r :=
  fun hr => h (hasClique_mono G hmr hr)

/-- An explicit triple `Fin 3 → Fin n` used to package a triangle as a `3`-clique. -/
def triple {n : ℕ} (u v w : Fin n) : Fin 3 → Fin n :=
  fun i => if i = 0 then u else if i = 1 then v else w

/-- **A triangle is exactly a `3`-clique.** The two formulations of "three distinct
    mutually adjacent vertices" agree. -/
theorem hasTriangle_iff_hasClique_three {n : ℕ} (G : Graph n) :
    G.hasTriangle ↔ G.hasClique 3 := by
  constructor
  · rintro ⟨u, v, w, huv, hvw, huw, auv, avw, auw⟩
    refine ⟨triple u v w, ?_, ?_⟩
    · intro i j h
      fin_cases i <;> fin_cases j <;> simp_all [triple]
    · have avu := G.symm _ _ auv
      have awv := G.symm _ _ avw
      have awu := G.symm _ _ auw
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [triple]
  · rintro ⟨s, hinj, hadj⟩
    exact ⟨s 0, s 1, s 2,
      fun h => absurd (hinj h) (by decide),
      fun h => absurd (hinj h) (by decide),
      fun h => absurd (hinj h) (by decide),
      hadj 0 1 (by decide), hadj 1 2 (by decide), hadj 0 2 (by decide)⟩

/-- **Triangle-freeness is `K_3`-freeness.** -/
theorem triangleFree_iff_cliqueFree_three {n : ℕ} (G : Graph n) :
    G.triangleFree ↔ G.cliqueFree 3 :=
  not_congr (hasTriangle_iff_hasClique_three G)

/-- **Triangle-freeness pulls back along homomorphisms** — recovered as the `r = 3`
    case of `cliqueFree_of_hom` via the bridge, reproducing the parent result. -/
theorem triangleFree_of_hom {n k : ℕ} (G : Graph n) (H : Graph k) (f : Fin n → Fin k)
    (hf : IsHom G H f) (hH : H.triangleFree) : G.triangleFree :=
  (triangleFree_iff_cliqueFree_three G).2
    (cliqueFree_of_hom G H f hf ((triangleFree_iff_cliqueFree_three H).1 hH))

/-- The **blow-up** of a base graph `H` along a class map `c : Fin n → Fin k`: two
    vertices are adjacent exactly when their classes are adjacent in `H`. -/
def blowup {n k : ℕ} (H : Graph k) (c : Fin n → Fin k) : Graph n where
  adj u v := H.adj (c u) (c v)
  symm u v h := H.symm (c u) (c v) h
  irrefl v h := H.irrefl (c v) h

/-- The class map of a blow-up is a graph homomorphism `blowup H c → H`. -/
theorem blowup_isHom {n k : ℕ} (H : Graph k) (c : Fin n → Fin k) :
    IsHom (blowup H c) H c := fun u v h => h

/-- **Every blow-up of a `K_r`-free graph is `K_r`-free.** -/
theorem blowup_cliqueFree {n k r : ℕ} (H : Graph k) (c : Fin n → Fin k)
    (hH : H.cliqueFree r) : (blowup H c).cliqueFree r :=
  cliqueFree_of_hom (blowup H c) H c (blowup_isHom H c) hH

/-- The **5-cycle `C₅`** on `Fin 5`: `i ~ j` iff they are one step apart around the
    cycle (modulo 5). -/
def C5 : Graph 5 where
  adj i j := i + 1 = j ∨ j + 1 = i
  symm u v h := h.symm
  irrefl := by decide

/-- **`C₅` is triangle-free** (decision procedure over `Fin 5`, not `native_decide`). -/
theorem C5_triangleFree : C5.triangleFree := by
  unfold Graph.triangleFree Graph.hasTriangle C5
  decide

/-- **`C₅` is `K_r`-free for every `r ≥ 3`.** It is triangle-free, and clique-freeness
    is monotone in the order. -/
theorem C5_cliqueFree {r : ℕ} (hr : 3 ≤ r) : C5.cliqueFree r :=
  cliqueFree_mono C5 hr ((triangleFree_iff_cliqueFree_three C5).1 C5_triangleFree)

/-- **Every blow-up of `C₅` is `K_r`-free for all `r ≥ 3`**, at every size `n` and for
    every class assignment `c : Fin n → Fin 5`. The conjectured-optimal extremal
    construction for Erdős #128 contains no clique of any order `≥ 3` — a strengthening,
    uniform in clique order, of its triangle-freeness. -/
theorem blowup_C5_cliqueFree {n r : ℕ} (c : Fin n → Fin 5) (hr : 3 ≤ r) :
    (blowup C5 c).cliqueFree r :=
  blowup_cliqueFree C5 c (C5_cliqueFree hr)

/-
## Significance

Erdős #128 asks whether density on every large induced subgraph forces a triangle; its
conjecturally optimal constant `1/50` is witnessed by blow-ups of `C₅`. The parent chain
showed triangle-freeness is hereditary and, sharper, homomorphism-monotone. This file
lifts the homomorphism-pullback principle from triangles to cliques of **every order**:
`cliqueFree_of_hom` shows `K_r`-freeness pulls back along any homomorphism, and
`cliqueFree_mono` shows clique-freeness is monotone in `r`. Together with the bridge
`triangleFree_iff_cliqueFree_three` (which recovers the parent's `triangleFree_of_hom`),
they yield `blowup_C5_cliqueFree`: the extremal `C₅`-blow-ups contain no clique of any
order `≥ 3`, at every scale. The remaining analytic content — that these blow-ups
achieve induced density `> 1/50`, and that this constant is optimal — stays open.
-/

end Erdos128WIP01OQ01OQ01
