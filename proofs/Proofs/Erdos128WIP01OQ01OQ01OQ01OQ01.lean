/-
# Erdős #128: Forbidden-subgraph freeness is hereditary, and the C₅-blow-up
  extremal family is hereditarily clique-free

## Source
Open question from `erdos-128-wip-01-oq-01-oq-01-oq-01` (the forbidden-subgraph
framework: `homFree`, `blowup`, `C5`) combined with `erdos-128-wip-01`'s induced
subgraph `Graph.induce` and its hereditary triangle-freeness.

## What This Proves

The parent established that forbidden-subgraph freeness `homFree F G`
("`G` has no homomorphic copy of `F`") pulls back along homomorphisms, with
clique-freeness the `F = Kᵣ` case, and that every blow-up of `C₅` is `Kᵣ`-free
for `r ≥ 3`. The original `erdos-128-wip-01` separately proved triangle-freeness
is **hereditary** (closed under induced subgraphs).

This entry unifies the two threads: it shows the *whole* forbidden-subgraph
relation is hereditary, because the inclusion of an induced subgraph is a graph
homomorphism. Specialising to `F = Kᵣ` gives hereditary clique-freeness, and
specialising further to the `C₅` blow-ups shows the extremal family for #128 is
hereditarily clique-free — exactly the property a candidate extremal
construction must have, since #128 constrains *every* `⌊n/2⌋`-vertex induced
subgraph.

**Main results:**
- `induce_isHom`: the identity is a homomorphism `G.induce S → G`.
- `homFree_induce`: `homFree F G → homFree F (G.induce S)` — forbidden-subgraph
  freeness is hereditary.
- `cliqueFree_induce`: `G.cliqueFree r → (G.induce S).cliqueFree r`.
- `blowup_C5_induce_homFree` / `blowup_C5_induce_cliqueFree`: every induced
  subgraph of every blow-up of `C₅` is `Kᵣ`-(hom-copy-)free for `r ≥ 3`.

## Structure of the Argument

An induced subgraph only deletes edges, so the identity map carries every edge
of `G.induce S` to an edge of `G`: it is a homomorphism `G.induce S → G`. The
parent's `homFree_of_hom` then pulls back `F`-freeness from `G` to `G.induce S`
with no further work. Clique-freeness is the `F = Kᵣ` instance via the parent's
bridge `cliqueFree_iff_homFree_completeGraph`, and the `C₅`-blow-up corollaries
chain this with `blowup_C5_homFree`.

The file is self-contained (the chain's convention: each entry re-derives the
small graph framework it needs), fully machine-checked, no `sorry`, no extra
axioms. `C5_homFree_three` uses ordinary `decide`, not `native_decide`.

## Depends on
Mathlib only. Mirrors the framework of `erdos-128-wip-01-oq-01-oq-01-oq-01`
(`homFree`, `homFree_of_hom`, `blowup`, `C5`) and `erdos-128-wip-01`
(`Graph.induce`).
-/

import Mathlib

set_option linter.unusedVariables false

namespace Erdos128WIP01OQ01OQ01OQ01OQ01

/-- A finite simple graph on `Fin n`, given by a symmetric irreflexive adjacency. -/
structure Graph (n : ℕ) where
  adj : Fin n → Fin n → Prop
  symm : ∀ u v, adj u v → adj v u
  irrefl : ∀ v, ¬ adj v v

/-- The **induced subgraph** on a vertex subset `S`: keep only edges with both
    endpoints in `S`. -/
def Graph.induce {n : ℕ} (G : Graph n) (S : Finset (Fin n)) : Graph n where
  adj u v := u ∈ S ∧ v ∈ S ∧ G.adj u v
  symm u v h := ⟨h.2.1, h.1, G.symm u v h.2.2⟩
  irrefl v h := G.irrefl v h.2.2

/-- A **graph homomorphism** `f : G → H` carries adjacent vertices to adjacent
    vertices. -/
def IsHom {n k : ℕ} (G : Graph n) (H : Graph k) (f : Fin n → Fin k) : Prop :=
  ∀ u v, G.adj u v → H.adj (f u) (f v)

/-- `G` **contains a homomorphic copy of `F`**: a graph homomorphism `φ : F → G`. -/
def hasHomCopy {m n : ℕ} (F : Graph m) (G : Graph n) : Prop :=
  ∃ φ : Fin m → Fin n, IsHom F G φ

/-- `G` is **`F`-free**: it has no homomorphic copy of `F`. -/
def homFree {m n : ℕ} (F : Graph m) (G : Graph n) : Prop := ¬ hasHomCopy F G

/-- **`F`-freeness pulls back along homomorphisms** (parent's `homFree_of_hom`):
    a homomorphism `f : G → H` with `H` `F`-free makes `G` `F`-free, by composing
    a copy `φ : F → G` with `f`. -/
theorem homFree_of_hom {m n k : ℕ} (F : Graph m) (G : Graph n) (H : Graph k)
    (f : Fin n → Fin k) (hf : IsHom G H f) (hH : homFree F H) : homFree F G := by
  rintro ⟨φ, hφ⟩
  exact hH ⟨f ∘ φ, fun a b hab => hf _ _ (hφ a b hab)⟩

/-- A homomorphism `g : F' → F` turns a copy of `F` into one of `F'` (precompose). -/
theorem hasHomCopy_mono {m' m n : ℕ} (F' : Graph m') (F : Graph m) (G : Graph n)
    (g : Fin m' → Fin m) (hg : IsHom F' F g) (h : hasHomCopy F G) : hasHomCopy F' G := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ ∘ g, fun a b hab => hφ (g a) (g b) (hg a b hab)⟩

/-! ### Cliques as the `F = Kᵣ` case -/

/-- `G` contains an **`r`-clique**: an injective family of `r` pairwise-adjacent vertices. -/
def Graph.hasClique {n : ℕ} (G : Graph n) (r : ℕ) : Prop :=
  ∃ s : Fin r → Fin n, Function.Injective s ∧ ∀ i j, i ≠ j → G.adj (s i) (s j)

/-- `G` is **`Kᵣ`-free**. -/
def Graph.cliqueFree {n : ℕ} (G : Graph n) (r : ℕ) : Prop := ¬ G.hasClique r

/-- The **complete graph `Kᵣ`** on `Fin r`. -/
def completeGraph (r : ℕ) : Graph r where
  adj i j := i ≠ j
  symm u v h := Ne.symm h
  irrefl v h := h rfl

/-- The inclusion `Fin.castLE` is a homomorphism `Kₘ → Kᵣ` for `m ≤ r`. -/
theorem completeGraph_castLE_isHom {m r : ℕ} (hmr : m ≤ r) :
    IsHom (completeGraph m) (completeGraph r) (Fin.castLE hmr) :=
  fun a b hab heq => hab (Fin.castLE_injective hmr heq)

/-- **A homomorphic copy of `Kᵣ` is exactly an `r`-clique** (the target's
    irreflexivity forces a homomorphism out of `Kᵣ` to be injective). -/
theorem hasHomCopy_completeGraph_iff {n : ℕ} (G : Graph n) (r : ℕ) :
    hasHomCopy (completeGraph r) G ↔ G.hasClique r := by
  constructor
  · rintro ⟨φ, hφ⟩
    refine ⟨φ, ?_, fun i j hij => hφ i j hij⟩
    intro a b hab
    by_contra hne
    exact G.irrefl (φ b) (hab ▸ hφ a b hne)
  · rintro ⟨s, hinj, hadj⟩
    exact ⟨s, fun a b hab => hadj a b hab⟩

/-- **`Kᵣ`-freeness is `Kᵣ`-homomorphic-copy-freeness.** -/
theorem cliqueFree_iff_homFree_completeGraph {n : ℕ} (G : Graph n) (r : ℕ) :
    G.cliqueFree r ↔ homFree (completeGraph r) G :=
  not_congr (hasHomCopy_completeGraph_iff G r).symm

/-- **`Kᵣ`-freeness pulls back along homomorphisms** — the `F = Kᵣ` corollary. -/
theorem cliqueFree_of_hom {n k r : ℕ} (G : Graph n) (H : Graph k) (f : Fin n → Fin k)
    (hf : IsHom G H f) (hH : H.cliqueFree r) : G.cliqueFree r :=
  (cliqueFree_iff_homFree_completeGraph G r).2
    (homFree_of_hom (completeGraph r) G H f hf
      ((cliqueFree_iff_homFree_completeGraph H r).1 hH))

/-! ### Hereditarity: the identity inclusion of an induced subgraph is a homomorphism -/

/-- **The identity is a homomorphism `G.induce S → G`.** Induction only deletes
    edges, so every edge of `G.induce S` is an edge of `G`. -/
theorem induce_isHom {n : ℕ} (G : Graph n) (S : Finset (Fin n)) :
    IsHom (G.induce S) G id := fun u v h => h.2.2

/-- **Forbidden-subgraph freeness is hereditary.** Every induced subgraph of an
    `F`-free graph is `F`-free — pull `homFree` back along the inclusion. -/
theorem homFree_induce {m n : ℕ} (F : Graph m) (G : Graph n) (S : Finset (Fin n))
    (hG : homFree F G) : homFree F (G.induce S) :=
  homFree_of_hom F (G.induce S) G id (induce_isHom G S) hG

/-- **Clique-freeness is hereditary.** Every induced subgraph of a `Kᵣ`-free graph
    is `Kᵣ`-free — the `F = Kᵣ` instance (also direct from `cliqueFree_of_hom`). -/
theorem cliqueFree_induce {n : ℕ} (G : Graph n) (r : ℕ) (S : Finset (Fin n))
    (hG : G.cliqueFree r) : (G.induce S).cliqueFree r :=
  cliqueFree_of_hom (G.induce S) G id (induce_isHom G S) hG

/-! ### Blow-ups and the `C₅` witness -/

/-- The **blow-up** of `H` along a class map `c`: adjacency is read off the classes. -/
def blowup {n k : ℕ} (H : Graph k) (c : Fin n → Fin k) : Graph n where
  adj u v := H.adj (c u) (c v)
  symm u v h := H.symm (c u) (c v) h
  irrefl v h := H.irrefl (c v) h

/-- The class map of a blow-up is a homomorphism `blowup H c → H`. -/
theorem blowup_isHom {n k : ℕ} (H : Graph k) (c : Fin n → Fin k) :
    IsHom (blowup H c) H c := fun u v h => h

/-- **Every blow-up of an `F`-free graph is `F`-free.** -/
theorem blowup_homFree {m n k : ℕ} (F : Graph m) (H : Graph k) (c : Fin n → Fin k)
    (hH : homFree F H) : homFree F (blowup H c) :=
  homFree_of_hom F (blowup H c) H c (blowup_isHom H c) hH

/-- The **5-cycle `C₅`** on `Fin 5`. -/
def C5 : Graph 5 where
  adj i j := i + 1 = j ∨ j + 1 = i
  symm u v h := h.symm
  irrefl := by decide

set_option maxRecDepth 4000 in
/-- **`C₅` has no homomorphic copy of `K₃`** (ordinary `decide`, not `native_decide`). -/
theorem C5_homFree_three : homFree (completeGraph 3) C5 := by
  unfold homFree hasHomCopy IsHom completeGraph C5
  decide

/-- **`C₅` has no homomorphic copy of `Kᵣ` for any `r ≥ 3`.** -/
theorem C5_homFree {r : ℕ} (hr : 3 ≤ r) : homFree (completeGraph r) C5 :=
  fun h => C5_homFree_three
    (hasHomCopy_mono (completeGraph 3) (completeGraph r) C5 _
      (completeGraph_castLE_isHom hr) h)

/-- **Every blow-up of `C₅` is `Kᵣ`-hom-copy-free for `r ≥ 3`.** -/
theorem blowup_C5_homFree {n r : ℕ} (c : Fin n → Fin 5) (hr : 3 ≤ r) :
    homFree (completeGraph r) (blowup C5 c) :=
  blowup_homFree (completeGraph r) C5 c (C5_homFree hr)

/-- **`C₅` is `Kᵣ`-free for `r ≥ 3`.** -/
theorem C5_cliqueFree {r : ℕ} (hr : 3 ≤ r) : C5.cliqueFree r :=
  (cliqueFree_iff_homFree_completeGraph C5 r).2 (C5_homFree hr)

/-- **Every blow-up of `C₅` is `Kᵣ`-free for `r ≥ 3`.** -/
theorem blowup_C5_cliqueFree {n r : ℕ} (c : Fin n → Fin 5) (hr : 3 ≤ r) :
    (blowup C5 c).cliqueFree r :=
  (cliqueFree_iff_homFree_completeGraph (blowup C5 c) r).2 (blowup_C5_homFree c hr)

/-! ### The extremal family is hereditarily clique-free -/

/-- **Every induced subgraph of every blow-up of `C₅` is `Kᵣ`-hom-copy-free**
    for `r ≥ 3` — hereditarity applied to the extremal family. -/
theorem blowup_C5_induce_homFree {n r : ℕ} (c : Fin n → Fin 5) (S : Finset (Fin n))
    (hr : 3 ≤ r) : homFree (completeGraph r) ((blowup C5 c).induce S) :=
  homFree_induce (completeGraph r) (blowup C5 c) S (blowup_C5_homFree c hr)

/-- **Every induced subgraph of every blow-up of `C₅` is `Kᵣ`-free** for `r ≥ 3`.
    Taking `r = 3`, every induced subgraph of a `C₅` blow-up is triangle-free:
    the candidate extremal construction for #128 keeps its forbidden-subgraph
    property on *every* vertex subset, in particular on every `⌊n/2⌋`-subgraph. -/
theorem blowup_C5_induce_cliqueFree {n r : ℕ} (c : Fin n → Fin 5) (S : Finset (Fin n))
    (hr : 3 ≤ r) : ((blowup C5 c).induce S).cliqueFree r :=
  cliqueFree_induce (blowup C5 c) r S (blowup_C5_cliqueFree c hr)

end Erdos128WIP01OQ01OQ01OQ01OQ01
