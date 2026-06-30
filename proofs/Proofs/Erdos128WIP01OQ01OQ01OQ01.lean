import Mathlib

/-
# Erdős #128 — forbidden-subgraph freeness pulls back along homomorphisms
# (erdos-128-wip-01-oq-01-oq-01-oq-01)

## The Problem

**Erdős Problem #128** ($250, OPEN). If every induced subgraph of an `n`-vertex
graph `G` on `≥ ⌊n/2⌋` vertices has more than `n²/50` edges, must `G` contain a
triangle? The constant `1/50` is conjectured optimal, witnessed by **blow-ups of
`C₅`**, which are triangle-free with induced density `> 1/50` at every scale.

The parent chain showed triangle-freeness is hereditary (`Erdos128WIP01.lean`),
then that it pulls back along **graph homomorphisms** (`triangleFree_of_hom`,
`Erdos128WIP01OQ01.lean`), and then lifted that pullback from triangles to
**`K_r`-cliques of every order** (`cliqueFree_of_hom`, `Erdos128WIP01OQ01OQ01.lean`).
That last entry's stated open question asks to generalise once more — beyond
cliques to **arbitrary forbidden subgraphs `F`**, "of which clique-freeness is the
`F = K_r` case." This file answers it.

## Result

The right notion is a **homomorphic copy** of `F`: a graph homomorphism
`φ : F → G` (no injectivity required). Working self-contained over Mathlib:

1. `homFree_of_hom` — **`F`-homomorphic-copy-freeness pulls back along homomorphisms**,
   for *every* fixed graph `F`. If there is a homomorphism `f : G → H` and `H` has no
   homomorphic copy of `F`, then neither does `G`. The proof is *pure composition*:
   `f ∘ φ` is a homomorphic copy of `F` in `H`. No irreflexivity is needed here — the
   irreflexivity that the clique argument used reappears only in the bridge below.

2. `hasHomCopy_mono` — **homomorphic-copy containment is monotone along homomorphisms**:
   a homomorphism `F' → F` turns a homomorphic copy of `F` into one of `F'`. This
   generalises the clique-order monotonicity `hasClique_mono` (which is the inclusion
   `K_m → K_r`).

3. `hasHomCopy_completeGraph_iff` / `cliqueFree_iff_homFree_completeGraph` — **the bridge**.
   Over an irreflexive target, a homomorphic copy of the complete graph `K_r` is exactly
   an `r`-clique (the homomorphism is forced injective by irreflexivity). Hence
   `K_r`-freeness *is* `K_r`-homomorphic-copy-freeness, and `cliqueFree_of_hom` is recovered
   as the `F = K_r` corollary of `homFree_of_hom`.

4. `blowup_homFree` — every blow-up of an `F`-free graph is `F`-free, for every `F`.

5. `C5_homFree` / `blowup_C5_homFree` — `C₅` has no homomorphic copy of `K_r` for any
   `r ≥ 3`, hence neither does any blow-up of `C₅`, at every size. Via the bridge this
   recovers `blowup_C5_cliqueFree`: the extremal construction is `K_r`-free for all `r ≥ 3`.

## Summary: 0 sorries, 0 axioms, no `native_decide`. Self-contained over Mathlib.
-/

set_option linter.unusedVariables false

namespace Erdos128WIP01OQ01OQ01OQ01

/-- A simple graph on `n` vertices. -/
structure Graph (n : ℕ) where
  adj : Fin n → Fin n → Prop
  symm : ∀ u v, adj u v → adj v u
  irrefl : ∀ v, ¬ adj v v

/-- A **graph homomorphism** `f : G → H`: it carries adjacent vertices to adjacent
    vertices. (No injectivity or surjectivity is required.) -/
def IsHom {n k : ℕ} (G : Graph n) (H : Graph k) (f : Fin n → Fin k) : Prop :=
  ∀ u v, G.adj u v → H.adj (f u) (f v)

/-! ### Homomorphic copies of a fixed graph `F` -/

/-- `G` **contains a homomorphic copy of `F`**: there is a graph homomorphism
    `φ : F → G`. Unlike a clique this asks for no injectivity — `F`'s edges must be
    realised by edges of `G`, nothing more. -/
def hasHomCopy {m n : ℕ} (F : Graph m) (G : Graph n) : Prop :=
  ∃ φ : Fin m → Fin n, IsHom F G φ

/-- `G` is **`F`-free**: it has no homomorphic copy of `F`. -/
def homFree {m n : ℕ} (F : Graph m) (G : Graph n) : Prop := ¬ hasHomCopy F G

/-- **`F`-freeness pulls back along graph homomorphisms**, for every fixed `F`.
    If there is a homomorphism `f : G → H` and `H` is `F`-free, then so is `G`.

    The argument is *pure composition*: a homomorphic copy `φ : F → G` composed with
    `f` is a homomorphic copy `f ∘ φ : F → H`. No irreflexivity is required — this is
    the general structural reason behind `cliqueFree_of_hom`, with the clique case's
    appeal to irreflexivity isolated entirely in the bridge below. -/
theorem homFree_of_hom {m n k : ℕ} (F : Graph m) (G : Graph n) (H : Graph k)
    (f : Fin n → Fin k) (hf : IsHom G H f) (hH : homFree F H) : homFree F G := by
  rintro ⟨φ, hφ⟩
  exact hH ⟨f ∘ φ, fun a b hab => hf _ _ (hφ a b hab)⟩

/-- **Homomorphic-copy containment is monotone along homomorphisms.** A homomorphism
    `g : F' → F` turns a homomorphic copy of `F` into one of `F'` (precompose). This
    generalises clique-order monotonicity: the inclusion `K_m → K_r` for `m ≤ r`. -/
theorem hasHomCopy_mono {m' m n : ℕ} (F' : Graph m') (F : Graph m) (G : Graph n)
    (g : Fin m' → Fin m) (hg : IsHom F' F g) (h : hasHomCopy F G) : hasHomCopy F' G := by
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ ∘ g, fun a b hab => hφ (g a) (g b) (hg a b hab)⟩

/-! ### Cliques as the `F = K_r` case -/

/-- `G` contains an **`r`-clique**: an injective family of `r` pairwise-adjacent vertices. -/
def Graph.hasClique {n : ℕ} (G : Graph n) (r : ℕ) : Prop :=
  ∃ s : Fin r → Fin n, Function.Injective s ∧ ∀ i j, i ≠ j → G.adj (s i) (s j)

/-- `G` is **`K_r`-free**: it has no `r`-clique. -/
def Graph.cliqueFree {n : ℕ} (G : Graph n) (r : ℕ) : Prop := ¬ G.hasClique r

/-- The **complete graph `K_r`** on `Fin r`: distinct vertices are adjacent. -/
def completeGraph (r : ℕ) : Graph r where
  adj i j := i ≠ j
  symm u v h := Ne.symm h
  irrefl v h := h rfl

/-- The inclusion `Fin.castLE` is a homomorphism `K_m → K_r` for `m ≤ r`. -/
theorem completeGraph_castLE_isHom {m r : ℕ} (hmr : m ≤ r) :
    IsHom (completeGraph m) (completeGraph r) (Fin.castLE hmr) :=
  fun a b hab heq => hab (Fin.castLE_injective hmr heq)

/-- **A homomorphic copy of `K_r` is exactly an `r`-clique** (the target is irreflexive,
    so a homomorphism out of the complete graph is forced injective: distinct vertices
    are adjacent in `K_r`, hence have adjacent — therefore distinct — images). This is
    the precise sense in which clique-freeness is the `F = K_r` instance of `homFree`. -/
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

/-- **`K_r`-freeness is `K_r`-homomorphic-copy-freeness.** -/
theorem cliqueFree_iff_homFree_completeGraph {n : ℕ} (G : Graph n) (r : ℕ) :
    G.cliqueFree r ↔ homFree (completeGraph r) G :=
  not_congr (hasHomCopy_completeGraph_iff G r).symm

/-- **`K_r`-freeness pulls back along homomorphisms** — recovered as the `F = K_r`
    corollary of `homFree_of_hom` through the bridge, reproducing the parent's
    `cliqueFree_of_hom`. -/
theorem cliqueFree_of_hom {n k r : ℕ} (G : Graph n) (H : Graph k) (f : Fin n → Fin k)
    (hf : IsHom G H f) (hH : H.cliqueFree r) : G.cliqueFree r :=
  (cliqueFree_iff_homFree_completeGraph G r).2
    (homFree_of_hom (completeGraph r) G H f hf
      ((cliqueFree_iff_homFree_completeGraph H r).1 hH))

/-! ### Blow-ups and the `C₅` witness -/

/-- The **blow-up** of `H` along a class map `c : Fin n → Fin k`: two vertices are
    adjacent exactly when their classes are adjacent in `H`. -/
def blowup {n k : ℕ} (H : Graph k) (c : Fin n → Fin k) : Graph n where
  adj u v := H.adj (c u) (c v)
  symm u v h := H.symm (c u) (c v) h
  irrefl v h := H.irrefl (c v) h

/-- The class map of a blow-up is a homomorphism `blowup H c → H`. -/
theorem blowup_isHom {n k : ℕ} (H : Graph k) (c : Fin n → Fin k) :
    IsHom (blowup H c) H c := fun u v h => h

/-- **Every blow-up of an `F`-free graph is `F`-free**, for every fixed `F` — the
    forbidden-subgraph generalisation of `blowup_cliqueFree`. -/
theorem blowup_homFree {m n k : ℕ} (F : Graph m) (H : Graph k) (c : Fin n → Fin k)
    (hH : homFree F H) : homFree F (blowup H c) :=
  homFree_of_hom F (blowup H c) H c (blowup_isHom H c) hH

/-- The **5-cycle `C₅`** on `Fin 5`: `i ~ j` iff one step apart around the cycle. -/
def C5 : Graph 5 where
  adj i j := i + 1 = j ∨ j + 1 = i
  symm u v h := h.symm
  irrefl := by decide

set_option maxRecDepth 4000 in
/-- **`C₅` has no homomorphic copy of `K₃`** (ordinary decision procedure over the
    finite function space, *not* `native_decide`). -/
theorem C5_homFree_three : homFree (completeGraph 3) C5 := by
  unfold homFree hasHomCopy IsHom completeGraph C5
  decide

/-- **`C₅` has no homomorphic copy of `K_r` for any `r ≥ 3`.** By monotonicity: a copy
    of `K_r` would, via the inclusion `K₃ → K_r`, give a copy of `K₃`. -/
theorem C5_homFree {r : ℕ} (hr : 3 ≤ r) : homFree (completeGraph r) C5 :=
  fun h => C5_homFree_three
    (hasHomCopy_mono (completeGraph 3) (completeGraph r) C5 _
      (completeGraph_castLE_isHom hr) h)

/-- **Every blow-up of `C₅` is `K_r`-homomorphic-copy-free for all `r ≥ 3`**, at every
    size `n` and for every class assignment `c : Fin n → Fin 5`. -/
theorem blowup_C5_homFree {n r : ℕ} (c : Fin n → Fin 5) (hr : 3 ≤ r) :
    homFree (completeGraph r) (blowup C5 c) :=
  blowup_homFree (completeGraph r) C5 c (C5_homFree hr)

/-- **`C₅` is `K_r`-free for every `r ≥ 3`** — the parent's `C5_cliqueFree`, recovered
    from the forbidden-subgraph framework via the bridge. -/
theorem C5_cliqueFree {r : ℕ} (hr : 3 ≤ r) : C5.cliqueFree r :=
  (cliqueFree_iff_homFree_completeGraph C5 r).2 (C5_homFree hr)

/-- **Every blow-up of `C₅` is `K_r`-free for all `r ≥ 3`** — the parent's
    `blowup_C5_cliqueFree`, recovered as an instance of the general `blowup_homFree`. -/
theorem blowup_C5_cliqueFree {n r : ℕ} (c : Fin n → Fin 5) (hr : 3 ≤ r) :
    (blowup C5 c).cliqueFree r :=
  (cliqueFree_iff_homFree_completeGraph (blowup C5 c) r).2 (blowup_C5_homFree c hr)

/-
## Significance

The parent chain narrowed the structural reason the `C₅`-blow-up witnesses for Erdős #128
are triangle-free: triangle-freeness pulls back along homomorphisms, and (one level down)
so does `K_r`-freeness for every clique order. This file isolates the *general* mechanism:
freeness of a homomorphic copy of **any** fixed graph `F` pulls back along homomorphisms,
by nothing more than composing `f ∘ φ`. The clique results are then the `F = K_r` instance —
`hasHomCopy_completeGraph_iff` shows a homomorphic copy of the complete graph is exactly a
clique once the target is irreflexive, recovering `cliqueFree_of_hom`, `C5_cliqueFree`, and
`blowup_C5_cliqueFree` as corollaries. Clique-order monotonicity becomes monotonicity along
homomorphisms `F' → F`. The analytic content of Erdős #128 — that the `C₅`-blow-ups achieve
induced density `> 1/50`, and that `1/50` is optimal — remains open.
-/

end Erdos128WIP01OQ01OQ01OQ01
