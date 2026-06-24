import Mathlib

/-
# Erdős #128 — triangle-freeness pulls back along graph homomorphisms
# (erdos-128-wip-01-oq-01)

## The Problem

**Erdős Problem #128** ($250, OPEN). If every induced subgraph of an `n`-vertex
graph `G` on `≥ ⌊n/2⌋` vertices has more than `n²/50` edges, must `G` contain a
triangle? The constant `1/50` is conjectured optimal, witnessed by **blow-ups of
`C₅`**: replace each vertex of the 5-cycle by an independent class and join two
classes completely exactly when their `C₅`-vertices are adjacent. These blow-ups
are triangle-free with induced-subgraph density `> 1/50` at every scale.

The parent file `Erdos128WIP01.lean` proved that triangle-freeness is **hereditary**
(passes to induced subgraphs) and that the edge count is monotone under induction.
This file isolates the *structural reason the extremal witnesses are triangle-free*:
triangle-freeness is preserved not only under induced subgraphs but under **arbitrary
graph homomorphisms**, pulled back along the map. A blow-up is precisely the graph
whose adjacency is the pullback of the base graph's adjacency along the class map,
so triangle-freeness of `C₅` transfers to every one of its blow-ups, of every size.

## Result

Working in a self-contained re-declaration of the parent's `Graph` objects:

1. `triangleFree_of_hom` — **triangle-freeness pulls back along homomorphisms.** If
   there is a graph homomorphism `f : G → H` (adjacent vertices map to adjacent
   vertices) and `H` is triangle-free, then `G` is triangle-free. (Irreflexivity of
   `H` supplies the distinctness of the three image vertices, so a triangle of `G`
   would force a genuine triangle of `H`.) This subsumes the parent's hereditary
   property: an induced subgraph maps into its ambient graph by the identity.

2. `blowup` / `blowup_isHom` — the **blow-up** of a base graph `H` along a class map
   `c` is the graph on `Fin n` with `adj u v := H.adj (c u) (c v)`; the class map is
   a homomorphism `blowup H c → H`.

3. `blowup_triangleFree` — every blow-up of a triangle-free graph is triangle-free.

4. `C5_triangleFree` — the concrete 5-cycle `C₅` is triangle-free (decision procedure).

5. `blowup_C5_triangleFree` — **hence every blow-up of `C₅` is triangle-free**, at
   every size `n` and for every class assignment `c : Fin n → Fin 5`. This is exactly
   the triangle-freeness of the conjectured-optimal extremal construction.

## Summary: 0 sorries, 0 axioms, no `native_decide`. Self-contained over Mathlib.
-/

set_option linter.unusedVariables false

namespace Erdos128WIP01OQ01

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

/-- A **graph homomorphism** `f : G → H`: it carries adjacent vertices to adjacent
    vertices. (No injectivity or surjectivity is required.) -/
def IsHom {n k : ℕ} (G : Graph n) (H : Graph k) (f : Fin n → Fin k) : Prop :=
  ∀ u v, G.adj u v → H.adj (f u) (f v)

/-- **Triangle-freeness pulls back along graph homomorphisms.** If there is a
    homomorphism `f : G → H` and `H` is triangle-free, then `G` is triangle-free.

    The three image vertices of a `G`-triangle are automatically distinct: each edge
    of `H` joins distinct endpoints because `H` is irreflexive, so the images form a
    genuine `H`-triangle — contradicting `H`'s triangle-freeness. This generalises the
    parent file's hereditary property (`triangleFree_induce`), which is the case where
    `f` is the identity inclusion of an induced subgraph. -/
theorem triangleFree_of_hom {n k : ℕ} (G : Graph n) (H : Graph k) (f : Fin n → Fin k)
    (hf : IsHom G H f) (hH : H.triangleFree) : G.triangleFree := by
  rintro ⟨u, v, w, -, -, -, a1, a2, a3⟩
  apply hH
  have b1 := hf u v a1
  have b2 := hf v w a2
  have b3 := hf u w a3
  refine ⟨f u, f v, f w, ?_, ?_, ?_, b1, b2, b3⟩
  · intro h; rw [h] at b1; exact H.irrefl (f v) b1
  · intro h; rw [h] at b2; exact H.irrefl (f w) b2
  · intro h; rw [h] at b3; exact H.irrefl (f w) b3

/-- The **blow-up** of a base graph `H` along a class map `c : Fin n → Fin k`: two
    vertices are adjacent exactly when their classes are adjacent in `H`. This is the
    formal extremal construction — `C₅`-blow-ups arise as `blowup C5 c`. -/
def blowup {n k : ℕ} (H : Graph k) (c : Fin n → Fin k) : Graph n where
  adj u v := H.adj (c u) (c v)
  symm u v h := H.symm (c u) (c v) h
  irrefl v h := H.irrefl (c v) h

/-- The class map of a blow-up is a graph homomorphism `blowup H c → H`. -/
theorem blowup_isHom {n k : ℕ} (H : Graph k) (c : Fin n → Fin k) :
    IsHom (blowup H c) H c := fun u v h => h

/-- **Every blow-up of a triangle-free graph is triangle-free.** A corollary of
    `triangleFree_of_hom` applied to the class map. -/
theorem blowup_triangleFree {n k : ℕ} (H : Graph k) (c : Fin n → Fin k)
    (hH : H.triangleFree) : (blowup H c).triangleFree :=
  triangleFree_of_hom (blowup H c) H c (blowup_isHom H c) hH

/-- The **5-cycle `C₅`** on `Fin 5`: `i ~ j` iff they are one step apart around the
    cycle (`i + 1 = j` or `j + 1 = i`, with addition modulo 5). -/
def C5 : Graph 5 where
  adj i j := i + 1 = j ∨ j + 1 = i
  symm u v h := h.symm
  irrefl := by decide

/-- **`C₅` is triangle-free.** No three vertices of the 5-cycle are mutually adjacent;
    verified by the decision procedure over `Fin 5` (not `native_decide`). -/
theorem C5_triangleFree : C5.triangleFree := by
  unfold Graph.triangleFree Graph.hasTriangle C5
  decide

/-- **Every blow-up of `C₅` is triangle-free**, for every size `n` and every class
    assignment `c : Fin n → Fin 5`. This is precisely the triangle-freeness of the
    conjectured-optimal extremal construction for Erdős #128: the `1/50` constant is
    expected to be witnessed by `C₅`-blow-ups, and those witnesses are triangle-free
    at every scale because triangle-freeness pulls back along the class map. -/
theorem blowup_C5_triangleFree {n : ℕ} (c : Fin n → Fin 5) :
    (blowup C5 c).triangleFree :=
  blowup_triangleFree C5 c C5_triangleFree

/-
## Significance

Erdős #128 asks whether density on every large induced subgraph forces a triangle.
Its conjecturally optimal constant `1/50` is witnessed by blow-ups of `C₅`. The parent
file showed triangle-freeness is hereditary; this file identifies the sharper
structural fact underlying the extremal witnesses: triangle-freeness is preserved
under **arbitrary graph homomorphisms** (`triangleFree_of_hom`), of which both induced
subgraphs (identity map) and blow-ups (class map) are instances. Concretely, `C₅` is
triangle-free (`C5_triangleFree`) and therefore so is every blow-up of it, at every
size (`blowup_C5_triangleFree`). The remaining, genuinely hard analytic content — that
these blow-ups achieve induced density `> 1/50`, and that this constant is optimal —
stays open.
-/

end Erdos128WIP01OQ01
