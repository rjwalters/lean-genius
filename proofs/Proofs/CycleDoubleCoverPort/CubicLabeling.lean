import Proofs.CycleDoubleCoverPort.EvenCover
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Ring

/-
# Cycle Double Cover port, step 7a: the cubic labelling argument

This is the slice of the port of the openai/cdc-lean development of the Cycle
Double Cover theorem (Szekeres 1973 / Seymour 1979, resolved 2026) that carries
the **new mathematics** of the upstream result. It corresponds to upstream
`CDCLean/CubicLabeling.lean`; see #37507 for the porting order and #43625 /
#43626 for steps 1 and 2.

## Provenance and licensing

`openai/cdc-lean` carries **no license file**, so default copyright applies and
no proof text may be vendored. This file is an *independent re-derivation*: the
upstream source was consulted only for the mathematical content — the shapes of
the definitions and the statements of the results — and every proof script here
was written from scratch against this repository's Mathlib pin. The four purely
finite facts about the eight-element group `Gamma = F₂³` are discharged by
kernel `decide`, which is the only sensible method for a closed statement over a
finite type and carries no authorial expression; every *structural* argument
below (the dual-obstruction calculation, the reindexing lemmas, the labelling
construction) is organised differently from upstream. In particular:

* the dual-obstruction proof is split into three reusable named lemmas
  (`coordinateFunctional_flow_eq_zero`, `sum_coordinateFunctional_edgeAt_eq_zero`,
  `dual_local_slot_identity`) rather than being carried by `have`s inside one
  long tactic block;
* the labelling construction is likewise split into named data
  (`compatibilitySolution`, `labelPotential`, `labelDefect`, `endLabel`,
  `labelBase`) with separately stated properties, so the final structure
  instance is three lines;
* the distinctness of the flow values at a cubic vertex is taken from
  `GammaFlow.val_edgeAt_ne` (proved in step 2 of this port) instead of being
  re-derived, and `DecidableEq V` is never assumed — the vertex-side
  `Pi.single` is produced by a local `classical`.

## Mathematical content

Fix a cubic multigraph `G` and a nowhere-zero `Gamma`-flow `f` on it (`Gamma =
F₂³`, so this is an *8-flow* in the classical language). The goal of the
labelling stage is to attach to every edge `e` a **base point** `p e ∈ Gamma`,
so that the affine pair

  `{p e, p e + f e} ⊆ Gamma`

— the set of indices `s` for which `e` is placed in the `s`-th edge set — has
the property that *every one of the eight resulting edge sets is even at every
vertex*. Since `f` is nowhere zero the pair is genuinely a pair
(`pairIndicator_card` from step 2b), so each edge lands in exactly two of the
eight sets: the cover is an **exact double** cover, not merely a quadruple one.
That last point is the whole reason the 8-flow route works.

### Why base points can be chosen coherently

At a vertex `v` with slot values `x, y, z = x + y` (nowhere-zero and pairwise
distinct, by step 2), the finite fact `local_pair_parity` says that the three
pairs

  `{t, t + x}`, `{t + x, t + x + y}`, `{t, t + x + y}`

based at a common `t` cover every index an even number of times. So evenness at
`v` is automatic *provided* the three base points around `v` are the ones read
off from a single vertex value `t v` via `localBase`. Each edge, however, sits
at two vertices and must be given **one** base point. The two candidate values
must therefore agree up to a shift by a multiple of `f e` — a shift by `f e`
leaves the pair `{p, p + f e}` unchanged (`pairIndicator_eq_of_difference`).

This is a linear system over `F₂`: find `t : V → Gamma` and `ε : E → F₂` with

  `t (e⁰) + t (e¹) + ε e • f e = localBase (e⁰) e + localBase (e¹) e`

for every edge `e`, i.e. `compatibilityRhs G f ∈ range (compatibilityMap G f)`.

### The dual-obstruction calculation

`compatibility_solvable` is the heart of the file. Over a field, a vector lies
in the range of a linear map iff every functional killing the range kills the
vector (`mem_range_of_dual_obstructions_vanish`). Let `φ` kill the range and
write `η e` for its `e`-th coordinate functional. Feeding `φ` the two families
of test vectors gives exactly two obstruction identities:

* edge tests (`ε = Pi.single e 1`): `η e (f e) = 0` for every edge;
* vertex tests (`t = Pi.single v c`): `η e₀ + η e₁ + η e₂ = 0` at every vertex.

Encoding each `η e` by its coordinate vector in `Gamma`, these say that the
three codes `a, b, c` at a vertex sum to zero and are orthogonal to `x`, `y`,
`x + y` respectively. `local_dual_identity` — again a closed finite statement
over `F₂³` — then computes

  `⟨b, x⟩ = [a ≠ 0] + [b ≠ 0] + [c ≠ 0]`,

which is precisely the local contribution of `v` to `φ (compatibilityRhs G f)`
on the left, and the count of nonzero coordinate functionals at `v` on the
right. Summing over all vertices, the right-hand side becomes a sum over edge
*ends*, hence each edge contributes its indicator twice — zero in `F₂`. So
`φ (compatibilityRhs G f) = 0`, and the system is solvable. Nothing about
dimensions of `Gamma` is imported: the only three-dimensional input is the
`decide`-checked `local_dual_identity`.

### Deliberate omissions

`cubic_even_double_cover` (upstream `EvenCover.lean`, which turns a
`CubicLabeling` into a `CubicGraph.IndexedEvenDoubleCover`) and everything in
`CubicTheorem.lean` belong to later steps and are **not** ported here. This
file does not discharge `CycleDoubleCover.cycleDoubleCover_of_bridgeless`.
-/

namespace CycleDoubleCover

open scoped BigOperators

/-! ### Finite facts about the eight-element group `Gamma = F₂³`

Each of the four statements below is closed and quantifies only over the finite
types `Gamma` and `F₂`, so the kernel can verify them exhaustively. Isolating
them here keeps every dimension-dependent input to the argument visible in one
place: no cardinality or dimension lemma about `Gamma` is used anywhere else in
this file. -/

/-- **Local parity at a cubic vertex.** The three affine pairs based at a common
point `t` in the directions `x`, `y` and `x + y` — laid out as they occur around
a vertex whose three slot values are `x`, `y`, `x + y` — cover every index of
`Gamma` an even number of times.

This is what makes each of the eight edge sets even at every vertex, once every
edge incident to `v` receives a base point derived from a single value `t`. -/
theorem local_pair_parity :
    ∀ x y t s : Gamma, x ≠ 0 → y ≠ 0 → x ≠ y →
      pairIndicator t x s +
      pairIndicator (t + x) y s +
      pairIndicator t (x + y) s = 0 := by
  decide

/-- **Shift invariance of affine pairs.** Two base points differing by a
multiple of the (nonzero) direction `h` describe the same pair `{p, p + h}`.

This is the slack that makes the compatibility system solvable at all: an edge's
base point only has to be right up to a shift by its own flow value. -/
theorem pairIndicator_eq_of_difference :
    ∀ (p q h : Gamma) (ε : F₂), h ≠ 0 → p + q = ε • h →
      pairIndicator p h = pairIndicator q h := by
  decide

/-- Characteristic two: a vanishing triple sum determines its last entry. Used
to identify the third slot value at a cubic vertex as the sum of the first
two. -/
theorem gamma_third_eq_add : ∀ x y z : Gamma, x + y + z = 0 → z = x + y := by decide

/-- Characteristic two, one dimension down. Used at the very end of the
dual-obstruction calculation, where every edge is counted once per end. -/
theorem f2_add_self : ∀ a : F₂, a + a = 0 := by decide

/-! ### Local base points and the compatibility system -/

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq E]

/-- The *local base point* of the edge `e` as seen from the vertex `v`: the
distinguished slot at `v` is slot `1`, which is given the value of the flow on
slot `0`, and the two other slots are given `0`.

Choosing one distinguished slot per vertex is an arbitrary but harmless break of
symmetry; it is what turns `local_pair_parity` (whose three pairs are based at
`t`, `t + x` and `t` respectively) into a statement about the three slots at
`v`. -/
def localBase (G : CubicGraph V E) (f : GammaFlow G) (v : V) (e : E) : Gamma :=
  if e = G.edgeAt v 1 then f.val (G.edgeAt v 0) else 0

/-- The right-hand side of the edge compatibility system: the discrepancy
between the local base points that the two endpoints of `e` propose for `e`. -/
def compatibilityRhs (G : CubicGraph V E) (f : GammaFlow G) (e : E) : Gamma :=
  localBase G f (G.endAt e 0) e + localBase G f (G.endAt e 1) e

/-- The left-hand side of the compatibility system, as an `F₂`-linear map. A
solution consists of a vertex potential `t : V → Gamma` together with a per-edge
shift `ε : E → F₂`, and the system asks that the endpoint discrepancy of `t`
plus the allowed shift `ε e • f e` reproduce `compatibilityRhs`.

The `ε` component is exactly the slack recorded by
`pairIndicator_eq_of_difference`; without it the system would be the (generally
unsolvable) demand that a coboundary hit a prescribed edge function. -/
def compatibilityMap (G : CubicGraph V E) (f : GammaFlow G) :
    ((V → Gamma) × (E → F₂)) →ₗ[F₂] (E → Gamma) where
  toFun x e := x.1 (G.endAt e 0) + x.1 (G.endAt e 1) + x.2 e • f.val e
  map_add' x y := by
    funext e
    dsimp only
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul]
    abel
  map_smul' c x := by
    funext e
    dsimp only
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      smul_add, mul_smul]

/-! ### Coordinates of a functional on an edge-indexed product -/

/-- The restriction of a functional on `E → Gamma` to the `e`-th summand.
Together these coordinates determine `φ` (`dual_apply_eq_sum_coordinates`). -/
def coordinateFunctional (φ : Module.Dual F₂ (E → Gamma)) (e : E) :
    Module.Dual F₂ Gamma :=
  φ.comp (LinearMap.single F₂ (fun _ : E ↦ Gamma) e)

/-- A functional on an edge-indexed product is the sum of its coordinates. -/
theorem dual_apply_eq_sum_coordinates (φ : Module.Dual F₂ (E → Gamma)) (y : E → Gamma) :
    φ y = ∑ e : E, coordinateFunctional φ e (y e) := by
  have hy : ∑ e : E, Pi.single e (y e) = y :=
    LinearMap.sum_single_apply (fun _ : E ↦ Gamma) y
  calc
    φ y = φ (∑ e : E, Pi.single e (y e)) := by rw [hy]
    _ = ∑ e : E, φ (Pi.single e (y e)) := map_sum φ _ _
    _ = ∑ e : E, coordinateFunctional φ e (y e) := rfl

/-- **Finite-dimensional separation**, in exactly the form the compatibility
argument consumes: over a field, an element lies in the range of a linear map as
soon as every functional annihilating the range annihilates it. -/
theorem mem_range_of_dual_obstructions_vanish
    {X Y : Type*} [AddCommGroup X] [Module F₂ X] [AddCommGroup Y] [Module F₂ Y]
    (L : X →ₗ[F₂] Y) (b : Y)
    (h : ∀ φ : Module.Dual F₂ Y, (∀ x, φ (L x) = 0) → φ b = 0) :
    b ∈ LinearMap.range L := by
  refine (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff
    (LinearMap.range L : Subspace F₂ Y) b).mp fun φ hφ => h φ fun x => ?_
  exact (Submodule.mem_dualAnnihilator φ).mp hφ (L x) (LinearMap.mem_range_self L x)

/-! ### Coordinates of a functional on `Gamma` itself -/

/-- The coordinate vector of a functional on `Gamma`, read off on the standard
basis. This identifies `Module.Dual F₂ Gamma` with `Gamma`. -/
def functionalCode (η : Module.Dual F₂ Gamma) : Gamma :=
  fun i ↦ η (Pi.single i 1)

/-- The standard `F₂`-valued dot product on `Gamma = F₂³`. -/
def gammaPairing (a x : Gamma) : F₂ := ∑ i : Fin 3, x i * a i

/-- Every functional on `Gamma` is pairing against its coordinate vector. -/
theorem functional_apply_eq_pairing (η : Module.Dual F₂ Gamma) (x : Gamma) :
    η x = gammaPairing (functionalCode η) x := by
  have hx : ∑ i : Fin 3, Pi.single i (x i) = x :=
    LinearMap.sum_single_apply (fun _ : Fin 3 ↦ F₂) x
  have hsingle (i : Fin 3) : Pi.single i (x i) = x i • Pi.single i (1 : F₂) := by
    funext j
    by_cases hj : i = j
    · subst hj; simp
    · simp [Pi.single_eq_of_ne (Ne.symm hj)]
  calc
    η x = η (∑ i : Fin 3, Pi.single i (x i)) := by rw [hx]
    _ = ∑ i : Fin 3, η (Pi.single i (x i)) := map_sum η _ _
    _ = ∑ i : Fin 3, x i * functionalCode η i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hsingle i, map_smul]
        simp [functionalCode]
    _ = gammaPairing (functionalCode η) x := rfl

/-- The `F₂`-valued indicator of "this functional is nonzero". Summing it over
the three slots at a vertex is the right-hand side of `local_dual_identity`. -/
def functionalNonzero (η : Module.Dual F₂ Gamma) : F₂ :=
  if functionalCode η = 0 then 0 else 1

/-- **The three-dimensional local dual identity.** Three codes summing to zero
and orthogonal to `x`, `y` and `x + y` respectively satisfy

  `⟨b, x⟩ = [a ≠ 0] + [b ≠ 0] + [c ≠ 0]`.

This is the only place where the *dimension* of `Gamma` enters the
dual-obstruction argument, and it enters as a closed finite statement verified
by the kernel — no rank or cardinality lemma is imported. -/
theorem local_dual_identity :
    ∀ x y a b c : Gamma,
      x ≠ 0 → y ≠ 0 → x ≠ y →
      a + b + c = 0 →
      gammaPairing a x = 0 → gammaPairing b y = 0 → gammaPairing c (x + y) = 0 →
      gammaPairing b x =
        (if a = 0 then 0 else 1) + (if b = 0 then 0 else 1) +
          (if c = 0 then 0 else 1) := by
  decide

/-- Consequences of a nowhere-zero characteristic-two flow at a cubic vertex,
stated as a standalone finite fact for reuse. In this port the same information
is usually obtained structurally from `GammaFlow.val_edgeAt_ne` and
`gamma_third_eq_add`. -/
theorem flow_triple_properties :
    ∀ x y z : Gamma, x ≠ 0 → y ≠ 0 → z ≠ 0 → x + y + z = 0 →
      z = x + y ∧ x ≠ y := by
  decide

/-! ### Reindexing sums over edge ends as sums over vertex slots -/

/-- A sum over edge ends, evaluated by a dual functional, read off from the
vertex slots instead. This is pure transport along the incidence equivalence
(`CubicGraph.sum_edgeEnds_eq_sum_vertexSlots`); the content is that every edge
end is a vertex slot exactly once. -/
theorem dual_end_sum (G : CubicGraph V E) (φ : Module.Dual F₂ (E → Gamma))
    (q : V → E → Gamma) :
    φ (fun e ↦ q (G.endAt e 0) e + q (G.endAt e 1) e) =
      ∑ v : V, ∑ i : Fin 3,
        coordinateFunctional φ (G.edgeAt v i) (q v (G.edgeAt v i)) := by
  have key := G.sum_edgeEnds_eq_sum_vertexSlots
    (fun (e : E) (j : Fin 2) => coordinateFunctional φ e (q (G.endAt e j) e))
  dsimp only at key
  simp only [CubicGraph.endAt_edgeAt_incidence] at key
  rw [dual_apply_eq_sum_coordinates, ← key]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [map_add, Fin.sum_univ_two]

/-- The vertex half of the compatibility map, dualised. -/
theorem dual_compatibility_vertex_part (G : CubicGraph V E) (f : GammaFlow G)
    (φ : Module.Dual F₂ (E → Gamma)) (t : V → Gamma) :
    φ (compatibilityMap G f (t, 0)) =
      ∑ v : V, ∑ i : Fin 3, coordinateFunctional φ (G.edgeAt v i) (t v) := by
  have hmap : compatibilityMap G f (t, 0) = fun e ↦ t (G.endAt e 0) + t (G.endAt e 1) := by
    funext e
    show t (G.endAt e 0) + t (G.endAt e 1) + (0 : F₂) • f.val e
      = t (G.endAt e 0) + t (G.endAt e 1)
    rw [zero_smul, add_zero]
  rw [hmap]
  exact dual_end_sum G φ (fun v _ ↦ t v)

/-- The edge half of the compatibility map, dualised. -/
theorem dual_compatibility_edge_part (G : CubicGraph V E) (f : GammaFlow G)
    (φ : Module.Dual F₂ (E → Gamma)) (ε : E → F₂) :
    φ (compatibilityMap G f (0, ε)) =
      ∑ e : E, coordinateFunctional φ e (ε e • f.val e) := by
  have hmap : compatibilityMap G f (0, ε) = fun e ↦ ε e • f.val e := by
    funext e
    show (0 : V → Gamma) (G.endAt e 0) + (0 : V → Gamma) (G.endAt e 1) + ε e • f.val e
      = ε e • f.val e
    simp
  rw [hmap]
  exact dual_apply_eq_sum_coordinates φ _

/-! ### The dual obstructions -/

variable {G : CubicGraph V E} {f : GammaFlow G} {φ : Module.Dual F₂ (E → Gamma)}

/-- **Edge obstruction.** A functional annihilating the range of the
compatibility map is orthogonal to the flow value in every edge coordinate.
Obtained by testing against the pure edge shift `ε = Pi.single e 1`. -/
theorem coordinateFunctional_flow_eq_zero
    (hφ : ∀ x, φ (compatibilityMap G f x) = 0) (e : E) :
    coordinateFunctional φ e (f.val e) = 0 := by
  have hcollapse : ∀ k ∈ (Finset.univ : Finset E), k ≠ e →
      coordinateFunctional φ k ((Pi.single e (1 : F₂) : E → F₂) k • f.val k) = 0 := by
    intro k _ hke
    rw [Pi.single_eq_of_ne hke, zero_smul, map_zero]
  have hz := hφ (0, Pi.single e 1)
  rw [dual_compatibility_edge_part,
    Finset.sum_eq_single_of_mem e (Finset.mem_univ e) hcollapse,
    Pi.single_eq_same, one_smul] at hz
  exact hz

/-- **Vertex obstruction.** A functional annihilating the range of the
compatibility map has its three coordinate functionals at every vertex summing
to zero. Obtained by testing against the pure vertex potential
`t = Pi.single v c`. -/
theorem sum_coordinateFunctional_edgeAt_eq_zero
    (hφ : ∀ x, φ (compatibilityMap G f x) = 0) (v : V) :
    ∑ i : Fin 3, coordinateFunctional φ (G.edgeAt v i) = 0 := by
  classical
  refine LinearMap.ext fun c => ?_
  have hcollapse : ∀ w ∈ (Finset.univ : Finset V), w ≠ v →
      (∑ i : Fin 3, coordinateFunctional φ (G.edgeAt w i)
        ((Pi.single v c : V → Gamma) w)) = 0 := by
    intro w _ hwv
    rw [Pi.single_eq_of_ne hwv]
    simp
  have hz := hφ (Pi.single v c, 0)
  rw [dual_compatibility_vertex_part,
    Finset.sum_eq_single_of_mem v (Finset.mem_univ v) hcollapse,
    Pi.single_eq_same] at hz
  simpa using hz

/-- **The local contribution of a vertex.** Combining the two obstructions with
`local_dual_identity`: at every vertex the "distinguished slot" value of `φ`
equals the number of nonzero coordinate functionals there, counted in `F₂`.

The left-hand side is exactly the contribution of `v` to
`φ (compatibilityRhs G f)`; the right-hand side is a quantity attached to edge
*ends*, which is why summing over vertices makes everything cancel. -/
theorem dual_local_slot_identity
    (hφ : ∀ x, φ (compatibilityMap G f x) = 0) (v : V) :
    coordinateFunctional φ (G.edgeAt v 1) (f.val (G.edgeAt v 0)) =
      ∑ i : Fin 3, functionalNonzero (coordinateFunctional φ (G.edgeAt v i)) := by
  set η : Fin 3 → Module.Dual F₂ Gamma := fun i => coordinateFunctional φ (G.edgeAt v i) with hη
  -- The three slot values at `v`, and their two structural properties.
  have hxy : f.val (G.edgeAt v 0) ≠ f.val (G.edgeAt v 1) :=
    f.val_edgeAt_ne v (show (0 : Fin 3) ≠ 1 by decide)
  have hz : f.val (G.edgeAt v 2) = f.val (G.edgeAt v 0) + f.val (G.edgeAt v 1) :=
    gamma_third_eq_add _ _ _ (f.sum_three v)
  -- The vertex obstruction, transported to coordinate vectors.
  have hcode : functionalCode (η 0) + functionalCode (η 1) + functionalCode (η 2) = 0 := by
    have hv := sum_coordinateFunctional_edgeAt_eq_zero hφ v
    rw [Fin.sum_univ_three] at hv
    funext k
    have hk := LinearMap.congr_fun hv (Pi.single k (1 : F₂))
    simpa [functionalCode, hη] using hk
  -- The edge obstruction at the three slots, transported to pairings.
  have hpair (i : Fin 3) : gammaPairing (functionalCode (η i)) (f.val (G.edgeAt v i)) = 0 := by
    rw [← functional_apply_eq_pairing]
    exact coordinateFunctional_flow_eq_zero hφ _
  have h2 : gammaPairing (functionalCode (η 2))
      (f.val (G.edgeAt v 0) + f.val (G.edgeAt v 1)) = 0 := by
    rw [← hz]; exact hpair 2
  rw [Fin.sum_univ_three, show coordinateFunctional φ (G.edgeAt v 1) = η 1 from rfl,
    functional_apply_eq_pairing]
  simp only [functionalNonzero]
  exact local_dual_identity _ _ _ _ _ (f.nowhereZero _) (f.nowhereZero _) hxy hcode
    (hpair 0) (hpair 1) h2

/-! ### Solvability of the compatibility system -/

/-- **The compatibility system is solvable.** Every cubic multigraph carrying a
nowhere-zero `Gamma`-flow admits a vertex potential and a system of edge shifts
reproducing the endpoint discrepancy of the local base points.

This is the manuscript's dual-obstruction calculation. The proof pairs an
arbitrary annihilating functional against the right-hand side, rewrites the
result as a sum over vertex slots (`dual_end_sum`), replaces each vertex's
contribution by its count of nonzero coordinate functionals
(`dual_local_slot_identity`), and observes that this count is attached to edge
*ends* — so every edge is counted twice and the total vanishes in `F₂`. -/
theorem compatibility_solvable (G : CubicGraph V E) (f : GammaFlow G) :
    compatibilityRhs G f ∈ LinearMap.range (compatibilityMap G f) := by
  refine mem_range_of_dual_obstructions_vanish _ _ fun φ hφ => ?_
  have hrhs : compatibilityRhs G f
      = fun e ↦ localBase G f (G.endAt e 0) e + localBase G f (G.endAt e 1) e := rfl
  rw [hrhs, dual_end_sum G φ (localBase G f)]
  -- Only the distinguished slot at each vertex carries a nonzero base point.
  have hslot (v : V) :
      (∑ i : Fin 3, coordinateFunctional φ (G.edgeAt v i) (localBase G f v (G.edgeAt v i)))
        = coordinateFunctional φ (G.edgeAt v 1) (f.val (G.edgeAt v 0)) := by
    have hinj := G.edgeAt_injective v
    have h0 : localBase G f v (G.edgeAt v 0) = 0 :=
      if_neg (hinj.ne (show (0 : Fin 3) ≠ 1 by decide))
    have h1 : localBase G f v (G.edgeAt v 1) = f.val (G.edgeAt v 0) := if_pos rfl
    have h2 : localBase G f v (G.edgeAt v 2) = 0 :=
      if_neg (hinj.ne (show (2 : Fin 3) ≠ 1 by decide))
    rw [Fin.sum_univ_three, h0, h1, h2, map_zero, map_zero, zero_add, add_zero]
  simp_rw [hslot, dual_local_slot_identity hφ]
  -- The remaining quantity lives on edge ends: every edge is counted twice.
  have hcount := G.sum_edgeEnds_eq_sum_vertexSlots
    (fun (e : E) (_ : Fin 2) => functionalNonzero (coordinateFunctional φ e))
  dsimp only at hcount
  rw [← hcount]
  refine Finset.sum_eq_zero fun e _ => ?_
  rw [Fin.sum_univ_two]
  exact f2_add_self _

/-! ### The labelling -/

/-- A choice of base point for every edge of a cubic multigraph such that, at
every vertex, the three affine pairs `{p e, p e + f e}` cover each index of
`Gamma` an even number of times.

This is the object the whole file exists to construct; combined with
`pairIndicator_card` (step 2b) it yields an exact indexed even *double* cover. -/
structure CubicLabeling (G : CubicGraph V E) (f : GammaFlow G) where
  /-- The base point attached to each edge. -/
  base : E → Gamma
  /-- Every index is covered an even number of times at every vertex. -/
  vertexParity : ∀ v s,
    ∑ i : Fin 3, pairIndicator (base (G.edgeAt v i)) (f.val (G.edgeAt v i)) s = 0

/-- Rearrangement in characteristic two: the compatibility equation, read as a
statement about the two endpoint proposals, says their sum is a multiple of the
flow value — exactly the hypothesis of `pairIndicator_eq_of_difference`. -/
theorem compatibility_rearrange :
    ∀ (a b c d h : Gamma) (ε : F₂),
      a + b + ε • h = c + d → a + c + (b + d) = ε • h := by
  intro a b c d h ε hab
  calc
    a + c + (b + d) = a + b + (c + d) := by ring
    _ = a + b + (a + b + ε • h) := by rw [← hab]
    _ = a + b + (a + b) + ε • h := by rw [add_assoc]
    _ = ε • h := by rw [gamma_add_self, zero_add]

section Construction

variable (G : CubicGraph V E) (f : GammaFlow G)

/-- A solution of the compatibility system, chosen once and for all. -/
noncomputable def compatibilitySolution : (V → Gamma) × (E → F₂) :=
  Classical.choose (LinearMap.mem_range.mp (compatibility_solvable G f))

theorem compatibilityMap_solution :
    compatibilityMap G f (compatibilitySolution G f) = compatibilityRhs G f :=
  Classical.choose_spec (LinearMap.mem_range.mp (compatibility_solvable G f))

/-- The vertex potential component of the chosen solution. -/
noncomputable def labelPotential : V → Gamma := (compatibilitySolution G f).1

/-- The per-edge shift component of the chosen solution. -/
noncomputable def labelDefect : E → F₂ := (compatibilitySolution G f).2

/-- The base point that end `j` of the edge `e` proposes for `e`: the vertex
potential there, corrected by the local base point. -/
noncomputable def endLabel (e : E) (j : Fin 2) : Gamma :=
  labelPotential G f (G.endAt e j) + localBase G f (G.endAt e j) e

/-- The base point finally attached to `e`: the proposal of its end `0`. -/
noncomputable def labelBase (e : E) : Gamma := endLabel G f e 0

/-- The two endpoint proposals for an edge differ by a multiple of its flow
value. This is the compatibility equation, rearranged. -/
theorem endLabel_add (e : E) :
    endLabel G f e 0 + endLabel G f e 1 = labelDefect G f e • f.val e := by
  refine compatibility_rearrange _ _ _ _ _ _ ?_
  have h := congrFun (compatibilityMap_solution G f) e
  exact h

/-- Case analysis on an end index, checked by the kernel. -/
private theorem fin_two_cases : ∀ j : Fin 2, j = 0 ∨ j = 1 := by decide

/-- Both endpoint proposals describe the *same* affine pair: shifting the base
point by a multiple of the direction does not move the pair. -/
theorem pairIndicator_endLabel (e : E) (j : Fin 2) :
    pairIndicator (endLabel G f e j) (f.val e) = pairIndicator (labelBase G f e) (f.val e) := by
  rcases fin_two_cases j with hj | hj <;> subst hj
  · rfl
  · refine pairIndicator_eq_of_difference _ _ _ (labelDefect G f e) (f.nowhereZero e) ?_
    rw [add_comm]
    exact endLabel_add G f e

/-- The pair attached to a slot at `v` is the one generated by the single vertex
potential value `labelPotential G f v` — which is precisely the configuration
`local_pair_parity` controls. -/
theorem pairIndicator_labelBase_slot (v : V) (i : Fin 3) :
    pairIndicator (labelBase G f (G.edgeAt v i)) (f.val (G.edgeAt v i)) =
      pairIndicator (labelPotential G f v + localBase G f v (G.edgeAt v i))
        (f.val (G.edgeAt v i)) := by
  have h := pairIndicator_endLabel G f (G.edgeAt v i) (G.incidence (v, i)).2
  have hrw : endLabel G f (G.edgeAt v i) (G.incidence (v, i)).2
      = labelPotential G f v + localBase G f v (G.edgeAt v i) := by
    simp [endLabel]
  rw [hrw] at h
  exact h.symm

/-- **The labelling exists.** Solvability of the compatibility system produces a
globally consistent choice of base points whose local multiplicities are even at
every vertex. -/
noncomputable def cubic_labeling : CubicLabeling G f where
  base := labelBase G f
  vertexParity := by
    intro v s
    have hxy : f.val (G.edgeAt v 0) ≠ f.val (G.edgeAt v 1) :=
      f.val_edgeAt_ne v (show (0 : Fin 3) ≠ 1 by decide)
    have hz : f.val (G.edgeAt v 2) = f.val (G.edgeAt v 0) + f.val (G.edgeAt v 1) :=
      gamma_third_eq_add _ _ _ (f.sum_three v)
    have hinj := G.edgeAt_injective v
    have h0 : localBase G f v (G.edgeAt v 0) = 0 :=
      if_neg (hinj.ne (show (0 : Fin 3) ≠ 1 by decide))
    have h1 : localBase G f v (G.edgeAt v 1) = f.val (G.edgeAt v 0) := if_pos rfl
    have h2 : localBase G f v (G.edgeAt v 2) = 0 :=
      if_neg (hinj.ne (show (2 : Fin 3) ≠ 1 by decide))
    rw [Fin.sum_univ_three]
    simp only [pairIndicator_labelBase_slot]
    rw [h0, h1, h2, add_zero, hz]
    exact local_pair_parity _ _ _ _ (f.nowhereZero _) (f.nowhereZero _) hxy

end Construction

end CycleDoubleCover
