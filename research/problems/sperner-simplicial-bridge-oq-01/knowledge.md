# Knowledge — sperner-simplicial-bridge-oq-01

## S1 OBSERVE (2026-05-12)

### Mathematical analysis: why stratification works

The parent file's door-counting argument
(`Sperner.exists_panchromatic` in `Proofs/SpernerMathlib.lean`,
invoked via the bridge file's `exists_panchromatic`) proves the
following combinatorial parity statement:

For a pure pseudomanifold $K$ of dimension $d$ with a Sperner
coloring $c : E \to \mathrm{Fin}(d+1)$:
- *Doors* are pairs $(s, k)$ where $s$ is a top-cell and $k$ is a
  vertex index such that the codim-1 face `faceOf s _ k` has a Sperner
  coloring (i.e., all but one color appear on the $d$-vertex face).
- A *boundary door* is a door with `adjFn s _ k = none` (no opposite
  cell across the face).
- The argument: each non-boundary door $(s, k)$ is paired with its
  $(\mathrm{adjFn}\,s\,k, k')$ partner. So the parity of non-boundary
  doors is even, hence the parity of *all* doors equals the parity of
  *boundary* doors. If the latter is odd, the parity of "doors per
  cell" is non-uniform, forcing some cell to have an odd door count
  — which is exactly the panchromatic condition.

**Key observation**: every door is *dimension-pure*. A door at level
$d$ involves a top-cell of cardinality $d+1$ and a face of cardinality
$d$. If we have cells of mixed dimensions, the door-relations
$(\mathrm{adjFn} \text{ on } K)$ are partitioned into disjoint
subsets per stratum: a door at level $d$ pairs only with another
door at level $d$ (an adjacent $d$-cell via the same face). Doors at
level $d \ne d'$ involve different face-cardinalities and cannot
pair.

So the parity argument runs *independently* on each stratum. For
each $d$ with non-empty `topCellsOfDim K d`, the parity of doors in
that stratum determines panchromaticity *within that stratum*. The
mixed-pseudomanifold theorem is therefore a finite disjunction over
$d$:
$$\bigl( \exists d, \text{stratum } d \text{ has odd boundary count} \bigr) \implies \exists d, \exists s \in K_d^{\mathrm{top}}, \; \mathrm{Panchromatic}(s).$$

This is a strict generalization of the parent theorem, recovered by
restricting to a single dimension.

### Edge cases

1. **Empty strata.** If `topCellsOfDim K d = ∅` for some $d$, the
   pseudomanifold condition `((topCellsOfDim K d).filter ...).card ≤
   2` is vacuously satisfied (filter of empty = empty, card 0 ≤ 2).
   The panchromaticity claim "exists $s$ in stratum $d$" is vacuously
   false; the disjunction over $d$ skips empty strata.

2. **Constant-dimension complexes.** Pure pseudomanifolds are the
   $K$ where exactly one stratum is non-empty. Then the theorem
   reduces to the parent's `exists_panchromatic` on that stratum.

3. **Coloring mismatch.** The parent's `exists_panchromatic` requires
   `c : E → Fin (d + 1)`, where $d$ is the (uniform) dimension. In
   the mixed case, different strata may want colorings into different
   `Fin n`. The cleanest formulation has the user fix a target dim
   $d$ at the outset and only invoke the theorem for that dim. A
   "universal" coloring `c : E → Nat` followed by per-stratum
   restriction to `Fin (d+1)` is possible but adds boilerplate.

4. **Boundary-count hypothesis.** The parent's `hbdry` clause is
   `Odd (Finset.univ.filter (fun p : { s // s ∈ topCells } × Fin (d+1) =>
       Sperner.IsDoor ... ∧ adjFn ... = none)).card`. For the mixed
   version, this becomes per-stratum: `∀ d, hbdry_d` where each
   `hbdry_d` is the parent's clause restricted to
   `topCellsOfDim K d`. The user fixes which $d$ they want a
   panchromatic cell from, and supplies only that stratum's `hbdry`.

5. **Decidability/finiteness.** `K.filter` is well-defined on finite
   sets without any new instance arguments; `topCellsOfDim` inherits
   `DecidableEq E` from the parent's setting.

### Mathlib API survey (v4.26.0)

#### Stratification machinery

- `Finset.filter : (α → Prop) → [DecidablePred] → Finset α → Finset α`
  with `Finset.mem_filter : a ∈ s.filter p ↔ a ∈ s ∧ p a`.
- `Finset.filter_subset : s.filter p ⊆ s`.
- `Finset.card_filter_le : (s.filter p).card ≤ s.card`.

All these are stock Mathlib and require no special imports beyond
what `Proofs.SpernerSimplicialBridge` already brings.

#### Card-filter inequalities

For the `MixedPseudomanifold.of_pure` sanity check (S2):
- `Finset.filter_filter` (composing two filters).
- `Finset.filter_eq_self` when the predicate is universal on the
  parent set.

#### Disjunction over dimensions

S3's main theorem produces an existence claim "exists $s$ in
`topCellsOfDim K d` ..." where $d$ is fixed by the hypothesis. No
disjunction needed in Lean — the theorem signature fixes $d$.

### Prior-art references

- **De Longueville (2013)**, *A Course in Topological Combinatorics*,
  Springer. Chapter 2 develops Sperner's lemma on non-pure
  simplicial complexes via stratification; the door-pairing argument
  is dimension-graded.
- **Henle (1979)**, *A Combinatorial Introduction to Topology*. The
  classical "barycentric subdivision" framework for Sperner on
  triangulated manifolds with boundary.
- **Mathlib `Geometry.SimplicialComplex.facets`**: defines
  `K.facets = {s ∈ K.faces | ∀ t ∈ K.faces, s ⊆ t → s = t}` for a
  Mathlib simplicial complex. Our `topCellsOfDim` is the
  dimension-grading of this when restricted to a `Finset (Finset E)`.

### S2 risk register

1. **`topCellsOfDim K d ⊆ K` is *not* automatically a hypothesis-free
   subgoal.** The parent's `exists_panchromatic` requires
   `topCells : Finset (Finset E)`, and using `topCellsOfDim K d` is
   fine because `Finset.filter` returns a `Finset`. The
   inclusion-into-K is via `Finset.mem_filter.mp`.

2. **`hcard : ∀ s ∈ topCellsOfDim K d, s.card = d + 1` is immediate.**
   `s ∈ K.filter (· .card = d + 1)` gives `s.card = d + 1` via
   `Finset.mem_filter.mp`'s second component.

3. **`hpseudo` for the d-stratum follows from `hpseudo : ∀ d', ∀ f,
   f.card = d' → ...` by instantiating `d' := d`.** No extra work.

4. **The boundary count is dimension-specific.** The user must
   supply `hbdry_d : Odd ...` where the door predicate refers to
   `topCellsOfDim K d` and `Fin (d + 1)`. S3's theorem signature
   makes this explicit.

5. **No `omega` traps anticipated.** `omega` handles `Nat`
   arithmetic on `card` and `d`; no decidable/non-decidable
   inequalities.

6. **No `noncomputable` headaches.** `topCellsOfDim` is
   `noncomputable def` (matches parent's pattern with
   `vertexEnum`); `Finset.filter` returns a `Finset` regardless of
   decidability.

7. **Build cost low**: ~10 min docker build because the parent
   `Proofs.SpernerSimplicialBridge` is the only direct dependency
   (Mathlib cache covers the rest).

### S2 implementation sketch

The full S2 file (~80 LOC):

```lean
/- Companion to SpernerSimplicialBridge: extension to non-pure
   simplicial complexes via dimension stratification. -/
import Proofs.SpernerSimplicialBridge

namespace Sperner.SimplicialComplex

open Finset

variable {E : Type} [DecidableEq E] [LinearOrder E]

/-- The dimension-d stratum of a (possibly non-pure) simplicial
    complex K, viewed as a Finset of facets. -/
noncomputable def topCellsOfDim (K : Finset (Finset E)) (d : Nat) :
    Finset (Finset E) :=
  K.filter (fun s => s.card = d + 1)

@[simp]
lemma mem_topCellsOfDim
    (K : Finset (Finset E)) (d : Nat) (s : Finset E) :
    s ∈ topCellsOfDim K d ↔ s ∈ K ∧ s.card = d + 1 :=
  Finset.mem_filter

lemma topCellsOfDim_subset (K : Finset (Finset E)) (d : Nat) :
    topCellsOfDim K d ⊆ K := Finset.filter_subset _ _

lemma card_eq_of_mem_topCellsOfDim
    (K : Finset (Finset E)) (d : Nat) (s : Finset E)
    (hs : s ∈ topCellsOfDim K d) : s.card = d + 1 :=
  (Finset.mem_filter.mp hs).2

/-- Mixed pseudomanifold: each dimension's stratum is independently a
    pseudomanifold. -/
def MixedPseudomanifold (K : Finset (Finset E)) : Prop :=
  ∀ d : Nat, ∀ f : Finset E, f.card = d →
    ((topCellsOfDim K d).filter (fun s => f ⊆ s)).card ≤ 2

/-- A pure pseudomanifold is a mixed pseudomanifold. -/
theorem MixedPseudomanifold.of_pure
    {d : Nat} (topCells : Finset (Finset E))
    (hcard : ∀ s ∈ topCells, s.card = d + 1)
    (hpseudo : ∀ f : Finset E, f.card = d →
      (topCells.filter (fun s => f ⊆ s)).card ≤ 2) :
    MixedPseudomanifold topCells := by
  intro d' f hf
  by_cases hd' : d' = d
  · subst hd'
    -- For dim d: topCellsOfDim topCells d = topCells, since all cells
    -- in topCells have cardinality d+1 by hcard.
    have heq : topCellsOfDim topCells d = topCells := by
      apply Finset.filter_eq_self.mpr
      intro s hs
      exact hcard s hs
    rw [heq]
    exact hpseudo f hf
  · -- For dim d' ≠ d: no cells of cardinality d'+1 in topCells.
    have hempty : topCellsOfDim topCells d' = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro s hs
      have h1 : s ∈ topCells := topCellsOfDim_subset _ _ hs
      have h2 : s.card = d' + 1 := card_eq_of_mem_topCellsOfDim _ _ _ hs
      have h3 : s.card = d + 1 := hcard s h1
      omega
    rw [hempty, Finset.filter_empty]
    simp

end Sperner.SimplicialComplex
```

### Next-session expectations (S3)

- **Output**: ~50-80 LOC delta. Statement and proof of
  `sperner_mixed_panchromatic` as a 5-line application of
  `exists_panchromatic` to the chosen stratum.
- **Sorry count**: 0 new sorries.
- **Build cost**: ~10 min docker build.
- **PR scope**: single ACT PR adding the main mixed-panchromatic
  theorem; S4 gallery integration in a follow-on PR.
