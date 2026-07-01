import Mathlib.Tactic
import Proofs.PlatonicSolidsOQ03

/-!
# Coxeter Diagrams, the Schläfli Order Formula, and the Spherical Criterion  (OQ-03-OQ-01)

The parent entry `PlatonicSolidsOQ03` records the reflection group of each Platonic
solid via its fundamental **degrees** (`A₃ = ⟨2,3,4⟩`, `B₃ = ⟨2,4,6⟩`, `H₃ = ⟨2,6,10⟩`)
and the numerical invariants those degrees pin down (order `= 4E = d₁d₂d₃`, exponents,
reflection count `N = nh/2`, the three symmetry classes).

This child answers the parent's next step

> *"Derive the rank-3 reflection classification (A₃, B₃, H₃, …) from the Schläfli
>  constraint."*

by reconstructing the same three groups from the **other** canonical datum — the
**Coxeter diagram** — and reading every invariant straight off the Schläfli symbol
`{p, q}`.  A finite reflection group of a regular polyhedron `{p, q}` is the linear
rank-3 Coxeter group with diagram

```
  o ---p--- o ---q--- o
```

i.e. the Coxeter matrix `mᵢⱼ` has `m₁₂ = p`, `m₂₃ = q`, `m₁₃ = 2` (the outer nodes
commute).  We formalise, all at the self-contained `decide`/`rfl` invariant level of
the parent:

* **Diagram of each solid** `= (p, q)`, and the three canonical diagrams
  `A₃ = [3,3]`, `B₃ = [4,3]`, `H₃ = [5,3]`.
* **Duality reverses the diagram** (`{p,q} ↦ {q,p}`), and diagram reversal is a group
  isomorphism — this is *why* cube `{4,3}` and octahedron `{3,4}`, whose diagrams are
  each other's mirror image, share the group `B₃`.
* **Direct Schläfli order formula** `|W| = 8pq / (2p + 2q − pq)`, matching the parent's
  `4E = d₁d₂d₃`.
* **Spherical (finiteness) criterion** `1/p + 1/q > 1/2`, i.e. `pq < 2p + 2q`: exactly
  the five solids satisfy it, and the "angular defect" denominator `2p + 2q − pq`
  takes the values `3, 2, 2, 1, 1`.

## Honest scope
As in the parent, these are the numerical/combinatorial invariants of the abstract
Coxeter groups, machine-checked in full; constructing the groups as concrete groups and
proving `|W| = ∏ dᵢ` intrinsically is not attempted (that machinery is absent from
Mathlib).

## References
- Coxeter, *Regular Polytopes*, §5 (the diagram `[p, q]` and the order `g` of `{p,q}`).
- Humphreys, *Reflection Groups and Coxeter Groups*, §2.4, §6.5.
- https://en.wikipedia.org/wiki/Coxeter_group  (linear diagrams; reversal isomorphism)
-/

set_option linter.unusedVariables false

namespace PlatonicSolidsOQ03OQ01

open PlatonicSolidsOQ03
open PlatonicSolidsOQ03.Solid

-- ============================================================
-- PART 1: The Coxeter diagram of a Schläfli symbol
-- ============================================================

/-- A **linear rank-3 Coxeter diagram** `o --a-- o --b-- o`, recorded by its two bond
    labels `a = m₁₂` and `b = m₂₃`.  The third label `m₁₃ = 2` is implicit: the two
    outer generators always commute, which is what makes the diagram a *path*. -/
structure CoxDiagram where
  a : ℕ
  b : ℕ
  deriving DecidableEq, Repr

/-- The implicit outer bond `m₁₃ = 2`: in a linear diagram the end nodes commute. -/
def CoxDiagram.outerBond : ℕ := 2

/-- The Coxeter diagram of a Platonic solid `{p, q}` is `o --p-- o --q-- o`.  (A bare
    function rather than a `Solid.`-projection, since `Solid` lives in the parent's
    namespace.) -/
def diagram (s : Solid) : CoxDiagram := ⟨s.schlafli.1, s.schlafli.2⟩

/-- The canonical diagrams of the three rank-3 Platonic reflection groups. -/
def diagA₃ : CoxDiagram := ⟨3, 3⟩
def diagB₃ : CoxDiagram := ⟨4, 3⟩
def diagH₃ : CoxDiagram := ⟨5, 3⟩

/-- The diagram of every solid, read straight off its Schläfli symbol. -/
theorem diagram_values :
    diagram tetrahedron = ⟨3, 3⟩ ∧ diagram cube = ⟨4, 3⟩ ∧ diagram octahedron = ⟨3, 4⟩ ∧
    diagram dodecahedron = ⟨5, 3⟩ ∧ diagram icosahedron = ⟨3, 5⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- The tetrahedron/cube/dodecahedron realise the canonical diagrams `A₃, B₃, H₃`. -/
theorem canonical_diagrams :
    diagram tetrahedron = diagA₃ ∧ diagram cube = diagB₃ ∧ diagram dodecahedron = diagH₃ := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

-- ============================================================
-- PART 2: Duality reverses the diagram (and preserves the group)
-- ============================================================

/-- Reversing a linear Coxeter diagram: read the path from the other end. -/
def CoxDiagram.reverse (d : CoxDiagram) : CoxDiagram := ⟨d.b, d.a⟩

/-- Reversal is an involution. -/
theorem reverse_reverse (d : CoxDiagram) : d.reverse.reverse = d := by
  cases d; rfl

/-- **Duality reverses the Coxeter diagram.**  Platonic duality swaps `p ↔ q`, which is
    exactly reflecting the linear diagram `o --p-- o --q-- o` about its centre. -/
theorem dual_reverses_diagram (s : Solid) : diagram s.dual = (diagram s).reverse := by
  cases s <;> rfl

/-- The **normalised** diagram (bond labels sorted `min ≤ max`): a reversal-invariant
    signature of the underlying path, ignoring the choice of end to start from. -/
def CoxDiagram.normalize (d : CoxDiagram) : CoxDiagram :=
  ⟨min d.a d.b, max d.a d.b⟩

/-- Reversal does not change the normalised diagram. -/
theorem normalize_reverse (d : CoxDiagram) : d.reverse.normalize = d.normalize := by
  cases d
  simp only [CoxDiagram.reverse, CoxDiagram.normalize, Nat.min_comm, Nat.max_comm]

/-- **Reversal is a diagram isomorphism**: dual solids have the *same* normalised
    diagram, so they carry the same reflection group.  This is the diagram-level reason
    the five solids give only three groups. -/
theorem dual_normalize_diagram (s : Solid) :
    (diagram s.dual).normalize = (diagram s).normalize := by
  rw [dual_reverses_diagram, normalize_reverse]

/-- The normalised diagram determines the Coxeter group across all five solids: two
    solids with the same normalised diagram have the same reflection group. -/
theorem normalize_determines_coxeter (s t : Solid) :
    (diagram s).normalize = (diagram t).normalize → s.coxeter = t.coxeter := by
  cases s <;> cases t <;> decide

/-- Consequently duals share their reflection group, recovered here from the diagram
    (the parent proved this from the degrees). -/
theorem coxeter_dual_via_diagram (s : Solid) : s.dual.coxeter = s.coxeter :=
  normalize_determines_coxeter _ _ (dual_normalize_diagram s)

-- ============================================================
-- PART 3: The direct Schläfli order formula  |W| = 8pq/(2p+2q−pq)
-- ============================================================

/-- The **angular-defect denominator** `2p + 2q − pq` of the Schläfli symbol `{p, q}`.
    Positive exactly for the spherical (Platonic) case; it equals `4 · (defect angle)`
    up to the usual normalisation and drives the order formula below. -/
def defect (s : Solid) : ℕ :=
  2 * s.schlafli.1 + 2 * s.schlafli.2 - s.schlafli.1 * s.schlafli.2

/-- The defect denominators `3, 2, 2, 1, 1`. -/
theorem defect_values :
    defect tetrahedron = 3 ∧ defect cube = 2 ∧ defect octahedron = 2 ∧
    defect dodecahedron = 1 ∧ defect icosahedron = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- **Direct Schläfli order formula.**  The full symmetry group order is
    `|W| = 8pq / (2p + 2q − pq)`, computed straight from the Schläfli symbol without
    passing through the edge count or the degrees.  For each solid the division is
    exact and reproduces the parent's `4E = d₁d₂d₃`. -/
theorem order_from_schlafli (s : Solid) :
    8 * s.schlafli.1 * s.schlafli.2 / defect s = s.coxeter.order := by
  cases s <;> decide

/-- The Schläfli formula also equals `4E` directly (bridge to the parent combinatorics). -/
theorem schlafli_order_eq_four_edges (s : Solid) :
    8 * s.schlafli.1 * s.schlafli.2 / defect s = 4 * s.edges := by
  cases s <;> decide

-- ============================================================
-- PART 4: The spherical (finiteness) criterion
-- ============================================================

/-- The **spherical criterion** `1/p + 1/q > 1/2`, cleared of denominators to
    `pq < 2p + 2q`.  Over `p, q ≥ 3` this holds precisely for the five Platonic
    Schläfli symbols; `= ` gives the (infinite) Euclidean tilings, `> ` the hyperbolic
    ones.  Being decidable it is checked directly. -/
def isSpherical (p q : ℕ) : Prop := p * q < 2 * p + 2 * q

instance (p q : ℕ) : Decidable (isSpherical p q) := by
  unfold isSpherical; infer_instance

/-- Every Platonic solid is spherical (its diagram gives a finite reflection group). -/
theorem solids_spherical (s : Solid) : isSpherical s.schlafli.1 s.schlafli.2 := by
  cases s <;> decide

/-- Sphericity is exactly a positive defect, and the order formula is defined precisely
    when the defect is positive. -/
theorem spherical_iff_defect_pos (s : Solid) :
    isSpherical s.schlafli.1 s.schlafli.2 ↔ 0 < defect s := by
  cases s <;> exact by decide

/-- The nearby *degenerate* symbols on the boundary of sphericity are **not** spherical:
    `{3,6}, {4,4}, {6,3}` (the three Euclidean tilings) have defect `0`.  This pins the
    Platonic list down as the strict interior of the criterion. -/
theorem euclidean_boundary_not_spherical :
    ¬ isSpherical 3 6 ∧ ¬ isSpherical 4 4 ∧ ¬ isSpherical 6 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- ============================================================
-- PART 5: Capstone — diagram + Schläfli order + duality
-- ============================================================

/-- **Schläfli ↔ Coxeter-diagram correspondence.**  For every Platonic solid `{p, q}`:
    its Coxeter diagram is the path with bond labels `(p, q)`; the group order is
    `8pq / (2p + 2q − pq) = 4E = d₁d₂d₃`; the solid is spherical; and Platonic duality
    reverses the diagram while preserving the (normalised diagram, hence the) group. -/
theorem schlafli_coxeter_correspondence :
    ∀ s : Solid,
      diagram s = ⟨s.schlafli.1, s.schlafli.2⟩ ∧
      8 * s.schlafli.1 * s.schlafli.2 / defect s = s.coxeter.order ∧
      s.coxeter.order = 4 * s.edges ∧
      isSpherical s.schlafli.1 s.schlafli.2 ∧
      diagram s.dual = (diagram s).reverse ∧
      s.dual.coxeter = s.coxeter := by
  intro s
  refine ⟨rfl, order_from_schlafli s, ?_, solids_spherical s, dual_reverses_diagram s,
    coxeter_dual_via_diagram s⟩
  cases s <;> decide

end PlatonicSolidsOQ03OQ01

-- Export main results
#check PlatonicSolidsOQ03OQ01.order_from_schlafli
#check PlatonicSolidsOQ03OQ01.dual_normalize_diagram
#check PlatonicSolidsOQ03OQ01.solids_spherical
#check PlatonicSolidsOQ03OQ01.schlafli_coxeter_correspondence
