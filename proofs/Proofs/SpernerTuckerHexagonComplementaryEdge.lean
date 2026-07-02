/-
# Tucker's lemma at n = 2: a complementary edge always exists on the hexagon disk

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's lemma and Borsuk–Ulam from
abstract door-counting").

## Where this sits

The `sperner-mathlib4-oq-02` program has, over sixteen iterations, machine-checked every
*structural* piece of the door-counting proof of Tucker's lemma:

* the abstract path-following / handshaking engines (`SpernerTuckerPathFollowing`,
  `SpernerTuckerDoorGraph`, `SpernerTuckerDoorIncidenceParity`, `SpernerTuckerInductiveTower`);
* the concrete n = 2 hexagon *door graph* is paths-and-cycles (`hdoor` + `hsimplex`,
  `SpernerTuckerHexagonFullDoorGraph`, `SpernerTuckerHexagonPseudomanifold`);
* the odd oriented *boundary seed* (`SpernerTuckerHexagonSignDegree`,
  `SpernerTuckerSignDegreeOneDim`).

Every one of those is a statement about the *machinery* — the door incidence bounds, the
degree sequence, the sign-degree seed — none of which is Tucker's actual **conclusion**.
Tucker's lemma itself asserts something simpler and stronger: for an antipodally-labelled
triangulation of `B²`, there is a **complementary edge** — an edge whose two endpoints carry
antipodal labels `{k, -k}`.  That conclusion had never been stated, let alone proved, for a
concrete n = 2 triangulation in this program.

## What this file proves (all by kernel `decide`, 0 axioms — no `native_decide`)

The standard hexagon + centre triangulation of `B²`: seven vertices — six boundary vertices
`v₀ … v₅` on `∂B² = S¹` (labelled antipodally, `v_{i+3} = -v_i`, so the boundary labels come
from three free labels `a, b, c` on `v₀, v₁, v₂`) and one interior centre vertex with a
**free** label `d`.  Twelve edges: six spokes `centre–vᵢ` and six boundary edges
`vᵢ–v_{i+1}` (indices cyclic in `Fin 6`).  Labels live in `{+1, +2, -1, -2}`, encoded as
`Fin 4` with `negL = ![2, 3, 0, 1]` the label negation; an edge is **complementary** when one
endpoint's label is the negation of the other's.

* `tucker_hexagon` — **Tucker's lemma for the hexagon disk.**  For *every* one of the
  `4⁴ = 256` antipodal labellings there is a complementary edge: either a spoke
  `centre–vᵢ` (`d = negL vᵢ`) or a boundary edge `vᵢ–v_{i+1}` (`v_{i+1} = negL vᵢ`).
* `boundary_ring_insufficient` — **the result is genuinely 2-dimensional.**  The boundary
  hexagon *ring alone* is not enough: there is an antipodal labelling of `v₀ … v₅` under which
  *no* boundary edge is complementary (24 of the 64 boundary labellings, in fact).  So Tucker
  here does **not** reduce to the already-verified 1-D (`S¹`) statement — the interior
  structure is doing real work.
* `interior_spoke_rescues` — and it is exactly the interior that does that work: whenever the
  boundary ring carries no complementary edge, a **spoke** to the centre is complementary, for
  *every* centre label `d`.  This is the concrete n = 1 → n = 2 step — the boundary (an n = 1
  Tucker instance on the arc) failing on the ring is repaired by the interior cone over it.

## Honest status

A **concrete verification**, not a dimension-free proof: it establishes Tucker's conclusion
for one specific (coarse) triangulation of `B²` by exhaustive kernel evaluation over its 256
labellings, and pins down that the interior is essential.  It does *not* prove Tucker for all
triangulations or all dimensions — that remains the abstract path-following program's job.
Its value is orthogonal to the engine files: it is the first time the **actual Tucker
conclusion** (a complementary edge, the object Borsuk–Ulam ultimately consumes) is
machine-checked at n = 2, and the first proof in the program that the n = 2 statement is not a
disguised n = 1 one.

Self-contained: imports Mathlib only.  0 sorries, 0 axioms (`propext` / `Quot.sound` only —
no `Classical.choice`, no `sorryAx`, no `Lean.ofReduceBool`).
-/
import Mathlib

namespace SpernerTuckerHexagonComplementaryEdge

/-! ## Labelling model (same encoding as `SpernerTuckerHexagon` / `…FullDoorGraph`) -/

/-- Label negation on `{+1, +2, -1, -2}` encoded as `Fin 4` (`0 ↦ +1, 1 ↦ +2, 2 ↦ -1,
3 ↦ -2`). -/
def negL : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/-- `negL` is an involution: negating twice is the identity. -/
theorem negL_involutive : ∀ x : Fin 4, negL (negL x) = x := by decide

/-- `negL` is fixed-point free: no label is its own antipode. -/
theorem negL_free : ∀ x : Fin 4, negL x ≠ x := by decide

/-- The six boundary labels from three free labels `a, b, c` on `v₀, v₁, v₂`, with the
antipodal boundary condition `v_{i+3} = -v_i` built in. -/
def V (a b c : Fin 4) : Fin 6 → Fin 4 := ![a, b, c, negL a, negL b, negL c]

/-- The boundary labelling is genuinely antipodal on `S¹`: `v_{i+3} = negL v_i`. -/
theorem V_antipodal : ∀ a b c : Fin 4, ∀ i : Fin 6, V a b c (i + 3) = negL (V a b c i) := by
  decide

/-! ## Complementary spokes and boundary edges

An edge is **complementary** when one endpoint's label is the antipode of the other's.  The
twelve edges of the hexagon + centre triangulation split into six spokes `centre–vᵢ` (label
pair `(d, vᵢ)`) and six boundary edges `vᵢ–v_{i+1}` (label pair `(vᵢ, v_{i+1})`, cyclic). -/

/-- Some **spoke** `centre–vᵢ` is complementary: the centre label `d` is the antipode of some
boundary label. -/
def spokeCompl (a b c d : Fin 4) : Prop := ∃ i : Fin 6, d = negL (V a b c i)

/-- Some **boundary edge** `vᵢ–v_{i+1}` (cyclic) is complementary. -/
def boundaryCompl (a b c : Fin 4) : Prop := ∃ i : Fin 6, V a b c (i + 1) = negL (V a b c i)

instance : ∀ a b c d, Decidable (spokeCompl a b c d) := fun _ _ _ _ => by
  unfold spokeCompl; infer_instance
instance : ∀ a b c, Decidable (boundaryCompl a b c) := fun _ _ _ => by
  unfold boundaryCompl; infer_instance

/-! ## Tucker's lemma for the hexagon disk -/

/-- **Tucker's lemma, hexagon disk.**  For every antipodal labelling `(a, b, c, d)` the
hexagon + centre triangulation of `B²` has a complementary edge — either a complementary
spoke `centre–vᵢ` or a complementary boundary edge `vᵢ–v_{i+1}`.  This is the conclusion of
Tucker's lemma at n = 2.  Verified by kernel `decide` over all `4⁴ = 256` labellings. -/
theorem tucker_hexagon (a b c d : Fin 4) : spokeCompl a b c d ∨ boundaryCompl a b c := by
  revert a b c d; decide

/-- **Existence of a complementary edge**, unpacked to the two endpoint labels: for every
labelling there are two adjacent vertices in the triangulation whose labels are antipodal. -/
theorem exists_complementary_edge (a b c d : Fin 4) :
    (∃ i : Fin 6, d = negL (V a b c i)) ∨ (∃ i : Fin 6, V a b c (i + 1) = negL (V a b c i)) :=
  tucker_hexagon a b c d

/-! ## The result is genuinely 2-dimensional

Tucker on the hexagon disk is not a disguised statement about its boundary `S¹`: the boundary
hexagon ring alone can fail to have a complementary edge, and it is precisely the interior
spoke to the centre that then supplies one. -/

/-- **The boundary ring alone is insufficient.**  There is an antipodal labelling of the six
boundary vertices under which *no* boundary edge is complementary.  Hence Tucker on the
hexagon disk does not reduce to the 1-D (`S¹`) statement — the interior is essential. -/
theorem boundary_ring_insufficient : ∃ a b c : Fin 4, ¬ boundaryCompl a b c := by decide

/-- **The interior spoke rescues the boundary.**  Whenever the boundary ring carries no
complementary edge, some spoke `centre–vᵢ` is complementary — for *every* centre label `d`.
This is the concrete n = 1 → n = 2 step: the boundary (an n = 1 Tucker instance on the
antipodal ring) failing is repaired by the interior cone over it, so a complementary edge
exists regardless of how the centre is labelled. -/
theorem interior_spoke_rescues (a b c d : Fin 4) (h : ¬ boundaryCompl a b c) :
    spokeCompl a b c d := by
  revert a b c d; decide

#print axioms tucker_hexagon
#print axioms exists_complementary_edge
#print axioms boundary_ring_insufficient
#print axioms interior_spoke_rescues

end SpernerTuckerHexagonComplementaryEdge
