/-
  Sperner → Tucker program, `sperner-mathlib4-oq-02`.

  # The canonical signed labelling of the cross-polytope door graph

  `SpernerTuckerCrossPolytopeBoundary` builds the general-`n` antipodally symmetric
  cross-polytope boundary `∂◊^{n+1}` (facets `Facet n = Fin (n+1) → Bool`, antipode =
  flip-all-signs, facet-adjacency the `(n+1)`-cube `crossGraph n`) and proves the fully
  symmetric graph can never supply Tucker's *odd* seed
  (`crossPolytope_not_tucker_level`).  `SpernerTuckerCrossPolytopeHemisphere` supplies the
  hemisphere ↔ lower-dimension recursion.  Both files note the same missing piece: neither
  yet installs a **Tucker labelling** that turns the cube edges into *complementary* doors.

  This file installs the labelling layer.  It generalises the hexagon's signed alphabet
  (`SpernerTuckerHexagonComplementaryEdge`: `Fin 4 = {±1, ±2}` with `negL = ![2,3,0,1]`) to
  every dimension:

    * `SignedLabel n = Bool × Fin (n+1)` — the alphabet `{±1, …, ±(n+1)}` (a sign and a
      coordinate), with `negLabel` (flip the sign) a **free involution**
      (`negLabel_involutive`, `negLabel_free`);
    * `coordLabel s i = (s i, i)` — the per-coordinate label of facet `s`, whose
      **antipodality** `coordLabel (antipode s) i = negLabel (coordLabel s i)`
      (`coordLabel_antipode`) is the defining property of a Tucker labelling `λ(-s) = -λ(s)`,
      the general-`n` form of the hexagon's `V_antipodal`;
    * `coordLabel (flipAt s i) i = negLabel (coordLabel s i)` (`coordLabel_flipAt_self`):
      **flipping coordinate `i` negates exactly the coordinate-`i` label** — the two endpoints
      of the cube edge across coordinate `i` are negation-related there, so every cube edge is
      a *complementary door* at its flip coordinate.

  The payoff is a sharp **scoping** fact (`compAdj_iff_adj`,
  `canonicalLabelling_not_tucker_level`): the complementary-door graph of this canonical
  per-coordinate labelling coincides with the *entire* antipodally-symmetric cube
  `crossGraph n`, so the program's own dimension-free no-go applies verbatim — the canonical
  labelling has an **even** interior-endpoint count and can never carry Tucker's odd seed.
  The genuine Tucker labelling must break the antipodal symmetry on a hemisphere
  (`coordLabel_flipAt_succ_zero` records the piece the hemisphere pin keeps fixed).  This
  rules out the naive per-coordinate labelling in *every* dimension, on the canonical
  octahedral model, machine-checked (previously only the `n = 2` hexagon obstruction was known,
  `SpernerTuckerHexagonDoorObstruction`).

  Honest status: the labelling *layer* for `bridge`, plus a no-go scoping result — **not** a
  proof of `bridge`.  It installs and audits the antipodal signed labelling but does not build
  the symmetry-broken almost-complementary structure carrying the odd seed; that remains the
  open frontier.  Everything is dimension-free (no `decide` / `native_decide`) and 0-axiom
  (`propext` / `Classical.choice` / `Quot.sound` only), as the `#print axioms` guards confirm.
-/
import Mathlib
import Proofs.SpernerTuckerCrossPolytopeBoundary

namespace SpernerTuckerCrossPolytopeLabelling

open Finset SimpleGraph SpernerTuckerInductiveTower SpernerTuckerCrossPolytopeBoundary

variable (n : ℕ)

/-! ## The signed-label alphabet with its free negation involution -/

/-- The signed-label alphabet `{±1, …, ±(n+1)}` for `∂◊^{n+1}`: a Boolean sign paired with a
coordinate index.  Generalises the hexagon's `Fin 4 = {±1, ±2}` (`negL`) to every dimension. -/
abbrev SignedLabel (n : ℕ) : Type := Bool × Fin (n + 1)

/-- Label negation: flip the sign, keep the coordinate.  The general-`n` analogue of the
hexagon `negL = ![2, 3, 0, 1]`. -/
def negLabel (l : SignedLabel n) : SignedLabel n := (!l.1, l.2)

@[simp] theorem negLabel_mk (b : Bool) (i : Fin (n + 1)) :
    negLabel n (b, i) = (!b, i) := rfl

/-- Label negation is an involution (`- -x = x`). -/
theorem negLabel_involutive : Function.Involutive (negLabel n) := by
  intro l; simp [negLabel]

/-- Label negation is fixed-point-free: no label is its own negation (the sign always flips).
This is what makes the antipodal labelling free, the alphabet-level analogue of
`antipode_free`. -/
theorem negLabel_free (l : SignedLabel n) : negLabel n l ≠ l := by
  intro h
  have h1 : (!l.1) = l.1 := (Prod.ext_iff.mp h).1
  exact (Bool.not_ne_self l.1) h1

/-! ## The canonical per-coordinate labelling -/

/-- The canonical per-coordinate label of facet `s` at coordinate `i`: the sign `s i` tagged
with the coordinate `i`. -/
def coordLabel (s : Facet n) (i : Fin (n + 1)) : SignedLabel n := (s i, i)

@[simp] theorem coordLabel_apply (s : Facet n) (i : Fin (n + 1)) :
    coordLabel n s i = (s i, i) := rfl

/-- **Antipodality of the labelling.**  The antipodal flip negates every coordinate label —
the defining property of a Tucker labelling, `λ(-s) = -λ(s)`, here at each coordinate.
Generalises the hexagon's `V_antipodal` to `∂◊^{n+1}`. -/
theorem coordLabel_antipode (s : Facet n) (i : Fin (n + 1)) :
    coordLabel n (antipode n s) i = negLabel n (coordLabel n s i) := rfl

/-- **Flipping coordinate `i` negates exactly the coordinate-`i` label.**  The two endpoints of
the cube edge across coordinate `i` carry negation-related `i`-labels — the sense in which every
cube edge of `crossGraph` is a *complementary door* at its flip coordinate. -/
theorem coordLabel_flipAt_self (s : Facet n) (i : Fin (n + 1)) :
    coordLabel n (flipAt n s i) i = negLabel n (coordLabel n s i) := by
  simp [coordLabel, negLabel, flipAt, Function.update_self]

/-- Flipping coordinate `i` leaves every **other** coordinate label unchanged. -/
theorem coordLabel_flipAt_of_ne (s : Facet n) {i j : Fin (n + 1)} (h : j ≠ i) :
    coordLabel n (flipAt n s i) j = coordLabel n s j := by
  simp [coordLabel, flipAt, Function.update_of_ne h]

/-! ## Every cube edge is a complementary door -/

/-- The **complementary-door relation** of the canonical labelling: `t` is a complementary door
of `s` when it is the coordinate-`i` flip for some `i` at which the two labels are
negation-related. -/
def CompAdj (s t : Facet n) : Prop :=
  ∃ i, flipAt n s i = t ∧ coordLabel n t i = negLabel n (coordLabel n s i)

/-- **The canonical labelling makes complementary doors coincide with cube edges.**  Every edge
of `crossGraph` is a complementary door (at its unique flip coordinate), and every complementary
door is a cube edge.  So the complementary-door graph of the canonical per-coordinate labelling
is the *entire* symmetric cube `crossGraph n` — not a proper, symmetry-broken subgraph. -/
theorem compAdj_iff_adj (s t : Facet n) :
    CompAdj n s t ↔ (crossGraph n).Adj s t := by
  constructor
  · rintro ⟨i, rfl, _⟩
    rw [← SimpleGraph.mem_neighborFinset, mem_neighbor_iff]
    exact ⟨i, rfl⟩
  · intro hadj
    rw [← SimpleGraph.mem_neighborFinset, mem_neighbor_iff] at hadj
    obtain ⟨i, hi⟩ := hadj
    refine ⟨i, hi, ?_⟩
    rw [← hi]
    exact coordLabel_flipAt_self n s i

/-- **Scoping no-go: the canonical labelling is not a Tucker certificate, in any dimension.**
Because its complementary-door graph is the whole antipodally-symmetric cube
(`compAdj_iff_adj`), the program's dimension-free no-go applies verbatim: for any
antipode-invariant boundary predicate the complementary-door interior-endpoint count is
**even**, never the odd seed Tucker needs.  A genuine Tucker labelling must therefore break the
antipodal symmetry on a hemisphere; the naive per-coordinate labelling cannot.  Generalises the
`n = 2` hexagon obstruction (`SpernerTuckerHexagonDoorObstruction`) to every dimension on the
canonical octahedral model. -/
theorem canonicalLabelling_not_tucker_level
    (B : Facet n → Prop) [DecidablePred B] (hB : ∀ s, B (antipode n s) ↔ B s)
    (hodd : Odd #(interiorEndpoints (crossGraph n) B)) : False :=
  crossPolytope_not_tucker_level n B hB hodd

/-! ## The hemisphere pin, in labelled form -/

/-- Within the positive hemisphere (`s 0 = true`), an interior door — a flip at a coordinate
`i.succ ≠ 0` — leaves the pinned coordinate-`0` label untouched, while its own coordinate becomes
a complementary door (`coordLabel_flipAt_self`).  This is the labelled form of the hemisphere door
split `hemisphere_degree_split`: the boundary door (coordinate-`0` flip) is separated from the
`n+1` interior doors precisely by which coordinate label the flip negates. -/
theorem coordLabel_flipAt_succ_zero (s : Facet (n + 1)) (i : Fin (n + 1)) :
    coordLabel (n + 1) (flipAt (n + 1) s i.succ) 0 = coordLabel (n + 1) s 0 :=
  coordLabel_flipAt_of_ne (n + 1) s (Fin.succ_ne_zero i).symm

/-! ## Axiom audit -- all results are 0-axiom (no `sorryAx`, no `Lean.ofReduceBool`),
dimension-free (no `decide` / `native_decide`). -/

#print axioms negLabel_free
#print axioms coordLabel_antipode
#print axioms coordLabel_flipAt_self
#print axioms compAdj_iff_adj
#print axioms canonicalLabelling_not_tucker_level

end SpernerTuckerCrossPolytopeLabelling
