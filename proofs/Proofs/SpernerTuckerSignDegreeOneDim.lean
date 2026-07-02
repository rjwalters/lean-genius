/-
# The antipodal sign-degree is odd in every dimension (the n = 1 telescoping engine,
# applied to a sign-reduced boundary arc over any label alphabet)

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's lemma and Borsuk–Ulam
from abstract door-counting").

## Where this sits — generalizing oq-04 from n = 2 / `decide` to all dimensions

Iteration 15 (`SpernerTuckerHexagonSignDegree`, gallery child `oq-02-oq-04`) identified
the odd oriented boundary seed the n ≥ 2 program needs: on the hexagon + centre
triangulation of `B²` it pushed the labelling through an antipodal **sign map**
`sgn : Fin 4 → ZMod 2` and proved the hemisphere-arc **sign-degree** (number of edges
across which the sign bit flips) is **odd** — but only for `n = 2`, `α = Fin 4`, and only
by kernel `decide` over all `4³ = 64` boundary labellings.  Its docstring claimed the
oddness holds "by the telescoping (discrete FTC) argument of n = 1 Tucker … realised on
the boundary of real n = 2 geometry", but never actually ran that argument: it re-decided
the count.

The already-verified `TuckerOneDim.tucker_one_dim` runs the telescoping over a `ZMod 2`
path of any length with antipodal endpoints.  What was missing is the **sign-reduction
map** turning a labelling over a rich Tucker alphabet `{±1, …, ±n}` (any dimension, any
alphabet) into that telescoping engine.  This file supplies it — the same discrete-FTC
telescoping, now stated once, dimension-free and alphabet-free, and applied through `sgn`.

## What this file proves (0 sorries, 0 axioms; `decide` only on the finite alphabet's
antipodal property `sgn_negL`, never on the count)

* `changes_cast` / `odd_changes_iff` — the **discrete intermediate-value theorem mod 2**:
  along any `ZMod 2` path `f : ℕ → ZMod 2`, the number of sign-change edges over
  `range N`, cast to `ZMod 2`, is `f N - f 0`; hence it is **odd iff the endpoints
  differ**.  The telescoping engine, stated abstractly over `ℕ`-indexed paths.
* `antipodal_signDegree_odd` — **dimension-free, alphabet-free.**  For ANY label type `α`
  with an antipodal map `neg` and an antipodal sign map `sgn : α → ZMod 2`
  (`sgn (neg x) = sgn x + 1`), and ANY vertex path `μ : ℕ → α` with antipodal endpoints
  (`μ N = neg (μ 0)`), the **sign-degree is odd** — because `sgn` sends antipodal labels
  to distinct `ZMod 2` values, so the reduced path `sgn ∘ μ` has distinct endpoints.  No
  dimension bound, no `decide` over the alphabet or the count.  This is the general odd
  boundary seed; oq-04's hexagon result is the `N = 3`, `α = Fin 4` instance.
* `loop_signDegree_even` — the companion: a **closed** antipodal loop
  (`sgn (μ N) = sgn (μ 0)`) has **even** sign-degree in every dimension — the abstract form
  of oq-04's `full_sign_changes_even` ("read the degree off half the loop").
* `HexagonInstance.hexagon_arc_signDegree_odd` — oq-04's hexagon hemisphere-arc oddness,
  re-derived as a **corollary of the telescoping engine** rather than by `decide` over the
  count.  Only the alphabet's antipodal property `sgn_negL` and the boundary condition
  `arc_bdry` are decided (finite facts about `Fin 4`); the oddness itself now flows from
  the dimension-free `antipodal_signDegree_odd`.  Realizes in Lean the n = 2 → n = 1
  connection oq-04 asserted in prose.

## Honest status

A **unification / scoping result**, not a proof of n ≥ 2 Tucker.  It shows the odd oriented
boundary seed is dimension-free and factors through the n = 1 telescoping engine for every
label alphabet — removing oq-04's dimension restriction and its brute-force `decide` on the
count.  The genuine open lever remains the 2-D almost-complementary path-following that
turns this odd **boundary sign-degree** into an **interior complementary simplex**.

Self-contained (narrow imports; the telescoping is the same `Finset.sum_range_sub` /
`ZMod 2` mod-reduction the n = 1 file uses).  0 sorries, 0 axioms
(`propext` / `Classical.choice` / `Quot.sound` only — no `sorryAx`, no `Lean.ofReduceBool`).
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Parity

open Finset

namespace SpernerTuckerSignDegreeOneDim

variable {α : Type*}

/-! ## The discrete intermediate-value theorem mod 2 (the telescoping engine) -/

/-- The complementarity indicator in `ZMod 2`: the difference of two labels is `1` when
they differ and `0` when they agree. -/
private lemma edge : ∀ a b : ZMod 2, (if a ≠ b then (1 : ZMod 2) else 0) = a - b := by decide

/-- In `ZMod 2`, `x + 1 ≠ x`. -/
private lemma add_one_ne : ∀ x : ZMod 2, x + 1 ≠ x := by decide

/-- **Sign-change count** of a `ZMod 2` path `f` over its first `N` edges. -/
def changes (f : ℕ → ZMod 2) (N : ℕ) : ℕ := (Finset.range N).filter (fun i => f (i + 1) ≠ f i) |>.card

/-- **Telescoping identity (discrete FTC mod 2).**  The number of sign-change edges of a
`ZMod 2` path, cast into `ZMod 2`, equals the net endpoint difference `f N - f 0`.  Proved
by turning the filter cardinality into a `ZMod 2` sum of indicators and telescoping. -/
theorem changes_cast (f : ℕ → ZMod 2) (N : ℕ) :
    (changes f N : ZMod 2) = f N - f 0 := by
  unfold changes
  rw [← Finset.sum_boole, ← Finset.sum_range_sub f N]
  apply Finset.sum_congr rfl
  intro i _
  exact edge (f (i + 1)) (f i)

/-- **Discrete intermediate-value theorem mod 2.**  The sign-change count over `range N`
is **odd iff the endpoints differ** (`f N ≠ f 0`). -/
theorem odd_changes_iff (f : ℕ → ZMod 2) (N : ℕ) :
    Odd (changes f N) ↔ f N ≠ f 0 := by
  rw [← Nat.not_even_iff_odd, ← ZMod.natCast_eq_zero_iff_even, changes_cast, sub_eq_zero]

/-! ## The antipodal sign-degree, dimension-free and alphabet-free -/

/-- **Sign-degree** of a vertex path `μ : ℕ → α` under a sign map `sgn`: the number of
edges (over the first `N`) across which the sign bit flips. -/
def signDegree (sgn : α → ZMod 2) (μ : ℕ → α) (N : ℕ) : ℕ := changes (fun i => sgn (μ i)) N

/-- **Dimension-free antipodal sign-degree (odd).**  Let `neg` be an antipodal map on a
label alphabet `α` and `sgn : α → ZMod 2` an antipodal sign map
(`sgn (neg x) = sgn x + 1`).  For any vertex path `μ` whose endpoints are antipodal
(`μ N = neg (μ 0)`), the sign-degree is **odd**.  The reduced labelling `sgn ∘ μ` has
distinct endpoints (`sgn (μ 0) + 1 ≠ sgn (μ 0)`), so `odd_changes_iff` fires.  No dimension
bound, no `decide` over the alphabet. -/
theorem antipodal_signDegree_odd
    (neg : α → α) (sgn : α → ZMod 2) (hsgn : ∀ x, sgn (neg x) = sgn x + 1)
    (μ : ℕ → α) (N : ℕ) (hbdry : μ N = neg (μ 0)) :
    Odd (signDegree sgn μ N) := by
  unfold signDegree
  rw [odd_changes_iff]
  show sgn (μ N) ≠ sgn (μ 0)
  rw [hbdry, hsgn]
  exact add_one_ne (sgn (μ 0))

/-- **Dimension-free antipodal sign-degree (even, closed loop).**  If the sign path is
**closed** (`sgn (μ N) = sgn (μ 0)`) then the sign-degree is **even**.  The odd seed lives
on the antipodal fundamental domain (a hemisphere arc), not on the whole boundary loop. -/
theorem loop_signDegree_even
    (sgn : α → ZMod 2) (μ : ℕ → α) (N : ℕ) (hloop : sgn (μ N) = sgn (μ 0)) :
    Even (signDegree sgn μ N) := by
  unfold signDegree
  rw [← ZMod.natCast_eq_zero_iff_even, changes_cast]
  show sgn (μ N) - sgn (μ 0) = 0
  rw [hloop, sub_self]

/-! ## Concrete instance: oq-04's hexagon hemisphere arc, from the engine (not `decide`) -/

namespace HexagonInstance

/-- Label negation on `{+1,+2,-1,-2}` encoded as `Fin 4` (same as
`SpernerTuckerHexagonSignDegree.negL`). -/
def negL : Fin 4 → Fin 4 := ![2, 3, 0, 1]

/-- Sign map collapsing magnitude, `{+1,+2} ↦ 0`, `{-1,-2} ↦ 1` (same as
`SpernerTuckerHexagonSignDegree.sgn`). -/
def sgn : Fin 4 → ZMod 2 := ![0, 0, 1, 1]

/-- The sign map is antipodal (label negation flips the sign bit).  This finite fact about
the `Fin 4` alphabet is the sole `decide`; it discharges the hypothesis `hsgn`. -/
theorem sgn_negL : ∀ x : Fin 4, sgn (negL x) = sgn x + 1 := by decide

/-- The four vertices `v₀, v₁, v₂, v₃ = -v₀` of the antipodal fundamental-domain arc
(a hemisphere of the hexagon boundary), from three free boundary labels `a, b, c`. -/
def arc (a b c : Fin 4) : ℕ → Fin 4 := fun i => [a, b, c, negL a].getD i a

/-- The arc has antipodal endpoints: `v₃ = -v₀`.  A finite fact about `Fin 4`. -/
theorem arc_bdry : ∀ a b c : Fin 4, arc a b c 3 = negL (arc a b c 0) := by decide

/-- **oq-04's hexagon hemisphere-arc sign-degree is ODD — now from the telescoping engine.**
`SpernerTuckerHexagonSignDegree.arc_sign_changes_odd` established this by `decide` over all
64 labellings; here the oddness is a corollary of the dimension-free
`antipodal_signDegree_odd`, with only the alphabet's antipodal property (`sgn_negL`) and the
boundary condition (`arc_bdry`) decided.  Realizes in Lean the "= n = 1 Tucker count of the
sign-reduced labelling" connection oq-04 asserted in prose. -/
theorem hexagon_arc_signDegree_odd (a b c : Fin 4) :
    Odd (signDegree sgn (arc a b c) 3) :=
  antipodal_signDegree_odd negL sgn sgn_negL (arc a b c) 3 (arc_bdry a b c)

end HexagonInstance

#print axioms antipodal_signDegree_odd
#print axioms loop_signDegree_even
#print axioms HexagonInstance.hexagon_arc_signDegree_odd

end SpernerTuckerSignDegreeOneDim
