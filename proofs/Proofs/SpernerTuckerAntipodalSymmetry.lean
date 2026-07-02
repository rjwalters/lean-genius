/-
# Antipodal symmetry kills the door-graph endpoint parity (n ≥ 1)

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's Lemma and Borsuk–Ulam
from abstract door-counting").

## Where this sits

The door-counting program reduces full-dimensional Tucker to a single open input —
the **geometric `bridge`** of `SpernerTuckerInductiveTower.TuckerTower`: the boundary
doors of the dimension-`(n+1)` complex are the interior complementary simplices of the
dimension-`n` complex.  The tower consumes an **odd** interior-endpoint count
(`interiorEndpoints`) at each level and propagates it upward.

`SpernerTuckerAntipodalParity.even_card_antipodal_boundary` already recorded the
dimension-free fact that the antipodal map is a **free involution** on the *raw boundary
doors*, so their count is always even.  But the object the tower actually consumes is not
the raw door set — it is the set of **degree-1 endpoints of the almost-complementary door
graph** (`SpernerTuckerInductiveTower.interiorEndpoints`/`boundaryEndpoints`).  This file
proves the analogue for *that* object, and turns it into a structural **no-go theorem**.

## What this file proves

Let `G` be a door graph on the top cells, `B` a boundary predicate, and `σ` the antipodal
map.  Suppose `σ` is

* a **free involution** (`σ ∘ σ = id`, `σ v ≠ v` — no cell is its own antipode), and
* a **boundary-preserving graph automorphism** (`G.Adj (σ v) (σ w) ↔ G.Adj v w` and
  `B (σ v) ↔ B v`).

Then:

* `degree_eq_of_aut`                    — `σ` preserves the degree of every vertex;
* `even_card_interiorEndpoints`         — the **interior** endpoint count is **even**;
* `even_card_boundaryEndpoints`         — the **boundary** endpoint count is **even**;
* `not_odd_card_interiorEndpoints`      — hence it is **never odd**;
* `symmetric_graph_not_tucker_level`    — so an antipodally-symmetric door graph can
  **never** be a Tucker level: the tower needs `Odd (interior n)`, which is impossible
  under the symmetry.

## Why this matters

Every prior session flagged (empirically, iteration 12) that the interior spoke-door graph
"produces ZERO endpoints on 64/256 labellings while Tucker holds", so the remaining bridge
input must be an *oriented / antipodally-signed* count, **not** a door-counting parity.
This file is the dimension-free structural reason: whenever the antipodal involution is an
honest graph symmetry, both endpoint classes split into antipodal 2-orbits, forcing an
*even* count — Tucker's *odd* interior count is unreachable.  The oddness can therefore only
appear once the symmetry is **broken**, i.e. on a *hemisphere fundamental domain* (cf.
`SpernerTuckerHemisphere.card_eq_two_mul_hemisphere`), where `σ` maps one hemisphere to the
other and ceases to be an automorphism.  So the labelling-induced asymmetry of the
almost-complementary door graph is not incidental — it is *essential*, and this is the
abstract obstruction that pins the exact shape of the open `bridge`.

The general lemma `even_card_filter_of_free_involution` (a free involution preserving a
decidable predicate forces an even fibre) is a reusable Mathlib-gap fact, the predicate-
restricted form of `SpernerTuckerAntipodalParity.even_card_of_free_involution`.

Self-contained: imports Mathlib and the tower.  0 sorries, 0 axioms
(`propext` / `Classical.choice` / `Quot.sound` only — NO `decide`/`native_decide`/
`ofReduceBool`).
-/
import Mathlib
import Proofs.SpernerTuckerInductiveTower

namespace SpernerTuckerAntipodalSymmetry

open Finset SimpleGraph SpernerTuckerInductiveTower

/-! ## A free involution forces an even cardinality

We reprove the base fact `even_card_of_free_involution` locally (it also lives in
`SpernerTuckerAntipodalParity`, but inlining it keeps this file's import chain minimal).
A fixed-point-free involution pairs the elements into disjoint 2-orbits, so the type has
even cardinality — obtained by summing `1 : ZMod 2` over `univ` and cancelling antipodal
pairs via `Finset.sum_ninvolution` (`1 + 1 = 0`). -/

/-- **A free involution forces even cardinality.**  If `σ : α → α` is an involution with
no fixed points, then `α` has even cardinality. -/
theorem even_card_of_free_involution {α : Type*} [Fintype α] {σ : α → α}
    (hinv : Function.Involutive σ) (hfree : ∀ a, σ a ≠ a) :
    Even (Fintype.card α) := by
  classical
  have hsum : (∑ _a ∈ (univ : Finset α), (1 : ZMod 2)) = 0 := by
    apply Finset.sum_ninvolution σ
    · intro a; decide
    · intro a _; exact hfree a
    · intro a; exact mem_univ _
    · intro a; exact hinv a
  rw [Finset.sum_const, card_univ, nsmul_eq_mul, mul_one] at hsum
  rwa [ZMod.natCast_eq_zero_iff_even] at hsum

/-! ## A free involution preserving a predicate forces an even fibre -/

/-- **A free involution preserving a decidable predicate forces an even fibre.**  If
`σ` is a fixed-point-free involution and the predicate `P` is `σ`-invariant
(`P (σ a) ↔ P a`), then `σ` restricts to a free involution on `{a | P a}`, so that set
has even cardinality.

This is the predicate-restricted form of
`SpernerTuckerAntipodalParity.even_card_of_free_involution` (the `P = ⊤` case), obtained
by transporting that lemma along the subtype `{a // P a}`. -/
theorem even_card_filter_of_free_involution {α : Type*} [Fintype α] {σ : α → α}
    (hinv : Function.Involutive σ) (hfree : ∀ a, σ a ≠ a)
    {P : α → Prop} [DecidablePred P] (hP : ∀ a, P (σ a) ↔ P a) :
    Even #{a | P a} := by
  classical
  -- `σ` restricts to a free involution on the subtype `{a // P a}`.
  let σ' : {a // P a} → {a // P a} := fun x => ⟨σ x.1, (hP x.1).mpr x.2⟩
  have hinv' : Function.Involutive σ' := fun x => Subtype.ext (hinv x.1)
  have hfree' : ∀ x : {a // P a}, σ' x ≠ x := fun x h => hfree x.1 (Subtype.ext_iff.mp h)
  have h := even_card_of_free_involution (α := {a // P a}) hinv' hfree'
  rwa [Fintype.card_subtype] at h

/-! ## The antipodal symmetry setup -/

section Symmetry

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (B : V → Prop) [DecidablePred B]
variable {σ : V → V}

/-- **A graph automorphism preserves degree.**  If `σ` is an involution and an
automorphism of `G` (`G.Adj (σ v) (σ w) ↔ G.Adj v w`), then `σ` carries the neighbours of
`σ v` bijectively onto the neighbours of `v`, so `G.degree (σ v) = G.degree v`. -/
theorem degree_eq_of_aut (hinv : Function.Involutive σ)
    (haut : ∀ v w, G.Adj (σ v) (σ w) ↔ G.Adj v w) (v : V) :
    G.degree (σ v) = G.degree v := by
  rw [← G.card_neighborFinset_eq_degree (σ v),
      ← G.card_neighborFinset_eq_degree v]
  apply Finset.card_bij (fun w _ => σ w)
  · -- maps neighbours of `σ v` to neighbours of `v`
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    rw [SimpleGraph.mem_neighborFinset]
    have h := (haut v (σ w)).mp
    rw [hinv w] at h
    exact h hw
  · -- injective
    intro w₁ _ w₂ _ h
    exact hinv.injective h
  · -- surjective
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    refine ⟨σ w, ?_, hinv w⟩
    rw [SimpleGraph.mem_neighborFinset]
    exact (haut v w).mpr hw

/-- **The interior-endpoint count is even under antipodal symmetry.**  If the antipodal
map `σ` is a free involution, a graph automorphism, and boundary-preserving, then the
degree-1 *interior* vertices split into antipodal 2-orbits, so their number is even. -/
theorem even_card_interiorEndpoints (hinv : Function.Involutive σ) (hfree : ∀ v, σ v ≠ v)
    (haut : ∀ v w, G.Adj (σ v) (σ w) ↔ G.Adj v w) (hB : ∀ v, B (σ v) ↔ B v) :
    Even #(interiorEndpoints G B) := by
  show Even #{v | G.degree v = 1 ∧ ¬ B v}
  refine even_card_filter_of_free_involution hinv hfree ?_
  intro v
  show (G.degree (σ v) = 1 ∧ ¬ B (σ v)) ↔ (G.degree v = 1 ∧ ¬ B v)
  rw [degree_eq_of_aut G hinv haut v, hB v]

/-- **The boundary-endpoint count is even under antipodal symmetry.**  Same argument as
`even_card_interiorEndpoints`, for the degree-1 *boundary* vertices. -/
theorem even_card_boundaryEndpoints (hinv : Function.Involutive σ) (hfree : ∀ v, σ v ≠ v)
    (haut : ∀ v w, G.Adj (σ v) (σ w) ↔ G.Adj v w) (hB : ∀ v, B (σ v) ↔ B v) :
    Even #(boundaryEndpoints G B) := by
  show Even #{v | G.degree v = 1 ∧ B v}
  refine even_card_filter_of_free_involution hinv hfree ?_
  intro v
  show (G.degree (σ v) = 1 ∧ B (σ v)) ↔ (G.degree v = 1 ∧ B v)
  rw [degree_eq_of_aut G hinv haut v, hB v]

/-- **The interior-endpoint count is never odd under antipodal symmetry.**  Immediate from
`even_card_interiorEndpoints`. -/
theorem not_odd_card_interiorEndpoints (hinv : Function.Involutive σ) (hfree : ∀ v, σ v ≠ v)
    (haut : ∀ v w, G.Adj (σ v) (σ w) ↔ G.Adj v w) (hB : ∀ v, B (σ v) ↔ B v) :
    ¬ Odd #(interiorEndpoints G B) := by
  rw [Nat.not_odd_iff_even]
  exact even_card_interiorEndpoints G B hinv hfree haut hB

/-- **No-go theorem: an antipodally-symmetric door graph is never a Tucker level.**  A
Tucker level requires an **odd** interior-endpoint count (this is what
`SpernerTuckerInductiveTower.TuckerTower.tower_interior_odd` propagates and what
`exists_interior_of_odd` turns into a complementary simplex).  But a free, automorphic,
boundary-preserving antipodal involution forces that count to be **even**.  The two are
contradictory: whenever the antipodal map is an honest boundary-preserving graph symmetry,
Tucker's odd interior count is impossible.

Consequently the odd count can only appear once the symmetry is **broken** — on a
hemisphere fundamental domain (`SpernerTuckerHemisphere`), where `σ` swaps the two
hemispheres and is no longer an automorphism.  The labelling-induced asymmetry of the
almost-complementary door graph is therefore essential, not incidental. -/
theorem symmetric_graph_not_tucker_level (hinv : Function.Involutive σ)
    (hfree : ∀ v, σ v ≠ v) (haut : ∀ v w, G.Adj (σ v) (σ w) ↔ G.Adj v w)
    (hB : ∀ v, B (σ v) ↔ B v) (hodd : Odd #(interiorEndpoints G B)) : False :=
  not_odd_card_interiorEndpoints G B hinv hfree haut hB hodd

end Symmetry

#check @even_card_filter_of_free_involution
#check @degree_eq_of_aut
#check @even_card_interiorEndpoints
#check @symmetric_graph_not_tucker_level

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`.
#print axioms even_card_filter_of_free_involution
#print axioms degree_eq_of_aut
#print axioms even_card_interiorEndpoints
#print axioms symmetric_graph_not_tucker_level

end SpernerTuckerAntipodalSymmetry
