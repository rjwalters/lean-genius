/-
# Where Tucker's odd count comes from: the fixed-point parity of an antipodal involution (n ≥ 1)

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's Lemma and Borsuk–Ulam
from abstract door-counting").

## Where this sits

The door-counting program for Tucker reduces full-dimensional Tucker to a single open
input — the **geometric `bridge`** of `SpernerTuckerInductiveTower.TuckerTower`, which
consumes an **odd** interior-endpoint count at every level.  Two prior sessions pinned the
*obstruction* to producing that odd count:

* `SpernerTuckerAntipodalParity.even_card_antipodal_boundary` and
  `SpernerTuckerHemisphere.card_eq_two_mul_hemisphere` — the antipodal map is a **free**
  involution on the boundary doors, so their count is always **even** (`= 2 × hemisphere`);
* `SpernerTuckerAntipodalSymmetry.even_card_interiorEndpoints` — if the antipodal map is a
  free, boundary-preserving graph **automorphism**, the interior-endpoint count is even,
  so an antipodally-symmetric door graph can **never** be a Tucker level (the no-go theorem).

Both results assume the antipodal involution is **fixed-point free** and conclude *even*.
Every prior session then said, in prose, that the odd count "can only appear once the
symmetry is broken."  This file supplies the **positive, quantitative** counterpart that
those no-go theorems were the negative half of: the general involution parity

  `Fintype.card α ≡ #{a | σ a = a}  (mod 2)`,

valid for **any** involution — free or not.  It says the parity of a finite set carrying an
involution is governed *exactly* by its **fixed points**.  Freeness (no fixed point) forces
even (recovering the no-go); an **odd number of fixed points** forces odd.  So the odd
interior count Tucker needs is neither mysterious nor merely "the symmetry being broken" —
it is precisely an **odd number of self-antipodal complementary simplices**, the cells the
antipodal map fixes.

## What this file proves

Abstract parity engine (dimension-free, any finite type):

* `even_card_not_fixed`            — the non-fixed points of an involution are even in
  number (they split into free antipodal 2-orbits);
* `odd_card_iff_odd_fixed`         — `Odd (card α) ↔ Odd #{a | σ a = a}` (the headline
  fixed-point parity);
* `odd_card_of_unique_fixed`       — an involution with a *unique* fixed point forces odd
  cardinality (the cleanest odd seed);
* `even_card_not_fixed_of_invariant`, `odd_card_filter_iff_odd_fixed` — the same over a
  `σ`-invariant predicate `P`: `Odd #{a | P a} ↔ Odd #{a | P a ∧ σ a = a}`.

Tucker specialisation (the payoff), over the tower's `interiorEndpoints`:

* `odd_interiorEndpoints_iff_odd_selfAntipodal` — for a boundary-preserving antipodal
  **automorphism** `σ` (*not* assumed free), the interior-endpoint count is odd **iff** the
  number of **self-antipodal** (`σ v = v`) interior endpoints is odd;
* `exists_selfAntipodal_of_tucker_level` — hence a Tucker level (odd interior count)
  **forces the existence of a self-antipodal complementary simplex** — the exact cell the
  antipodal map cannot pair away;
* `even_interiorEndpoints_of_free` — re-deriving
  `SpernerTuckerAntipodalSymmetry.even_card_interiorEndpoints` as the `#fixed = 0` corollary,
  showing this result strictly **generalises** iteration 13's no-go theorem.

## Why this matters

Iteration 13's no-go (`symmetric_graph_not_tucker_level`) proved a symmetric door graph is
never a Tucker level but assumed **freeness** and could only conclude *even*.  This file
removes the freeness assumption and turns the obstruction into a **characterisation**: a
boundary-preserving antipodal automorphism is a Tucker level *exactly* when it has an odd
number of self-antipodal complementary simplices.  This localises the still-open odd input
of the `bridge` onto a concrete, geometrically meaningful set — the cells fixed by the
antipodal map (intuitively the central simplices of the ball `Bⁿ`, near the origin the
antipodal reflection fixes) — rather than "some symmetry breaking."  It is the missing
*positive* half of the free-involution parity dichotomy the program is built on.

The general lemma `odd_card_iff_odd_fixed` (any involution's cardinality is congruent mod 2
to its fixed-point count) is reusable Mathlib-gap infrastructure — the involution analogue
of the handshaking lemma, dual to `even_card_of_free_involution`.

Self-contained: imports Mathlib and the iteration-13 symmetry file (for `degree_eq_of_aut`
and the tower's `interiorEndpoints`).  0 sorries, 0 axioms (`propext` / `Classical.choice` /
`Quot.sound` only — NO `decide` / `native_decide` / `ofReduceBool`).
-/
import Mathlib
import Proofs.SpernerTuckerAntipodalSymmetry

namespace SpernerTuckerFixedPointParity

open Finset SimpleGraph

/-! ## The abstract fixed-point parity engine

For an involution `σ` on a finite type, the non-fixed points split into free antipodal
2-orbits, so they are even in number; hence the parity of the whole type is carried
entirely by the fixed points.  This is the involution analogue of the handshaking lemma
and the exact dual of `SpernerTuckerAntipodalSymmetry.even_card_of_free_involution`
(the fixed-point-free case). -/

variable {α : Type*} [Fintype α] [DecidableEq α] {σ : α → α}

/-- **The non-fixed points of an involution are even in number.**  On the subtype
`{a // ¬ σ a = a}` the involution `σ` is fixed-point free, so that subtype has even
cardinality; transporting along `Fintype.card_subtype` gives the count over the ambient
type. -/
theorem even_card_not_fixed (hinv : Function.Involutive σ) :
    Even #{a | ¬ σ a = a} := by
  classical
  have h := SpernerTuckerAntipodalSymmetry.even_card_of_free_involution
    (α := {a // ¬ σ a = a})
    (σ := fun x => ⟨σ x.1, by rw [hinv x.1]; exact fun he => x.2 he.symm⟩)
    (fun x => Subtype.ext (hinv x.1))
    (fun x hx => x.2 (congrArg Subtype.val hx))
  rwa [Fintype.card_subtype] at h

/-- **Fixed-point parity of an involution.**  The cardinality of a finite type carrying an
involution `σ` is congruent mod 2 to its number of fixed points:

  `Odd (Fintype.card α) ↔ Odd #{a | σ a = a}`.

The fixed points and the non-fixed points partition the type; the latter are even
(`even_card_not_fixed`), so all of the parity lives on the fixed points.  This is the
positive counterpart of the free-involution "even cardinality" fact — the involution
analogue of the handshaking lemma. -/
theorem odd_card_iff_odd_fixed (hinv : Function.Involutive σ) :
    Odd (Fintype.card α) ↔ Odd #{a | σ a = a} := by
  classical
  have key := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset α)) (p := fun a => σ a = a)
  rw [Finset.card_univ] at key
  have heven : Even #{a | ¬ σ a = a} := even_card_not_fixed hinv
  rw [Nat.odd_iff, Nat.odd_iff]
  rw [Nat.even_iff] at heven
  omega

/-- **A unique fixed point forces odd cardinality.**  If an involution has exactly one
fixed point, the type has odd cardinality — the cleanest way to manufacture an odd count. -/
theorem odd_card_of_unique_fixed (hinv : Function.Involutive σ)
    (h1 : #{a | σ a = a} = 1) : Odd (Fintype.card α) :=
  (odd_card_iff_odd_fixed hinv).mpr (by rw [h1]; exact odd_one)

/-! ## The predicate-restricted form

The same argument relativised to a `σ`-invariant predicate `P` (`P (σ a) ↔ P a`): the
non-fixed `P`-points split into free 2-orbits, so `Odd #{P} ↔ Odd #{P ∧ fixed}`. -/

/-- **The non-fixed `P`-points are even in number**, for a `σ`-invariant decidable
predicate `P`.  On the subtype `{a // P a ∧ ¬ σ a = a}` the involution `σ` (which preserves
`P`) is fixed-point free. -/
theorem even_card_not_fixed_of_invariant (hinv : Function.Involutive σ)
    {P : α → Prop} [DecidablePred P] (hP : ∀ a, P (σ a) ↔ P a) :
    Even #{a | P a ∧ ¬ σ a = a} := by
  classical
  have h := SpernerTuckerAntipodalSymmetry.even_card_of_free_involution
    (α := {a // P a ∧ ¬ σ a = a})
    (σ := fun x => ⟨σ x.1, (hP x.1).mpr x.2.1, by rw [hinv x.1]; exact fun he => x.2.2 he.symm⟩)
    (fun x => Subtype.ext (hinv x.1))
    (fun x hx => x.2.2 (congrArg Subtype.val hx))
  rwa [Fintype.card_subtype] at h

/-- **Fixed-point parity, relativised to a `σ`-invariant predicate.**  If `P` is preserved
by the involution `σ`, then `Odd #{a | P a} ↔ Odd #{a | P a ∧ σ a = a}`: among the
`P`-points, the parity is carried by those `P`-points that `σ` fixes. -/
theorem odd_card_filter_iff_odd_fixed (hinv : Function.Involutive σ)
    {P : α → Prop} [DecidablePred P] (hP : ∀ a, P (σ a) ↔ P a) :
    Odd #{a | P a} ↔ Odd #{a | P a ∧ σ a = a} := by
  classical
  have key := Finset.filter_card_add_filter_neg_card_eq_card
    (s := ({a | P a} : Finset α)) (p := fun a => σ a = a)
  simp only [Finset.filter_filter] at key
  have heven : Even #{a | P a ∧ ¬ σ a = a} := even_card_not_fixed_of_invariant hinv hP
  rw [Nat.odd_iff, Nat.odd_iff]
  rw [Nat.even_iff] at heven
  omega

/-! ## Tucker specialisation: the odd count lives on the self-antipodal simplices

We now feed the tower's `interiorEndpoints` (degree-1 non-boundary vertices — the
complementary simplices Tucker asserts) into the predicate-restricted parity, with `P` the
interior-endpoint predicate and `σ` the antipodal map.  A boundary-preserving graph
automorphism preserves `P` (via `degree_eq_of_aut`), so the interior count is odd iff the
number of **self-antipodal** interior endpoints is odd. -/

section Symmetry

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
variable (B : V → Prop) [DecidablePred B]
variable {σ : V → V}

open SpernerTuckerInductiveTower

/-- **The interior-endpoint count is odd iff the self-antipodal interior count is odd.**
For a boundary-preserving antipodal **automorphism** `σ` — an involution with
`G.Adj (σ v) (σ w) ↔ G.Adj v w` and `B (σ v) ↔ B v`, but *not* assumed fixed-point free —
the number of degree-1 interior (complementary) vertices has the same parity as the number
of those vertices that `σ` fixes.  The automorphism preserves the interior-endpoint
predicate (`degree_eq_of_aut` preserves degree, `hB` preserves the boundary), so this is
`odd_card_filter_iff_odd_fixed` with `P v := G.degree v = 1 ∧ ¬ B v`. -/
theorem odd_interiorEndpoints_iff_odd_selfAntipodal (hinv : Function.Involutive σ)
    (haut : ∀ v w, G.Adj (σ v) (σ w) ↔ G.Adj v w) (hB : ∀ v, B (σ v) ↔ B v) :
    Odd #(interiorEndpoints G B) ↔
      Odd #((interiorEndpoints G B).filter (fun v => σ v = v)) := by
  have hP : ∀ v, (G.degree (σ v) = 1 ∧ ¬ B (σ v)) ↔ (G.degree v = 1 ∧ ¬ B v) := by
    intro v
    rw [SpernerTuckerAntipodalSymmetry.degree_eq_of_aut G hinv haut v, hB v]
  have h := odd_card_filter_iff_odd_fixed (σ := σ) hinv
    (P := fun v => G.degree v = 1 ∧ ¬ B v) hP
  simpa [interiorEndpoints, Finset.filter_filter] using h

/-- **A Tucker level forces a self-antipodal complementary simplex.**  If the interior
(complementary) count is odd — i.e. this door graph is a Tucker level — under a
boundary-preserving antipodal automorphism, then some interior endpoint is **fixed** by the
antipodal map (`σ v = v`).  The antipodal map cannot pair every complementary simplex with
a distinct partner; at least one is its own antipode.  This is the positive dual of the
iteration-13 no-go theorem. -/
theorem exists_selfAntipodal_of_tucker_level (hinv : Function.Involutive σ)
    (haut : ∀ v w, G.Adj (σ v) (σ w) ↔ G.Adj v w) (hB : ∀ v, B (σ v) ↔ B v)
    (hodd : Odd #(interiorEndpoints G B)) :
    ∃ v ∈ interiorEndpoints G B, σ v = v := by
  have h := (odd_interiorEndpoints_iff_odd_selfAntipodal G B hinv haut hB).mp hodd
  obtain ⟨v, hv⟩ := Finset.card_pos.mp h.pos
  rw [Finset.mem_filter] at hv
  exact ⟨v, hv.1, hv.2⟩

/-- **Recovers iteration 13's no-go as the fixed-point-free case.**  If the antipodal
automorphism `σ` is additionally fixed-point free (`σ v ≠ v` for every `v`), then there is
no self-antipodal interior endpoint, so the interior count cannot be odd — it is even.  This
reproduces `SpernerTuckerAntipodalSymmetry.even_card_interiorEndpoints`, exhibiting the
present file as a strict generalisation: freeness is exactly the `#fixed = 0` special case
of the fixed-point parity. -/
theorem even_interiorEndpoints_of_free (hinv : Function.Involutive σ)
    (haut : ∀ v w, G.Adj (σ v) (σ w) ↔ G.Adj v w) (hB : ∀ v, B (σ v) ↔ B v)
    (hfree : ∀ v, σ v ≠ v) :
    Even #(interiorEndpoints G B) := by
  rw [← Nat.not_odd_iff_even]
  intro hodd
  obtain ⟨v, _, hv⟩ := exists_selfAntipodal_of_tucker_level G B hinv haut hB hodd
  exact hfree v hv

end Symmetry

#check @even_card_not_fixed
#check @odd_card_iff_odd_fixed
#check @odd_card_of_unique_fixed
#check @odd_card_filter_iff_odd_fixed
#check @odd_interiorEndpoints_iff_odd_selfAntipodal
#check @exists_selfAntipodal_of_tucker_level
#check @even_interiorEndpoints_of_free

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`.
#print axioms odd_card_iff_odd_fixed
#print axioms odd_card_filter_iff_odd_fixed
#print axioms exists_selfAntipodal_of_tucker_level
#print axioms even_interiorEndpoints_of_free

end SpernerTuckerFixedPointParity
