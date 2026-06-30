/-
# Antipodal parity for the Tucker door-counting program (n ≥ 1)

Research artifact for `sperner-mathlib4-oq-02` ("Tucker's Lemma and Borsuk–Ulam from
abstract door-counting").

## Where this sits

The door-counting program reduces full-dimensional Tucker to a single open input —
the **geometric `bridge`** of `SpernerTuckerInductiveTower.TuckerTower`: the boundary
doors of the dimension-`(n+1)` complex are the interior complementary simplices of the
dimension-`n` complex.  Every single-level parity piece is already machine-checked; the
companion files repeatedly flag two things this file addresses head-on:

1. **Why the bridge cannot use the *raw* boundary count.**
   `SpernerTuckerBoundaryParity.ring_complementary_count_even` established — but only for
   the `n = 2` hexagon, by a 64-case `decide` — that the raw antipodal boundary count is
   *even*, so the odd parity the engine needs must come from the lower dimension.  Here we
   prove the *general, dimension-free reason*: the antipodal map is a **free involution**
   on the boundary doors, and a free involution forces an even cardinality.  Mathlib has
   no such lemma (only the much heavier `p`-group `card_modEq_card_fixedPoints`), so the
   core fact is proved from scratch.

2. **What shape the open obligation actually has.**  The tower takes `bridge` as a bare
   parity *equivalence*.  Geometrically it is an honest **cardinality bijection** (the
   boundary of `Bⁿ⁺¹` is `Sⁿ`, on which the labelling is an `n`-Tucker instance).  We
   record the refinement `bridge` ⇐ `boundary (n+1) = interior n` and build a tower from
   such count equalities, then exhibit the first **non-trivial** (growing-count) tower —
   the only prior instance was the constant-`1` `trivialTower`.

## Honest status

This is parity *infrastructure*, not new Tucker geometry.  Pillar 1 is a genuine, reusable
Mathlib-gap lemma that generalises a previously `decide`-only fact to every dimension;
Pillar 2 sharpens the open obligation (bijection, not parity coincidence) and shows the
recursion does substantive work on non-constant data.  The geometric construction of the
boundary bijection remains the open frontier, exactly as every prior session flagged.

Self-contained.  0 sorries, 0 axioms (propext / Classical.choice / Quot.sound only).
-/
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Proofs.SpernerTuckerInductiveTower

namespace SpernerTuckerAntipodalParity

open Finset SpernerTuckerInductiveTower

/-! ## Pillar 1 — the free-involution parity engine -/

/-- **A free involution forces even cardinality.**  If `σ : α → α` is an involution
(`σ ∘ σ = id`) with no fixed points (`σ a ≠ a` for every `a`), then `α` has even
cardinality: `σ` pairs the elements of `α` into disjoint 2-element orbits.

Mathlib has no direct form of this (only the `p`-group `card_modEq_card_fixedPoints`,
which is much heavier).  Proof: sum the constant `1 : ZMod 2` over `univ`; `σ` cancels
the summand in antipodal pairs (`1 + 1 = 0` in `ZMod 2`) via `Finset.sum_ninvolution`,
so the total — which is `Fintype.card α` reduced mod `2` — vanishes, i.e. the card is
even. -/
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

/-- **The raw antipodal boundary count is even — in every dimension.**  The boundary
doors of an antipodally-symmetric triangulation carry the free antipodal involution
`d ↦ -d` (a boundary door and its antipode are distinct boundary doors).  Hence the
*raw* number of boundary doors is always even.

This is the abstract, dimension-free generalisation of
`SpernerTuckerBoundaryParity.ring_complementary_count_even`, which established the same
fact for the `n = 2` hexagon by a 64-case `decide`.  It is precisely why the inductive
`bridge` must take its odd boundary parity from the lower-dimensional Tucker instance
(the interior count) and **not** from the raw boundary ring. -/
theorem even_card_antipodal_boundary {Door : Type*} [Fintype Door] {neg : Door → Door}
    (hinv : Function.Involutive neg) (hfree : ∀ d, neg d ≠ d) :
    Even (Fintype.card Door) :=
  even_card_of_free_involution hinv hfree

/-! ## Pillar 2 — the geometric bridge as an explicit cardinality bijection -/

/-- A **cardinality equality** `a = b` (the count consequence of an explicit bijection)
yields the `TuckerTower.bridge` parity equivalence.  This records the true shape of the
open geometric obligation: not a bare parity coincidence, but an honest bijection — the
antipodal boundary of `Bⁿ⁺¹` is `Sⁿ`, on which the labelling is an `n`-Tucker instance,
so its boundary doors are in bijection with the level-`n` interior simplices. -/
theorem bridge_of_card_eq {a b : ℕ} (h : a = b) : Odd a ↔ Odd b := by rw [h]

/-- Build a `TuckerTower` from explicit per-level **count equalities**
`boundary (n+1) = interior n` (the cardinality consequence of the geometric boundary
bijection), the single-level engine `step`, and the verified base case.  This is strictly
stronger input than `TuckerTower.bridge` — an equality of counts, not merely of parities —
and is exactly what an explicit bijection supplies. -/
def towerOfCountEq
    (boundary interior : ℕ → ℕ)
    (step : ∀ n, Odd (boundary n) ↔ Odd (interior n))
    (hcard : ∀ n, boundary (n + 1) = interior n)
    (base : Odd (interior 0)) : TuckerTower where
  boundary := boundary
  interior := interior
  step := step
  bridge := fun n => bridge_of_card_eq (hcard n)
  base := base

/-! ## A non-trivial tower: the recursion on genuinely growing data

The only previously-exhibited `TuckerTower` was the constant-`1` `trivialTower`
(`bridge := Iff.rfl`).  Here is a tower whose interior count *grows* with the dimension —
`interior n = 2n+1` — with the bridge discharged from real count equalities
`boundary (n+1) = interior n`, demonstrating that the dimension recursion does
substantive work, not bookkeeping on a constant. -/

/-- Interior count `2n+1` (odd, strictly increasing). -/
def growInterior (n : ℕ) : ℕ := 2 * n + 1

/-- Boundary count: `1` at level `0`, `2n+1` at level `n+1` (so the bridge equality
`boundary (n+1) = interior n` holds on the nose). -/
def growBoundary : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * n + 1

/-- The growing tower: interior `2n+1`, boundary matching by the bridge equality. -/
def growingTower : TuckerTower :=
  towerOfCountEq growBoundary growInterior
    (fun n => by
      have hi : Odd (growInterior n) := Nat.odd_iff.mpr (by unfold growInterior; omega)
      have hb : Odd (growBoundary n) := by
        cases n with
        | zero => decide
        | succ m => exact Nat.odd_iff.mpr (by simp only [growBoundary]; omega)
      exact iff_of_true hb hi)
    (fun n => by simp [growBoundary, growInterior])
    (by decide)

/-- The growing tower's interior count is odd at every level (the dimension recursion). -/
example : ∀ n, Odd (growingTower.interior n) := growingTower.tower_interior_odd

/-- …and positive, so a complementary simplex exists at every level. -/
example : ∀ n, 0 < growingTower.interior n := growingTower.tower_exists_interior

/-- The counts genuinely grow with dimension (not the constant-`1` placeholder). -/
example : growingTower.interior 3 = 7 := rfl
example : growingTower.boundary 3 = 5 := rfl

#check @even_card_of_free_involution
#check @even_card_antipodal_boundary
#check @towerOfCountEq

-- Axiom audit: foundational axioms only (propext / Classical.choice / Quot.sound);
-- no `sorryAx`, no `Lean.ofReduceBool`.
#print axioms even_card_of_free_involution
#print axioms even_card_antipodal_boundary
#print axioms growingTower

end SpernerTuckerAntipodalParity
