import Proofs.ThreePlaceIdentity

/-
# Three-Place Identity — The Role of Foundation in the Round-Trip

## The Question (OQ-01)
The base file `ThreePlaceIdentity.lean` proves the Round-Trip Theorem
(`ThreePlaceIdentity.roundtrip`) *under the assumption* that the membership
relation satisfies the Foundation (Regularity) axiom `∀ x, ¬ mem x x`. The
prose there asserts Foundation is "essential" and that "without it, the
round-trip breaks down" — but this is only *asserted*, never proved.

OQ-01 makes that claim precise:

  1. Is Foundation actually **necessary**, or merely sufficient?
  2. What *exactly* happens to the round-trip when Foundation fails?

## Answer
We give a **sharp** characterization. Let `D` denote the derived membership
obtained by going `mem ─D2→ identity ─D1→ mem'`. Then for every viewpoint `x`
and element `y`:

      D(mem) y x  ↔  ¬ (mem y x ↔ mem x x)

From this single identity everything follows:

  * **Sufficiency (recovers `roundtrip`)**: if `¬ mem x x` then `D y x ↔ mem y x`.
  * **Necessity**: the round-trip holds at viewpoint `x` *for all* `y`
    **iff** Foundation holds at `x` (`¬ mem x x`). So Foundation is exactly
    the right hypothesis — not stronger than needed.
  * **Inversion**: if `mem x x` (Foundation fails at `x`), the round-trip does
    not merely "break"; it **inverts**: `D y x ↔ ¬ mem y x`.
  * **Self-regularization**: the derived membership `D(mem)` *always* satisfies
    Foundation, no matter how badly `mem` violates it. Hence `D` is an
    idempotent "regularization": `D(D(mem)) = D(mem)`.

Everything is pure classical propositional logic — 0 axioms, 0 sorries — and
reuses the definitions from `ThreePlaceIdentity.lean` unchanged.

## References
- T. Etter, "Three-place Identity," Boundary Institute, 2006.
- See `ThreePlaceIdentity.lean` (universality) and `ThreePlaceIdentityOQ02.lean`
  (stereo equality) for the surrounding development.
-/

namespace ThreePlaceIdentity.OQ01

open ThreePlaceIdentity

variable {U : Type}

/-- The derived membership relation: start from a raw membership `mem`, build the
    relative identity via bridge **D2**, then read membership back off via bridge
    **D1**. This is the composite `D2 ; D1` whose fixed points the Round-Trip
    Theorem studies. No Foundation hypothesis is imposed on `mem`. -/
def derivedMem (mem : U → U → Prop) (y x : U) : Prop :=
  MemFromId (IdFromMem.toRelativeIdentity mem) y x

-- ═══════════════════════════════════════════════════════════════
-- PART I: The Sharp Round-Trip Identity
-- ═══════════════════════════════════════════════════════════════

/-- **Sharp Round-Trip Identity.** Unconditionally (no Foundation assumed),

      `derivedMem mem y x  ↔  ¬ (mem y x ↔ mem x x)`.

    Reading: `y` is a derived-member of `x` exactly when `y` and `x` have
    *different* membership-status in `x`. The whole behaviour of the round-trip
    is governed by the single bit `mem x x`. -/
theorem derivedMem_iff (mem : U → U → Prop) (y x : U) :
    derivedMem mem y x ↔ ¬ (mem y x ↔ mem x x) := by
  unfold derivedMem MemFromId IdFromMem.toRelativeIdentity IdFromMem
  tauto

/-- The derived membership relation **always** satisfies Foundation, regardless of
    whether the input `mem` does. (`derivedMem mem x x` is `¬ Id x x x`, and the
    relative identity is reflexive, so `Id x x x` always holds.) Thus the
    composite bridge `D2 ; D1` lands inside the well-founded membership relations:
    it is a *regularization* operator. -/
theorem derivedMem_irrefl (mem : U → U → Prop) (x : U) :
    ¬ derivedMem mem x x :=
  MemFromId.irrefl (IdFromMem.toRelativeIdentity mem) x

-- ═══════════════════════════════════════════════════════════════
-- PART II: Foundation is Sufficient (recovering `roundtrip`)
-- ═══════════════════════════════════════════════════════════════

/-- **Sufficiency.** If Foundation holds at the viewpoint `x` (`¬ mem x x`),
    the round-trip recovers membership exactly: `derivedMem mem y x ↔ mem y x`.
    This is the pointwise content of `ThreePlaceIdentity.roundtrip`, here proved
    from the sharp identity without needing a global `WellFoundedMembership`. -/
theorem derivedMem_of_foundation (mem : U → U → Prop) (y x : U)
    (hx : ¬ mem x x) : derivedMem mem y x ↔ mem y x := by
  rw [derivedMem_iff]
  simp [hx]

-- ═══════════════════════════════════════════════════════════════
-- PART III: Foundation is Necessary (the converse)
-- ═══════════════════════════════════════════════════════════════

/-- **Necessity / sharpness.** The round-trip holds at viewpoint `x` *for every*
    `y` **iff** Foundation holds at `x`. So Foundation is not just sufficient —
    it is exactly the hypothesis the round-trip requires. -/
theorem roundtrip_iff_foundation (mem : U → U → Prop) (x : U) :
    (∀ y, derivedMem mem y x ↔ mem y x) ↔ ¬ mem x x := by
  constructor
  · -- If the round-trip holds for all y, instantiate at y := x. The derived
    -- relation is always irreflexive, so `mem x x` must be False.
    intro h hxx
    exact (derivedMem_irrefl mem x) ((h x).mpr hxx)
  · -- Foundation at x ⇒ round-trip at x for all y.
    intro hx y
    exact derivedMem_of_foundation mem y x hx

-- ═══════════════════════════════════════════════════════════════
-- PART IV: Without Foundation, the Round-Trip Inverts
-- ═══════════════════════════════════════════════════════════════

/-- **Inversion.** When Foundation *fails* at `x` (`mem x x` holds), the round-trip
    does not merely break — it flips membership to its negation:
    `derivedMem mem y x ↔ ¬ mem y x`. -/
theorem derivedMem_of_not_foundation (mem : U → U → Prop) (y x : U)
    (hx : mem x x) : derivedMem mem y x ↔ ¬ mem y x := by
  rw [derivedMem_iff]
  simp [hx]

/-- A concrete, non-vacuous witness that the round-trip genuinely fails without
    Foundation: take `U = Unit` with the *total* membership relation. Here
    `mem x x` always holds, and the derived membership is everywhere `False`,
    so it disagrees with the original `mem` (which is everywhere `True`). -/
theorem roundtrip_fails_example :
    ∃ (mem : Unit → Unit → Prop) (y x : Unit),
      ¬ (derivedMem mem y x ↔ mem y x) := by
  refine ⟨fun _ _ => True, (), (), ?_⟩
  rw [derivedMem_of_not_foundation (fun _ _ => True) () () trivial]
  simp

/-- **Global sharpness.** Quantifying over every viewpoint, the round-trip
    recovers `mem` everywhere **iff** `mem` satisfies Foundation everywhere.
    The right-hand side is *exactly* the `WellFoundedMembership.foundation`
    field the base file's `roundtrip` assumes — so this closes the loop: the
    global hypothesis of `ThreePlaceIdentity.roundtrip` is not merely sufficient
    but necessary. -/
theorem global_roundtrip_iff_foundation (mem : U → U → Prop) :
    (∀ x y, derivedMem mem y x ↔ mem y x) ↔ (∀ x, ¬ mem x x) := by
  constructor
  · intro h x
    exact (roundtrip_iff_foundation mem x).mp (fun y => h x y)
  · intro hx x y
    exact derivedMem_of_foundation mem y x (hx x)

-- ═══════════════════════════════════════════════════════════════
-- PART V: Self-Regularization and Idempotence
-- ═══════════════════════════════════════════════════════════════

/-- Package the derived membership as a `WellFoundedMembership`, using the fact
    that it is always irreflexive. This makes the regularization explicit. -/
def derivedWFM (mem : U → U → Prop) : WellFoundedMembership U where
  mem := derivedMem mem
  foundation := derivedMem_irrefl mem

/-- **Idempotence.** Because `derivedMem mem` is already well-founded, applying
    the round-trip a second time changes nothing: the derivation is an idempotent
    projection onto well-founded membership relations. -/
theorem derivedMem_idempotent (mem : U → U → Prop) (y x : U) :
    derivedMem (derivedMem mem) y x ↔ derivedMem mem y x :=
  roundtrip (derivedWFM mem) y x

-- ═══════════════════════════════════════════════════════════════
-- Final verification
-- ═══════════════════════════════════════════════════════════════

#check @derivedMem_iff
#check @roundtrip_iff_foundation
#check @global_roundtrip_iff_foundation
#check @derivedMem_of_not_foundation
#check @derivedMem_idempotent

end ThreePlaceIdentity.OQ01
