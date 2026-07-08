import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

/-!
# Orbit–Stabilizer Without Finiteness — The Bijection and its Cardinal Corollary

## What This Proves

This file answers `oq-03` of the parent `lagrange-theorem-oq-02` (the
orbit–stabilizer family).  The parent, and the `Nat.card` sibling
`lagrange-theorem-oq-02-oq-02-oq-01-oq-01-oq-01-oq-01`, phrase orbit–stabilizer
over `Nat.card`, which is **`0` on infinite types**.  Over `Nat.card` the
identity `#(orbit) = [G : stabilizer]` still holds unconditionally (the bijection
is finiteness-free), but the *product* form `#(orbit) · #(stabilizer) = #G`
degenerates to `0 = 0` as soon as anything in sight is infinite, and the
statement `#(orbit) = #(G ⧸ stabilizer)` carries no information when the orbit is
infinite.

This file gives the **honest infinite-general** formulation over `Cardinal.mk`,
where every identity retains its content for infinite groups, orbits, and
stabilizers:

* the orbit–stabilizer **bijection** `orbit G x ≃ G ⧸ stabilizer G x`, together
  with the explicit coset characterization of when two group elements send `x` to
  the same point (`g₁ • x = g₂ • x ↔ g₁⁻¹ g₂ ∈ stabilizer ↔ ↑g₁ = ↑g₂` in the
  coset space);
* the **cardinal** identity `#(orbit G x) = #(G ⧸ stabilizer G x)`, a genuine
  equality of (possibly infinite) cardinals;
* the **cardinal orbit–stabilizer product** `#(orbit G x) · #(stabilizer G x) = #G`
  for an *arbitrary* group, obtained from the cardinal form of Lagrange's theorem
  `#G = #(G ⧸ H) · #H` (`Subgroup.groupEquivQuotientProdSubgroup`), and which — unlike
  its `Nat.card` shadow — stays true and informative in the infinite setting;
* the **finite specialization**, recovering the classical product formula over
  `Nat.card`;
* the **transitive** case, where the orbit is everything and one reads off
  `#X = #(G ⧸ stabilizer G x)`.

The mathematical point: finiteness plays no role in orbit–stabilizer.  What is
really going on is a bijection, and taking cardinalities of a bijection is
finiteness-free.  Working over `Cardinal.mk` rather than `Nat.card` is what makes
that content survive into the infinite regime.

## Status
- [x] Coset characterization of equal images (`same_image_iff_*`) — `0` sorries
- [x] Cardinal orbit–stabilizer bijection and cardinal identity — `0` sorries
- [x] Cardinal Lagrange `#G = #(G ⧸ H) · #H` and cardinal orbit–stabilizer product
- [x] Finite `Nat.card` specialization
- [x] Transitive-action corollary
- 0 axioms beyond Mathlib's foundational `propext`/`Classical.choice`/`Quot.sound`.

## Mathlib Dependencies
- `Mathlib.GroupTheory.GroupAction.Quotient` : `MulAction.orbitEquivQuotientStabilizer`
- `Mathlib.GroupTheory.Coset.Basic` : `Subgroup.groupEquivQuotientProdSubgroup`,
  `QuotientGroup.eq`
- `Mathlib.SetTheory.Cardinal.Finite` : `Cardinal.mk_congr`, `Cardinal.mk_prod`,
  `Cardinal.lift_id`, `Nat.card_congr`
-/

namespace OrbitStabilizerCardinal

open MulAction Cardinal

universe u

variable {G : Type u} [Group G] {X : Type u} [MulAction G X]

/-! ### The coset characterization of the bijection

The heart of orbit–stabilizer is a *pointwise* fact with no finiteness anywhere:
two group elements move `x` to the same place exactly when they lie in the same
left coset of the stabilizer.  This is the map `g • x ↦ g · stabilizer` being
well defined and injective. -/

/-- Two elements send `x` to the same point iff `g₁⁻¹ g₂` stabilizes `x`. -/
theorem same_image_iff_mem_stabilizer (x : X) (g₁ g₂ : G) :
    g₁ • x = g₂ • x ↔ g₁⁻¹ * g₂ ∈ stabilizer G x := by
  rw [mem_stabilizer_iff, mul_smul]
  constructor
  · intro h
    rw [← h, ← mul_smul, inv_mul_cancel, one_smul]
  · intro h
    calc g₁ • x = g₁ • (g₁⁻¹ • (g₂ • x)) := by rw [h]
      _ = g₂ • x := by rw [← mul_smul, mul_inv_cancel, one_smul]

/-- Two elements send `x` to the same point iff they represent the same coset in
`G ⧸ stabilizer G x`.  This is precisely the statement that
`g • x ↦ (g : G ⧸ stabilizer G x)` is a well-defined injection of the orbit into
the coset space — the finiteness-free content of orbit–stabilizer. -/
theorem same_image_iff_coset_eq (x : X) (g₁ g₂ : G) :
    g₁ • x = g₂ • x ↔ (g₁ : G ⧸ stabilizer G x) = (g₂ : G ⧸ stabilizer G x) := by
  rw [same_image_iff_mem_stabilizer, ← QuotientGroup.eq]

/-! ### The bijection and the cardinal identity -/

/-- **Orbit–stabilizer bijection, no finiteness hypothesis.**  This is Mathlib's
`orbitEquivQuotientStabilizer`, restated here as the central object of this file:
a genuine bijection between the orbit and the coset space, valid for *any* group
action. -/
noncomputable def orbitEquivQuotient (x : X) :
    orbit G x ≃ G ⧸ stabilizer G x :=
  orbitEquivQuotientStabilizer G x

/-- **Cardinal orbit–stabilizer.**  `#(orbit G x) = #(G ⧸ stabilizer G x)` as an
equality of cardinals, for an arbitrary (possibly infinite) group.  Unlike the
`Nat.card` version, this retains its content when the orbit is infinite. -/
theorem mk_orbit_eq_mk_quotient_stabilizer (x : X) :
    #(orbit G x) = #(G ⧸ stabilizer G x) :=
  mk_congr (orbitEquivQuotientStabilizer G x)

/-! ### Cardinal Lagrange and the cardinal orbit–stabilizer product -/

/-- **Cardinal form of Lagrange's theorem.**  `#G = #(G ⧸ H) · #H` for an
arbitrary subgroup `H` of an arbitrary group `G`.  This is the cardinal image of
the bijection `G ≃ (G ⧸ H) × H` (`Subgroup.groupEquivQuotientProdSubgroup`), and
holds for infinite groups, where the `Nat.card` product formula collapses to
`0 = 0`. -/
theorem mk_eq_mk_quotient_mul_mk (H : Subgroup G) :
    #G = #(G ⧸ H) * #H := by
  rw [mk_congr (Subgroup.groupEquivQuotientProdSubgroup (s := H)), mk_prod,
    lift_id, lift_id]

/-- **Cardinal orbit–stabilizer product.**  `#(orbit G x) · #(stabilizer G x) = #G`
for an arbitrary group action.  This is the infinite-general product form: it is
obtained by feeding the cardinal identity `#(orbit) = #(G ⧸ stabilizer)` into the
cardinal Lagrange identity, and — unlike `Nat.card (orbit) · Nat.card (stabilizer)
= Nat.card G` — remains a true, non-degenerate statement when the group is
infinite. -/
theorem mk_orbit_mul_mk_stabilizer (x : X) :
    #(orbit G x) * #(stabilizer G x) = #G := by
  rw [mk_orbit_eq_mk_quotient_stabilizer, ← mk_eq_mk_quotient_mul_mk]

/-! ### Finite specialization -/

/-- **Finite specialization.**  For a finite group the cardinal product formula
descends to the classical natural-number identity
`#(orbit) · #(stabilizer) = #G` over `Nat.card`, recovering the statement of the
parent gallery entry. -/
theorem card_orbit_mul_card_stabilizer [Finite G] (x : X) :
    Nat.card (orbit G x) * Nat.card (stabilizer G x) = Nat.card G := by
  rw [← Nat.card_prod, Nat.card_congr (orbitProdStabilizerEquivGroup G x)]

/-! ### Transitive actions -/

/-- **Transitive case.**  When the action is (pre)transitive the orbit of any
point is all of `X`, so the cardinal identity reads
`#X = #(G ⧸ stabilizer G x)`: the size of the space equals the index of any point
stabilizer, with no finiteness assumption. -/
theorem mk_eq_mk_quotient_stabilizer_of_pretransitive [MulAction.IsPretransitive G X]
    (x : X) : #X = #(G ⧸ stabilizer G x) := by
  have horbit : orbit G x = Set.univ := by
    ext y
    simp only [Set.mem_univ, iff_true, MulAction.mem_orbit_iff]
    exact MulAction.exists_smul_eq G x y
  rw [← mk_orbit_eq_mk_quotient_stabilizer, horbit, mk_univ]

#check @same_image_iff_mem_stabilizer
#check @same_image_iff_coset_eq
#check @mk_orbit_eq_mk_quotient_stabilizer
#check @mk_eq_mk_quotient_mul_mk
#check @mk_orbit_mul_mk_stabilizer
#check @card_orbit_mul_card_stabilizer
#check @mk_eq_mk_quotient_stabilizer_of_pretransitive

end OrbitStabilizerCardinal
