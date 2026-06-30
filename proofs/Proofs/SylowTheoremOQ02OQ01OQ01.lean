/-
# Sylow Subgroups of a Nilpotent Group are Characteristic

OQ-02-OQ-01-OQ-01 follow-up to `sylow-theorem-oq-02-oq-01`
(`SylowTheoremOQ02OQ01Nilpotent.lean`).

The parent entry proved the structural headline

  `IsNilpotent G  ↔  ∀ p P, (P : Subgroup G).Normal`
  `IsNilpotent G  ↔  ∀ p, #(Sylow p G) = 1`

for a finite group `G`: nilpotency is exactly the simultaneous *normality*
(equivalently, *uniqueness*) of all Sylow subgroups.

This leaf sharpens "normal" to "characteristic".  In general a normal subgroup
need not be characteristic — characteristic (invariance under *every*
automorphism) is strictly stronger than normal (invariance under inner
automorphisms only).  **For a Sylow subgroup the two notions coincide**, and the
reason is uniqueness: a normal Sylow `p`-subgroup is the *only* Sylow
`p`-subgroup, and every automorphism permutes the Sylow `p`-subgroups, so it must
fix the unique one.  This is Mathlib's `Sylow.characteristic_of_normal`.

Packaging that per-prime coincidence with the parent's nilpotency criteria gives
a four-way characterization with "characteristic" sitting between "normal" and
"nilpotent", and the explicit automorphism-invariance statement
`(P : Subgroup G).map φ = P` for every `φ : G ≃* G`.

## Main Results

- `sylow_characteristic_iff_normal` :
    for a Sylow `p`-subgroup of a finite group, `Characteristic ↔ Normal`
- `sylow_characteristic_of_nilpotent` :
    nilpotent ⇒ every Sylow `p`-subgroup is characteristic
- `sylow_map_aut_eq_of_nilpotent` :
    nilpotent ⇒ every Sylow `p`-subgroup is fixed setwise by every `φ : G ≃* G`
- `nilpotent_of_forall_sylow_characteristic` :
    all Sylow subgroups characteristic ⇒ nilpotent
- `nilpotent_iff_forall_sylow_characteristic` :
    the characteristic-tier biconditional
- `nilpotent_tfae` :
    nilpotent ⟺ all Sylow normal ⟺ all Sylow characteristic ⟺ all Sylow counts one

The file is self-contained: the parent's `nilpotent ↔ all Sylow normal` and
`nilpotent ↔ all counts one` are re-derived from Mathlib's nilpotency TFAE rather
than imported.

## Tags
group-theory, sylow, nilpotent, finite-groups, characteristic-subgroup, automorphism
-/

import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.Sylow
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Tactic

namespace SylowCharacteristic

variable {G : Type*} [Group G] [Finite G]

/-- Mathlib's nilpotency TFAE, slice `(1) ↔ (4)`: a finite group is nilpotent iff
every Sylow `p`-subgroup (for every prime `p`) is normal.  Re-stated here so the
file is self-contained. -/
theorem nilpotent_iff_forall_sylow_normal :
    Group.IsNilpotent G ↔
      ∀ (p : ℕ) (_hp : Fact p.Prime) (P : Sylow p G), (P : Subgroup G).Normal :=
  (isNilpotent_of_finite_tfae (G := G)).out 0 3

/-- **Counting characterization** (re-derived from the parent).  A finite group is
nilpotent iff each Sylow count is one. -/
theorem nilpotent_iff_forall_card_sylow_eq_one :
    Group.IsNilpotent G ↔
      ∀ (p : ℕ) (_hp : Fact p.Prime), Nat.card (Sylow p G) = 1 := by
  rw [nilpotent_iff_forall_sylow_normal]
  constructor
  · intro h p hp
    haveI := hp
    obtain ⟨P⟩ := (Sylow.nonempty : Nonempty (Sylow p G))
    haveI := Sylow.unique_of_normal P (h p hp P)
    exact Nat.card_unique
  · intro h p hp P
    haveI := hp
    have hcard : Nat.card (Sylow p G) = 1 := h p hp
    haveI : Subsingleton (Sylow p G) := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact Sylow.normal_of_subsingleton P

/-- **Per-prime coincidence.**  For a Sylow `p`-subgroup of a finite group, being
*characteristic* is equivalent to being *normal*.

The forward direction is the generic fact that characteristic subgroups are
normal.  The reverse — the interesting one — is `Sylow.characteristic_of_normal`:
a normal Sylow subgroup is the unique Sylow `p`-subgroup, and uniqueness forces
invariance under every automorphism. -/
theorem sylow_characteristic_iff_normal (p : ℕ) [Fact p.Prime] (P : Sylow p G) :
    (P : Subgroup G).Characteristic ↔ (P : Subgroup G).Normal :=
  ⟨fun h => by haveI := h; infer_instance,
   fun h => Sylow.characteristic_of_normal P h⟩

/-- In a finite nilpotent group every Sylow `p`-subgroup is characteristic. -/
theorem sylow_characteristic_of_nilpotent (h : Group.IsNilpotent G)
    (p : ℕ) [Fact p.Prime] (P : Sylow p G) : (P : Subgroup G).Characteristic :=
  Sylow.characteristic_of_normal P
    (nilpotent_iff_forall_sylow_normal.mp h p ‹Fact p.Prime› P)

/-- **Explicit automorphism-invariance.**  In a finite nilpotent group every
Sylow `p`-subgroup is fixed setwise by every automorphism of `G`. -/
theorem sylow_map_aut_eq_of_nilpotent (h : Group.IsNilpotent G)
    (p : ℕ) [Fact p.Prime] (P : Sylow p G) (φ : G ≃* G) :
    (P : Subgroup G).map φ.toMonoidHom = (P : Subgroup G) :=
  Subgroup.characteristic_iff_map_eq.mp (sylow_characteristic_of_nilpotent h p P) φ

/-- Converse direction: if every Sylow subgroup is characteristic then the group
is nilpotent (characteristic ⇒ normal, then apply the normality criterion). -/
theorem nilpotent_of_forall_sylow_characteristic
    (h : ∀ (p : ℕ) (_hp : Fact p.Prime) (P : Sylow p G),
        (P : Subgroup G).Characteristic) :
    Group.IsNilpotent G :=
  nilpotent_iff_forall_sylow_normal.mpr fun p hp P => by
    haveI := h p hp P; infer_instance

/-- **Characteristic-tier characterization of nilpotency.**  A finite group is
nilpotent iff *every* Sylow `p`-subgroup is characteristic. -/
theorem nilpotent_iff_forall_sylow_characteristic :
    Group.IsNilpotent G ↔
      ∀ (p : ℕ) (_hp : Fact p.Prime) (P : Sylow p G),
        (P : Subgroup G).Characteristic :=
  ⟨fun h p _hp P => sylow_characteristic_of_nilpotent h p P,
   nilpotent_of_forall_sylow_characteristic⟩

/-- **Four-way characterization.**  For a finite group `G` the following are
equivalent:
1. `G` is nilpotent;
2. every Sylow `p`-subgroup is normal;
3. every Sylow `p`-subgroup is characteristic;
4. every Sylow count `#(Sylow p G)` equals one.

The new content over the parent is the "characteristic" tier (3), which sits
strictly between (2) and the global structure but collapses onto (2) precisely
because Sylow subgroups are unique when normal. -/
theorem nilpotent_tfae :
    [ Group.IsNilpotent G,
      ∀ (p : ℕ) (_hp : Fact p.Prime) (P : Sylow p G), (P : Subgroup G).Normal,
      ∀ (p : ℕ) (_hp : Fact p.Prime) (P : Sylow p G), (P : Subgroup G).Characteristic,
      ∀ (p : ℕ) (_hp : Fact p.Prime), Nat.card (Sylow p G) = 1 ].TFAE := by
  tfae_have 1 ↔ 2 := nilpotent_iff_forall_sylow_normal
  tfae_have 1 ↔ 3 := nilpotent_iff_forall_sylow_characteristic
  tfae_have 1 ↔ 4 := nilpotent_iff_forall_card_sylow_eq_one
  tfae_finish

end SylowCharacteristic
