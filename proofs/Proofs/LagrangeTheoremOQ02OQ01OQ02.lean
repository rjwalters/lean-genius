import Mathlib

/-
# Sum of stabilizer cardinalities directly from orbit-stabilizer
  (lagrange-theorem-oq-02-oq-01-oq-02)

## Open question

The parent entry (`lagrange-theorem-oq-02-oq-01`) derives Burnside's counting lemma by
the double-counting chain

    Σ_g |Fix(g)| = Σ_x |Stab(x)| = |X/G| · |G|,

routing the second identity through the explicit fixed-point/stabilizer bijection.  This
child establishes the point-side identity on its own,

    Σ_{x ∈ X} |Stab(x)| = |X/G| · |G|,

**directly** from the orbit-stabilizer theorem — i.e. without first proving Burnside.

## Proof

The disjoint union `Σ x : X, Stab(x)` decomposes over orbits.  On the orbit of a
representative `ω.out`, every stabilizer is conjugate to `Stab(ω.out)`
(`stabilizerEquivStabilizerOfOrbitRel`), so the union over that orbit is
`orbit(ω.out) × Stab(ω.out)`, which the orbit-stabilizer equivalence
`orbitProdStabilizerEquivGroup` identifies with `G`.  Summing over the `|X/G|` orbits
gives `(X/G) × G`.  This is exactly the stabilizer half of Mathlib's Burnside bijection
`sigmaFixedByEquivOrbitsProdGroup`, reused here as a standalone equivalence; taking
cardinalities yields the identity.

This mirrors Mathlib's `MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group`, but on
the `Σ_x |Stab(x)|` side rather than the `Σ_g |Fix(g)|` side.

Sorry-free and axiom-free.
-/

open MulAction

namespace LagrangeTheoremOQ02OQ01OQ02

variable {α : Type*} [Group α] {β : Type*} [MulAction α β]

local notation "Ω" => Quotient (orbitRel α β)

/-- **Stabilizer half of the Burnside bijection.** The disjoint union of the stabilizers
`Stab(x)` over all points `x : X` is in bijection with `(X/G) × G`.  This is the
orbit-stabilizer content underlying `Σ_x |Stab(x)| = |X/G| · |G|`; it is the same chain
of equivalences that Mathlib's `sigmaFixedByEquivOrbitsProdGroup` passes through, isolated
from the fixed-point side. -/
noncomputable def sigmaStabilizerEquivOrbitsProdGroup :
    (Σ b : β, stabilizer α b) ≃ Ω × α :=
  calc
    (Σ b : β, stabilizer α b)
        ≃ Σ ωb : Σ ω : Ω, orbit α ω.out, stabilizer α (ωb.2 : β) :=
      (selfEquivSigmaOrbits α β).sigmaCongrLeft'
    _ ≃ Σ ω : Ω, Σ b : orbit α ω.out, stabilizer α (b : β) :=
      Equiv.sigmaAssoc fun (ω : Ω) (b : orbit α ω.out) => stabilizer α (b : β)
    _ ≃ Σ ω : Ω, Σ _ : orbit α ω.out, stabilizer α ω.out :=
      Equiv.sigmaCongrRight fun _ =>
        Equiv.sigmaCongrRight fun ⟨_, hb⟩ => (stabilizerEquivStabilizerOfOrbitRel hb).toEquiv
    _ ≃ Σ ω : Ω, orbit α ω.out × stabilizer α ω.out :=
      Equiv.sigmaCongrRight fun _ => Equiv.sigmaEquivProd _ _
    _ ≃ Σ _ : Ω, α := Equiv.sigmaCongrRight fun ω => orbitProdStabilizerEquivGroup α ω.out
    _ ≃ Ω × α := Equiv.sigmaEquivProd Ω α

/-- **`Σ_x |Stab(x)| = |X/G| · |G|`**, obtained directly from the orbit-stabilizer
theorem (via `sigmaStabilizerEquivOrbitsProdGroup`), without Burnside as an intermediate
step.  Here `|X/G| = Fintype.card Ω` is the number of orbits. -/
theorem sum_card_stabilizer_eq_card_orbits_mul_card_group
    [Fintype β] [∀ b : β, Fintype (stabilizer α b)] [Fintype α] [Fintype Ω] :
    (∑ b : β, Fintype.card (stabilizer α b)) = Fintype.card Ω * Fintype.card α := by
  rw [← Fintype.card_prod, ← Fintype.card_sigma,
    Fintype.card_congr sigmaStabilizerEquivOrbitsProdGroup]

end LagrangeTheoremOQ02OQ01OQ02
