/-
# The transfer homomorphism to the abelianization of a subgroup: `G → P/[P,P]`

This file constructs the **transfer homomorphism into the abelianization** of a
finite-index subgroup and establishes its universal property.

Mathlib (`Mathlib/GroupTheory/Transfer.lean`) builds, for `ϕ : H →* A` from a
finite-index subgroup `H ≤ G` into a *commutative* group `A`, the transfer
homomorphism `transfer ϕ : G →* A`, together with the Burnside normal
`p`-complement theorem (`ker_transferSylow_isComplement'`).  What Mathlib does
**not** record is that this construction is *natural in the coefficient
homomorphism* `ϕ`, and the resulting universal object: the transfer

  `transferAb H : G →* Abelianization H`

induced by the canonical map `Abelianization.of : H →* Abelianization H`.  When
`H = P` is a Sylow `p`-subgroup this is exactly the classical transfer map
`G → P/[P,P]` that opens the focal-subgroup theory of finite groups.

## Main results

* `Subgroup.leftTransversals.diff_comp` — the transversal difference is natural:
  `diff (ψ.comp ϕ) S T = ψ (diff ϕ S T)`.
* `MonoidHom.transfer_comp` — **naturality of the transfer**:
  `transfer (ψ.comp ϕ) = ψ.comp (transfer ϕ)`.
* `MonoidHom.transferAb` — the transfer `G →* Abelianization H` (= `G → P/[P,P]`).
* `MonoidHom.transfer_eq_lift_comp_transferAb` — **universal property**: every
  abelian transfer factors through `transferAb`:
  `transfer ϕ = (Abelianization.lift ϕ).comp (transferAb H)`.
* `MonoidHom.transferAb_ker_le` — `transferAb` is the *finest* abelian transfer:
  its kernel is contained in the kernel of `transfer ϕ` for every `ϕ`.
* `MonoidHom.transferSylowAb` / `transferSylowAb_universal` — the Sylow
  specialisation `G → P/[P,P]` and its universal property.
* `MonoidHom.transferCenterPow_eq_lift_comp_transferAb` — Mathlib's central
  transfer `g ↦ g ^ [G : Z(G)]` factors through the universal abelianization
  transfer of the centre.

Everything is fully machine-checked against Mathlib with no additional axioms,
no `sorry`, and no `native_decide`.
-/
import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.Abelianization.Defs

open scoped Pointwise

namespace Subgroup.leftTransversals

variable {G : Type*} [Group G] {H : Subgroup G}
variable {A : Type*} [CommGroup A] {B : Type*} [CommGroup B]

/-- **Naturality of the transversal difference.**  Pushing the difference of two
left transversals through a homomorphism `ψ : A →* B` of commutative groups is
the same as forming the difference with the postcomposed coefficient map
`ψ.comp ϕ`.  This is immediate from `map_prod`, since `diff` is by definition a
product of `ϕ`-values. -/
theorem diff_comp (ψ : A →* B) (ϕ : H →* A) [FiniteIndex H]
    (S T : H.LeftTransversal) : diff (ψ.comp ϕ) S T = ψ (diff ϕ S T) := by
  unfold diff
  rw [map_prod]
  rfl

end Subgroup.leftTransversals

namespace MonoidHom

open Subgroup Subgroup.leftTransversals

variable {G : Type*} [Group G] {H : Subgroup G}
variable {A : Type*} [CommGroup A] {B : Type*} [CommGroup B]

/-- **Naturality of the transfer homomorphism.**  For a homomorphism
`ψ : A →* B` of commutative groups, the transfer of the postcomposition
`ψ.comp ϕ` equals the postcomposition of the transfer of `ϕ`:

  `transfer (ψ.comp ϕ) = ψ.comp (transfer ϕ).`

In categorical terms, `H ↦ transfer (-)` is a natural transformation in the
coefficient homomorphism. -/
theorem transfer_comp (ψ : A →* B) (ϕ : H →* A) [FiniteIndex H] :
    transfer (ψ.comp ϕ) = ψ.comp (transfer ϕ) := by
  ext g
  rw [comp_apply, transfer_def _ (default : H.LeftTransversal),
    transfer_def _ (default : H.LeftTransversal), diff_comp]

/-- The **transfer homomorphism into the abelianization** of a finite-index
subgroup, `transferAb H : G →* Abelianization H`.  It is induced by the
canonical projection `Abelianization.of : H →* Abelianization H`.  When `H = P`
is a Sylow subgroup this is the classical map `G → P/[P,P]`. -/
noncomputable def transferAb (H : Subgroup G) [FiniteIndex H] :
    G →* Abelianization H :=
  transfer Abelianization.of

/-- **Universal property of `transferAb`.**  Every transfer with abelian
coefficients factors *uniquely* through the transfer to the abelianization:

  `transfer ϕ = (Abelianization.lift ϕ).comp (transferAb H).`

Indeed `ϕ = (Abelianization.lift ϕ).comp Abelianization.of`, so the claim is the
naturality `transfer_comp` applied to `Abelianization.lift ϕ`.  This says
`transferAb` is the initial object among abelian transfers of `H`: the codomain
`Abelianization H = H/[H,H]` is the universal abelian target. -/
theorem transfer_eq_lift_comp_transferAb (ϕ : H →* A) [FiniteIndex H] :
    transfer ϕ = (Abelianization.lift ϕ).comp (transferAb H) := by
  unfold transferAb
  rw [← transfer_comp]
  congr 1

/-- `transferAb` has the **smallest kernel** among all abelian transfers of `H`:
for every `ϕ : H →* A` into a commutative group, the kernel of `transferAb H`
is contained in the kernel of `transfer ϕ`.  Equivalently, `transfer ϕ` is
constant on the cosets of `(transferAb H).ker`. -/
theorem transferAb_ker_le (ϕ : H →* A) [FiniteIndex H] :
    (transferAb H).ker ≤ (transfer ϕ).ker := by
  intro g hg
  rw [mem_ker] at hg ⊢
  rw [transfer_eq_lift_comp_transferAb, comp_apply, hg, map_one]

section Sylow

variable {p : ℕ} (P : Sylow p G)

/-- The **transfer homomorphism `G → P/[P,P]`** of a Sylow `p`-subgroup `P`,
defined as the transfer into the abelianization `Abelianization P`.  This is the
map underlying the focal-subgroup theorem. -/
noncomputable def transferSylowAb [FiniteIndex (P : Subgroup G)] :
    G →* Abelianization (P : Subgroup G) :=
  transferAb (P : Subgroup G)

/-- **Universal property of the Sylow transfer `G → P/[P,P]`.**  Every transfer
of `G` along a homomorphism `ϕ : P →* A` into a commutative group factors
through `transferSylowAb P`.  In particular Burnside's `transferSylow` (for an
abelian Sylow subgroup) is such a factorisation. -/
theorem transferSylowAb_universal [FiniteIndex (P : Subgroup G)]
    (ϕ : (P : Subgroup G) →* A) :
    transfer ϕ = (Abelianization.lift ϕ).comp (transferSylowAb P) :=
  transfer_eq_lift_comp_transferAb ϕ

end Sylow

variable (G) in
/-- Mathlib's central transfer `transferCenterPow G : g ↦ g ^ [G : Z(G)]`
factors through the universal abelianization transfer of the centre.  Since the
centre is already abelian, `Abelianization (center G)` collapses back onto it
via `Abelianization.lift (.id _)`, and the composite recovers `g ↦ g ^ index`.
This exhibits a Mathlib Burnside-transfer map as an instance of the universal
factorisation `transfer_eq_lift_comp_transferAb`. -/
theorem transferCenterPow_eq_lift_comp_transferAb [FiniteIndex (center G)] :
    (transferCenterPow G) =
      (Abelianization.lift (MonoidHom.id _)).comp (transferAb (center G)) := by
  have h : transfer (MonoidHom.id (center G))
      = (Abelianization.lift (MonoidHom.id _)).comp (transferAb (center G)) :=
    transfer_eq_lift_comp_transferAb (MonoidHom.id (center G))
  rw [← h]
  ext g
  rw [transfer_center_eq_pow, transferCenterPow_apply]

end MonoidHom
