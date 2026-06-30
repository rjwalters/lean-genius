import Mathlib

/-
# Abel–Ruffini: the solvable side of the symmetric-group threshold

The group-theoretic heart of the Abel–Ruffini theorem is the dichotomy

> `Sₙ` is solvable **iff** `n ≤ 4`.

The non-solvable half (`n ≥ 5`) is Mathlib's `Equiv.Perm.fin_5_not_solvable`,
generalized to all `n ≥ 5` in `AbelRuffiniObstructionOQ06.lean`. This file
supplies the **positive** half — the solvable cases — which Mathlib does *not*
package: there is no Mathlib lemma asserting `IsSolvable (Equiv.Perm (Fin n))`
for `n ∈ {3, 4}`.

## What is proved here

* `permSolvable_of_alternatingSolvable` — a reusable **reduction**: `Sₙ` is
  solvable as soon as the alternating group `Aₙ` is, because `Aₙ = ker (sign)` is
  a normal subgroup of `Sₙ` with abelian quotient (`Sₙ / Aₙ ↪ ℤˣ`). This is the
  short exact sequence `1 → Aₙ → Sₙ → ℤˣ` packaged through
  `solvable_of_ker_le_range`.
* `permFinTwo_isSolvable`, `permFinThree_isSolvable` — `S₂` and `S₃` are solvable.
  Both alternating groups here have prime order (`1` and `3`), hence are cyclic,
  hence abelian, hence solvable; the reduction then lifts solvability to the full
  symmetric group.

Combined with the `n ≥ 5` non-solvability, these complete the threshold for every
`n` except the single remaining case `S₄` (whose alternating group `A₄` of order
12 needs the Klein-four normal subgroup `V₄ ⊴ A₄`); that case is isolated in the
companion `AbelRuffiniOQ06Aristotle.lean`.

## Scope

This is the *characteristic-independent core*. The title's characteristic-`p` /
Abhyankar angle (fundamental groups of curves in positive characteristic —
Raynaud/Harbater) is deep, unformalized theory and out of scope.
-/

namespace AbelRuffiniOQ06

open Equiv

/-!
## The reduction `Aₙ solvable ⟹ Sₙ solvable`
-/

/--
**Reduction lemma.** If the alternating group `Aₙ = alternatingGroup (Fin n)` is
solvable, then the full symmetric group `Sₙ = Equiv.Perm (Fin n)` is solvable.

The alternating group is the kernel of the sign homomorphism
`Equiv.Perm.sign : Sₙ →* ℤˣ`, so we have a short exact sequence
`1 → Aₙ → Sₙ → ℤˣ` with abelian (hence solvable) quotient. Solvability of an
extension of a solvable group by a solvable group is `solvable_of_ker_le_range`.
-/
theorem permSolvable_of_alternatingSolvable (n : ℕ)
    [IsSolvable (alternatingGroup (Fin n))] :
    IsSolvable (Equiv.Perm (Fin n)) :=
  solvable_of_ker_le_range (alternatingGroup (Fin n)).subtype Equiv.Perm.sign
    (by rw [Subgroup.range_subtype]; exact alternatingGroup_eq_sign_ker.ge)

/-!
## `A₂` and `A₃` are solvable (prime order ⟹ cyclic ⟹ abelian)
-/

/-- The alternating group `A₃` is cyclic of order `3`, hence solvable. -/
instance alternatingFinThree_isSolvable : IsSolvable (alternatingGroup (Fin 3)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]; rfl
  haveI : IsCyclic (alternatingGroup (Fin 3)) := isCyclic_of_prime_card hcard
  exact isSolvable_of_comm fun a b => (IsCyclic.commutative).comm a b

/-- The alternating group `A₂` is trivial of order `1`, hence solvable. -/
instance alternatingFinTwo_isSolvable : IsSolvable (alternatingGroup (Fin 2)) := by
  have hcard : Fintype.card (alternatingGroup (Fin 2)) = 1 := by
    rw [card_alternatingGroup, Fintype.card_fin]; rfl
  haveI : Subsingleton (alternatingGroup (Fin 2)) := Fintype.card_le_one_iff_subsingleton.mp hcard.le
  infer_instance

/-!
## `S₂` and `S₃` are solvable
-/

/-- `S₂ = Equiv.Perm (Fin 2)` is solvable. -/
theorem permFinTwo_isSolvable : IsSolvable (Equiv.Perm (Fin 2)) :=
  permSolvable_of_alternatingSolvable 2

/-- `S₃ = Equiv.Perm (Fin 3)` is solvable. -/
theorem permFinThree_isSolvable : IsSolvable (Equiv.Perm (Fin 3)) :=
  permSolvable_of_alternatingSolvable 3

end AbelRuffiniOQ06
