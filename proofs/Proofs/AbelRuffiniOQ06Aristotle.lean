import Mathlib

/-
# Abel–Ruffini OQ-06 — companion: the remaining S₄ / A₄ case

The verified file `AbelRuffiniOQ06.lean` proves the reduction
`Aₙ solvable ⟹ Sₙ solvable` and settles `S₂`, `S₃`. The only symmetric group
below the n ≥ 5 non-solvability threshold not yet closed is `S₄`, which by the
reduction needs solvability of the alternating group `A₄` (order 12).

`A₄` is solvable because it has the Klein-four normal subgroup
`V₄ = {1, (12)(34), (13)(24), (14)(23)}` with abelian quotient `A₄ / V₄ ≅ ℤ/3`.
Equivalently, its derived series is `A₄ ⊳ V₄ ⊳ 1`.

This companion isolates that single fact and discharges it via the short exact
sequence `1 → V₄ → A₄ → A₄/V₄ → 1`. The membership/normality/commutativity
checks are finite and settled by `decide` / `native_decide`.
-/

namespace AbelRuffiniOQ06Aristotle

open Equiv

/-- Reduction (proved in the verified file, restated here standalone): if the
alternating group is solvable then the full symmetric group is solvable. -/
theorem permSolvable_of_alternatingSolvable (n : ℕ)
    [IsSolvable (alternatingGroup (Fin n))] :
    IsSolvable (Equiv.Perm (Fin n)) :=
  solvable_of_ker_le_range (alternatingGroup (Fin n)).subtype Equiv.Perm.sign
    (by rw [Subgroup.range_subtype]; exact alternatingGroup_eq_sign_ker.ge)

/-- The Klein four-group `V₄` as a subgroup of `A₄`:
`V₄ = {e, (12)(34), (13)(24), (14)(23)}` — the even double transpositions,
characterized as the involutions (elements squaring to `1`). -/
private def kleinFour : Subgroup (alternatingGroup (Fin 4)) where
  carrier := {x | x.1 * x.1 = 1}
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

/-- Decidable membership in `V₄`. -/
private instance : DecidablePred (· ∈ kleinFour) := fun x =>
  if h : x.1 * x.1 = 1 then isTrue h else isFalse h

/-- `V₄` is normal in `A₄`. -/
private instance kleinFour_normal : kleinFour.Normal where
  conj_mem := by native_decide

/-- `V₄` is commutative (all non-identity elements have order 2). -/
private theorem kleinFour_comm : ∀ (a b : kleinFour), a * b = b * a := by native_decide

/-- `V₄` is solvable, being abelian. -/
private instance : IsSolvable kleinFour := isSolvable_of_comm kleinFour_comm

/-- The quotient `A₄ / V₄` is commutative (it is cyclic of order 3). -/
private theorem quotient_kleinFour_comm :
    ∀ (a b : alternatingGroup (Fin 4) ⧸ kleinFour), a * b = b * a := by native_decide

/-- `A₄ / V₄` is solvable, being abelian. -/
private instance : IsSolvable (alternatingGroup (Fin 4) ⧸ kleinFour) :=
  isSolvable_of_comm quotient_kleinFour_comm

/-- The alternating group `A₄` is solvable (derived series `A₄ ⊳ V₄ ⊳ 1`),
via the short exact sequence `1 → V₄ → A₄ → A₄/V₄ → 1` with both ends solvable. -/
theorem alternatingFinFour_isSolvable : IsSolvable (alternatingGroup (Fin 4)) :=
  solvable_of_ker_le_range kleinFour.subtype (QuotientGroup.mk' kleinFour)
    (fun x hx => by
      rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
      exact ⟨⟨x, hx⟩, rfl⟩)

/-- `S₄ = Equiv.Perm (Fin 4)` is solvable. -/
theorem permFinFour_isSolvable : IsSolvable (Equiv.Perm (Fin 4)) := by
  haveI := alternatingFinFour_isSolvable
  exact permSolvable_of_alternatingSolvable 4

end AbelRuffiniOQ06Aristotle
