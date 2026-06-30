import Mathlib
import Proofs.AbelRuffiniOQ06

/-
# Abel–Ruffini: closing the threshold at S₄ — the full equivalence Sₙ solvable ⟺ n ≤ 4
  (abel-ruffini-oq-06-oq-01)

The parent entry `Proofs.AbelRuffiniOQ06` supplies the *solvable side* of the
symmetric-group threshold for every degree except the last open case, `S₄`:

  * `permSolvable_of_alternatingSolvable` — the reduction `Aₙ solvable ⟹ Sₙ solvable`
    (the short exact sequence `1 → Aₙ → Sₙ → ℤˣ` with abelian quotient);
  * `permFinTwo_isSolvable`, `permFinThree_isSolvable` — `S₂`, `S₃` solvable, via the
    prime-order (cyclic, hence abelian) alternating groups `A₂`, `A₃`.

It left two open questions, both resolved here:

  * **A₄ solvable.** `alternatingFinFour_isSolvable` proves `IsSolvable (A₄)`. The group
    `A₄` of order 12 is the one case the prime-order argument cannot reach. Its commutator
    subgroup is the Klein-four group `V₄ ⊴ A₄` (Mathlib's `alternatingGroup.kleinFour`,
    `kleinFour_eq_commutator`), which has exponent two hence is abelian
    (`mul_comm_of_exponent_two`), so it is solvable; and the quotient `A₄ / V₄` is abelian
    because `V₄` *is* the commutator (`quotient_commutative_iff_commutator_le`), hence
    solvable. The short exact sequence `1 → V₄ → A₄ → A₄/V₄ → 1` then gives `IsSolvable A₄`
    via `solvable_of_ker_le_range` — i.e. the metabelian derived series `A₄ ⊳ V₄ ⊳ 1`.
    Through the parent reduction this yields `permFinFour_isSolvable : IsSolvable (S₄)`.

  * **The full equivalence.** With `S₄` closed, `isSolvable_perm_fin_iff` packages the
    whole dichotomy as a single biconditional

        IsSolvable (Equiv.Perm (Fin n))  ↔  n ≤ 4.

    The forward direction is the non-solvability half: for `n ≥ 5` the alternating group
    `A₅ ↪ Aₙ` is simple and non-abelian, so `Sₙ` is not solvable
    (Mathlib's `Equiv.Perm.not_solvable`). The backward direction collects the solvable
    cases `n ∈ {0,1,2,3,4}` — the trivial groups `S₀, S₁`, the parent's `S₂, S₃`, and the
    new `S₄`.

This is the exact group-theoretic threshold underlying the Abel–Ruffini theorem: the
general polynomial of degree `n` is solvable by radicals iff its Galois group `Sₙ` is
solvable, iff `n ≤ 4`.

Status: 0 sorries, 0 axioms, no `native_decide`. `#print axioms` on the headline theorems
reports only `propext, Classical.choice, Quot.sound`.
-/

namespace AbelRuffiniOQ06OQ01

open Equiv

/-- **`A₄ = alternatingGroup (Fin 4)` is solvable.** The single case the prime-order
argument cannot reach (`|A₄| = 12`). The commutator subgroup of `A₄` is the Klein-four
group `V₄` (abelian, exponent two), and the quotient `A₄ / V₄ ≅ ℤ/3` is abelian since `V₄`
is exactly the commutator. Hence the derived series `A₄ ⊳ V₄ ⊳ 1` terminates: `A₄` is
metabelian, so solvable. -/
theorem alternatingFinFour_isSolvable : IsSolvable (alternatingGroup (Fin 4)) := by
  have hα4 : Nat.card (Fin 4) = 4 := Nat.card_eq_fintype_card.trans (Fintype.card_fin 4)
  set N := alternatingGroup.kleinFour (Fin 4) with hN
  haveI hNnormal : N.Normal := alternatingGroup.normal_kleinFour hα4
  -- V₄ has exponent two, hence is abelian, hence solvable.
  have hexp : Monoid.exponent N = 2 := by
    rw [hN]; exact alternatingGroup.exponent_kleinFour_of_card_eq_four hα4
  haveI hNsolv : IsSolvable N :=
    isSolvable_of_comm (fun a b => mul_comm_of_exponent_two hexp a b)
  -- A₄ / V₄ is abelian because V₄ is the commutator subgroup of A₄.
  have hcomm_le : commutator (alternatingGroup (Fin 4)) ≤ N :=
    le_of_eq (alternatingGroup.kleinFour_eq_commutator hα4).symm
  have hQcomm : Std.Commutative (· * · : (alternatingGroup (Fin 4) ⧸ N) → _ → _) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm_le
  haveI hQsolv : IsSolvable (alternatingGroup (Fin 4) ⧸ N) :=
    isSolvable_of_comm (fun a b => hQcomm.comm a b)
  -- The short exact sequence  1 → V₄ → A₄ → A₄/V₄ → 1.
  exact solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
    (le_of_eq (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype]))

/-- **`S₄ = Equiv.Perm (Fin 4)` is solvable.** Lifts `A₄` solvable through the parent
reduction `permSolvable_of_alternatingSolvable`. This closes the last open case of the
solvable side of the threshold. -/
theorem permFinFour_isSolvable : IsSolvable (Equiv.Perm (Fin 4)) :=
  haveI := alternatingFinFour_isSolvable
  AbelRuffiniOQ06.permSolvable_of_alternatingSolvable 4

/-- **The Abel–Ruffini threshold, packaged:** `Sₙ = Equiv.Perm (Fin n)` is solvable **iff**
`n ≤ 4`. The forward direction is non-solvability for `n ≥ 5` (`Equiv.Perm.not_solvable`,
rooted in the simplicity of `A₅`); the backward direction collects the solvable cases
`n ∈ {0,1,2,3,4}` — the trivial `S₀, S₁`, the parent's `S₂, S₃`, and `S₄`. -/
theorem isSolvable_perm_fin_iff (n : ℕ) :
    IsSolvable (Equiv.Perm (Fin n)) ↔ n ≤ 4 := by
  constructor
  · -- solvable ⟹ n ≤ 4, by contraposition through Aₙ non-solvable for n ≥ 5
    intro hsolv
    by_contra hn
    push_neg at hn
    exact Equiv.Perm.not_solvable (Fin n)
      (by rw [Cardinal.mk_fin]; exact_mod_cast hn) hsolv
  · -- n ≤ 4 ⟹ solvable, case by case
    intro hn
    interval_cases n
    · infer_instance
    · infer_instance
    · exact AbelRuffiniOQ06.permFinTwo_isSolvable
    · exact AbelRuffiniOQ06.permFinThree_isSolvable
    · exact permFinFour_isSolvable

end AbelRuffiniOQ06OQ01
