import Mathlib

/-
# The permutation-group consequence of the mod-7 `(1,1,3)` factor type (OQ-06 → OQ-02)

The sibling files `InverseGaloisOQ06OQ02.lean` (mod 7) and
`InverseGaloisOQ06OQ02P11.lean` (mod 11) supply the *algebraic* input that
Dedekind's theorem consumes toward the last axiom of `InverseGaloisA5.lean`:

  `axiom three_dvd_gal_card : 3 ∣ Fintype.card q.Gal`

namely that `q = X⁵ - 5X⁴ + 10X³ - 10X² + 25X - 5` reduces, modulo the
unramified prime `7`, to a product of distinct irreducibles of degrees
`(1, 1, 3)`.

Dedekind's theorem itself — the statement that this factorization type forces
`Gal(q) ⊆ S₅` to contain a *Frobenius element of the same cycle type* — is the
remaining Mathlib 4.26 gap. But Dedekind's conclusion splits into two parts:

  (A) Frobenius ↔ factorization: the genuine number-theory gap, owned by the
      sibling `inverse-galois-a5-oq-01` (`InverseGaloisA5Dedekind.lean`).
  (B) cycle type ⟹ element order ⟹ divisibility of `|Gal|`: a *purely
      group-theoretic*, fully machine-checkable consequence.

This file isolates and verifies **part (B)** with **no axioms and no sorries**,
so the only thing standing between the verified algebraic input and the axiom is
part (A). Concretely we:

* exhibit an explicit permutation of the five roots with cycle type `(1, 1, 3)`
  (a 3-cycle that fixes two points — the two linear factors `X-5`, `X-6` mod 7),
* prove it has order exactly `3`,
* prove the abstract bridge: **any finite group with an order-3 element, and any
  subgroup of `S₅` containing such a `(1,1,3)` permutation, has order divisible
  by 3.**

This is *not* a claim that `three_dvd_gal_card` is eliminated — it makes precise
that the deterministic half of the mod-7 Dedekind route is verified, and the
residual gap is exactly the Frobenius ↔ factorization correspondence (A).
-/

open Equiv Equiv.Perm

namespace InverseGaloisOQ06OQ02Cycle

/-! ## An explicit `(1,1,3)` permutation of the five roots -/

/-- The cycle type `(1, 1, 3)` of `q mod 7` corresponds, in the symmetric group
`S₅` on the five roots, to a permutation that 3-cycles the three roots of the
irreducible cubic factor and fixes the two roots of the linear factors
`X - 5`, `X - 6`.  We realise it concretely as `(2 3 4)`, fixing `0` and `1`. -/
def frob113 : Perm (Fin 5) := swap 2 3 * swap 2 4

/-- `frob113` is a three-cycle (matching the single degree-3 irreducible factor). -/
theorem frob113_isThreeCycle : frob113.IsThreeCycle :=
  isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

/-- Its cycle type is `{3}` — i.e. one 3-cycle plus two fixed points, exactly the
`(1, 1, 3)` shape of the mod-7 factorization. -/
theorem frob113_cycleType : frob113.cycleType = {3} :=
  frob113_isThreeCycle.cycleType

/-- The order of the `(1,1,3)` permutation is exactly `3`. -/
theorem frob113_orderOf : orderOf frob113 = 3 :=
  frob113_isThreeCycle.orderOf

/-- The root of the linear factor `X - 5` (encoded as point `0`) is fixed. -/
theorem frob113_fixes_zero : frob113 0 = 0 := by decide

/-- The root of the linear factor `X - 6` (encoded as point `1`) is fixed. -/
theorem frob113_fixes_one : frob113 1 = 1 := by decide

/-! ## The abstract deterministic half of Dedekind: cycle type ⟹ `3 ∣ |G|` -/

/-- **Group-level bridge.** In any finite group, a single order-3 element forces
`3 ∣ |G|`.  This is the trivial-but-essential downstream step of Dedekind: once
the Frobenius element of cycle type `(1,1,3)` is known to have order 3, its order
divides the group order. -/
theorem three_dvd_card_of_orderOf_three {G : Type*} [Group G] [Fintype G]
    (g : G) (hg : orderOf g = 3) : 3 ∣ Fintype.card G := by
  rw [← hg]; exact orderOf_dvd_card

/-- **Subgroup-level bridge.** If a subgroup `H ⊆ S(α)` of a permutation group
contains a three-cycle, then `3 ∣ |H|`.  Applied with `H = Gal(q) ↪ S₅` and the
Frobenius `(1,1,3)` permutation, this is precisely the conclusion the mod-7
Dedekind route needs — modulo the Frobenius ↔ factorization correspondence,
which is the genuine remaining gap. -/
theorem three_dvd_natCard_of_isThreeCycle_mem {α : Type*} [Fintype α] [DecidableEq α]
    {H : Subgroup (Perm α)} {σ : Perm α} (hσ : σ.IsThreeCycle) (hmem : σ ∈ H) :
    3 ∣ Nat.card H := by
  rw [← hσ.orderOf]
  exact H.orderOf_dvd_natCard hmem

/-- **Instantiation at the explicit `(1,1,3)` witness.** Any subgroup of `S₅`
containing `frob113` (the cycle type of `q mod 7`) has order divisible by 3. -/
theorem three_dvd_natCard_of_frob113_mem {H : Subgroup (Perm (Fin 5))}
    (hmem : frob113 ∈ H) : 3 ∣ Nat.card H :=
  three_dvd_natCard_of_isThreeCycle_mem frob113_isThreeCycle hmem

/-- **Packaged statement of part (B).** The `(1,1,3)` factor type, *once realised
as a Frobenius permutation `σ ∈ Gal`* (the hypothesis `hmem` together with the
cycle-type identity `hσ`), deterministically yields `3 ∣ |Gal|`.  Phrasing it
with the cycle-type hypothesis explicit makes the residual Mathlib gap visible:
supplying `σ` and `hmem` for the actual mod-7 Frobenius is part (A), Dedekind's
theorem. -/
theorem dedekind_consequence_113 {α : Type*} [Fintype α] [DecidableEq α]
    {Gal : Subgroup (Perm α)} {σ : Perm α}
    (hσ : σ.cycleType = {3}) (hmem : σ ∈ Gal) :
    3 ∣ Nat.card Gal :=
  three_dvd_natCard_of_isThreeCycle_mem hσ hmem

end InverseGaloisOQ06OQ02Cycle
