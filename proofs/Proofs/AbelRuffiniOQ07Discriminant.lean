/-
  Discriminant / Jordan route to Gal(X⁵ − X − 1 / ℚ) ≅ S₅
  (Open Question OQ-07 of abel-ruffini, discriminant variant)

  ## Background
  The sibling entry `AbelRuffiniOQ07.lean` reduces the claim Gal(X⁵−X−1) ≅ S₅ to
  the existence of a *transposition* in the Galois group, obtained from the order-6
  Frobenius element at p = 2 (a Dedekind/Frobenius cycle-type input). That route
  hard-codes a very specific permutation (`frob2 ^ 3 = swap 0 1`).

  ## This file: the discriminant route
  The classical Selmer/Galois argument for X⁵ − X − 1 uses the **discriminant**
  rather than a single transposition:

    * Δ(X⁵ − X − 1) = 2869 = 19 · 151 is **not a perfect square**, so the Galois
      group is **not contained in A₅** — it contains *some* odd permutation
      (not necessarily a transposition).
    * Irreducibility (Selmer 1956) gives a transitive action of prime degree 5,
      hence a *primitive* action.
    * `3 ∣ |Gal|` gives an element of order 3, i.e. a **3-cycle** in S₅.

  Jordan's theorem (a primitive permutation group containing a 3-cycle contains the
  alternating group) then forces A₅ ≤ Gal, and the odd permutation upgrades this to
  Gal = ⊤ = S₅.

  This is strictly more robust than the transposition route: it needs only that
  *some* element is odd (the discriminant datum), never a specific swap.

  ## What this file verifies (0 sorry, 0 axiom)
    * `gal_eq_top_of_transitive_threeCycle_odd` — the discriminant-route assembler:
      for any `G ≤ S₅` acting transitively, containing a 3-cycle and an odd
      permutation, `G = ⊤`. Proven via Mathlib's Jordan theorem
      (`alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem`).
    * `disc_value` / `disc_factorization` — the discriminant Δ = 2869 = 19 · 151.
    * `disc_not_square` — 2869 is not a perfect square (it is ≡ 6 (mod 7), a
      quadratic non-residue), the formal content of "Gal ⊄ A₅".

  The two number-theoretic inputs to the assembler — `3 ∣ |Gal|` (a 3-cycle) and
  "Gal contains an odd permutation" (from `disc_not_square`) — are exposed as
  hypotheses, because the bridges that produce them (Dedekind–Frobenius cycle types;
  discriminant-square ⟺ Gal ⊆ A₅) are not present in Mathlib v4.26.0. Everything in
  this file is fully machine-checked with 0 sorries and 0 axioms.
-/
import Mathlib.GroupTheory.GroupAction.Jordan
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

open MulAction Equiv Equiv.Perm

/-- The symmetric group on the 5 roots. -/
abbrev S5 := Equiv.Perm (Fin 5)

/-- The degree is the prime 5 — the hypothesis that makes the prime-degree
permutation-group machinery (primitivity from transitivity, Jordan) applicable. -/
theorem card_fin5_prime : Nat.Prime (Nat.card (Fin 5)) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num

/-!
## The discriminant-route assembler

Any subgroup of `S₅` that acts **transitively**, contains a **3-cycle**, and
contains an **odd permutation** is the whole of `S₅`.  This is the corrected,
discriminant-compatible criterion: unlike the swap-based assembler in the sibling
file, it accepts *any* odd element (which is exactly what a non-square discriminant
provides).
-/

/-- **Discriminant-route assembler.**  A transitive subgroup `G ≤ S₅` containing a
3-cycle and an odd permutation equals `⊤`.

Proof: prime degree 5 upgrades transitivity to primitivity; Jordan's theorem then
gives `A₅ ≤ G`; and an odd element rules out `G = A₅`, leaving `G = ⊤` since `A₅`
has index 2. -/
theorem gal_eq_top_of_transitive_threeCycle_odd
    {G : Subgroup S5} (htrans : IsPretransitive G (Fin 5))
    {g : S5} (h3 : g.IsThreeCycle) (hg : g ∈ G)
    {h : S5} (hodd : h ∉ alternatingGroup (Fin 5)) (hhG : h ∈ G) :
    G = ⊤ := by
  haveI : IsPretransitive G (Fin 5) := htrans
  -- prime degree ⟹ primitive action
  have hprim : IsPreprimitive G (Fin 5) := IsPreprimitive.of_prime_card card_fin5_prime
  -- Jordan: a primitive group with a 3-cycle contains the alternating group
  have hA : alternatingGroup (Fin 5) ≤ G :=
    alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim h3 hg
  -- `A₅` has index 2, so `G.index ∣ 2`; the odd element kills `G.index = 2`.
  have hdvd : G.index ∣ (alternatingGroup (Fin 5)).index := Subgroup.index_dvd_of_le hA
  rw [alternatingGroup.index_eq_two] at hdvd
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact Subgroup.index_eq_one.mp h1
  · exact absurd ((eq_alternatingGroup_of_index_eq_two h2) ▸ hhG) hodd

/-!
## The discriminant of `X⁵ − X − 1`

For the trinomial `X⁵ + aX + b` the discriminant is `4⁴·a⁵ + 5⁵·b⁴`; for
`X⁵ − X − 1` (`a = −1, b = −1`) this is `256·(−1) + 3125 = 2869`.
-/

/-- The discriminant of `X⁵ − X − 1` is `2869`. -/
theorem disc_value : (256 * (-1 : ℤ) ^ 5 + 3125 * (-1 : ℤ) ^ 4) = 2869 := by norm_num

/-- `2869 = 19 · 151` — squarefree, hence not a perfect square. -/
theorem disc_factorization : (2869 : ℤ) = 19 * 151 := by norm_num

/-- The discriminant `2869` is **not a perfect square**: it is `≡ 6 (mod 7)`, and
`6` is a quadratic non-residue mod 7.  Group-theoretically this is the statement
`Gal(X⁵−X−1) ⊄ A₅` (the Galois group contains an odd permutation), the input the
discriminant supplies to `gal_eq_top_of_transitive_threeCycle_odd`. -/
theorem disc_not_square : ¬ IsSquare (2869 : ℤ) := by
  intro h
  have h7 : IsSquare ((2869 : ℤ) : ZMod 7) := h.map (Int.castRingHom (ZMod 7))
  have : ¬ IsSquare ((2869 : ℤ) : ZMod 7) := by decide
  exact this h7
