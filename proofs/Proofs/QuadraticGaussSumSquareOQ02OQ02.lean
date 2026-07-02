/-
  Fibre counts for the power map `x ↦ xᵏ` over a finite field.

  The parent entry `quadratic-gauss-sum-square-oq-02` counts the nonzero
  squares of `ZMod p` using the *quadratic* character `χ` and the vanishing
  character sum `∑ χ = 0`: the map `x ↦ x²` is exactly 2-to-1 on the units, so
  there are `(p-1)/2` squares.  Its open question asks whether the same fibre
  count generalises to higher-order maps `x ↦ xᵏ` — the quadratic case being
  `k = 2` and the character-sum decomposition being the `k`-th order analogue of
  character orthogonality.

  This file answers that question *exactly*, and for an arbitrary finite field
  `F` (not just `ZMod p`).  Rather than routing through the `k` multiplicative
  characters of order dividing `k` and their orthogonality relations, we use the
  structural fact underlying that computation: on the cyclic group `Fˣ` the map
  `x ↦ xᵏ` is the monoid endomorphism `powMonoidHom k`, whose kernel and range
  cardinalities are pinned by `gcd(k, |Fˣ|)`.  Concretely, with `q = |F|` and
  `d = gcd(k, q-1)`:

    * the number of `k`-th roots of unity `#{x : xᵏ = 1}` is `d`;
    * the number of `k`-th powers `#{xᵏ : x}` is `(q-1)/d`;
    * every nonempty fibre `#{x : xᵏ = a}` has exactly `d` elements, because it
      is a coset of the kernel (`MonoidHom.fiberEquivKer`);
    * so `x ↦ xᵏ` is a `d`-to-`1` map onto its image.

  Specialising to `k = 2` and `F = ZMod p` (`p` an odd prime) recovers the
  parent's count: `d = gcd(2, p-1) = 2`, giving `(p-1)/2` squares, each with two
  square roots.  So the parent's quadratic-character count is the `k = 2` shadow
  of this uniform gcd law.

  Everything is 0-axiom: the arithmetic comes from
  `IsCyclic.card_powMonoidHom_ker` / `IsCyclic.card_powMonoidHom_range` (the
  units of a finite field are cyclic) and the fibre count from the coset
  equivalence `MonoidHom.fiberEquivKer`.
-/
import Mathlib

open scoped BigOperators
open Finset

namespace QuadraticGaussSumSquareOQ02OQ02

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The `k`-th power map on the units of `F`, as a monoid endomorphism
`x ↦ xᵏ`.  `Fˣ` is a finite commutative — indeed cyclic — group, which is what
makes the fibre count purely arithmetic. -/
noncomputable abbrev powHom (k : ℕ) : Fˣ →* Fˣ := powMonoidHom k

@[simp] theorem powHom_apply (k : ℕ) (x : Fˣ) : powHom k x = x ^ k := rfl

/-- The number of `k`-th roots of unity in `Fˣ`, i.e. the kernel of `x ↦ xᵏ`,
is `gcd(k, q-1)` where `q = |F|`.  This is `IsCyclic.card_powMonoidHom_ker`
specialised to the cyclic group `Fˣ`, with `|Fˣ| = q - 1`. -/
theorem card_kthRootsOfUnity (k : ℕ) :
    Nat.card (powHom (F := F) k).ker = (Fintype.card F - 1).gcd k := by
  rw [IsCyclic.card_powMonoidHom_ker, Nat.card_eq_fintype_card, Fintype.card_units]

/-- The number of `k`-th powers in `Fˣ`, i.e. the range of `x ↦ xᵏ`, is
`(q-1)/gcd(k, q-1)`.  This is `IsCyclic.card_powMonoidHom_range` on `Fˣ`. -/
theorem card_kthPowers (k : ℕ) :
    Nat.card (powHom (F := F) k).range
      = (Fintype.card F - 1) / (Fintype.card F - 1).gcd k := by
  rw [IsCyclic.card_powMonoidHom_range, Nat.card_eq_fintype_card, Fintype.card_units]

/-- **Uniform fibre count.** Every value `a` that *is* a `k`-th power has exactly
`gcd(k, q-1)` pre-images under `x ↦ xᵏ`: the fibre is a coset of the kernel, so
has the same cardinality as the kernel (`MonoidHom.fiberEquivKer`). -/
theorem card_fibre_of_mem_range (k : ℕ) (a : Fˣ)
    (ha : a ∈ (powHom (F := F) k).range) :
    Nat.card ((powHom (F := F) k) ⁻¹' {a}) = (Fintype.card F - 1).gcd k := by
  obtain ⟨x, hx⟩ := ha
  have hfib : (powHom (F := F) k) ⁻¹' {a} = (powHom (F := F) k) ⁻¹' {powHom k x} := by
    rw [hx]
  rw [hfib, Nat.card_congr (MonoidHom.fiberEquivKer (powHom (F := F) k) x),
    card_kthRootsOfUnity]

/-- A value that is **not** a `k`-th power has an empty fibre — there is no `x`
with `xᵏ = a`. -/
theorem fibre_empty_of_not_mem_range (k : ℕ) (a : Fˣ)
    (ha : a ∉ (powHom (F := F) k).range) :
    (powHom (F := F) k) ⁻¹' {a} = (∅ : Set Fˣ) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
  intro hx
  exact ha ⟨x, hx⟩

/- The full dichotomy: the fibre of `x ↦ xᵏ` over any `a : Fˣ` has cardinality
`gcd(k, q-1)` if `a` is a `k`-th power and `0` otherwise. -/
open Classical in
theorem card_fibre (k : ℕ) (a : Fˣ) :
    Nat.card ((powHom (F := F) k) ⁻¹' {a})
      = if a ∈ (powHom (F := F) k).range then (Fintype.card F - 1).gcd k else 0 := by
  by_cases ha : a ∈ (powHom (F := F) k).range
  · rw [if_pos ha, card_fibre_of_mem_range k a ha]
  · rw [if_neg ha, fibre_empty_of_not_mem_range k a ha, Nat.card_eq_fintype_card,
      Fintype.card_of_isEmpty]

/-- **Counting identity.** `(number of `k`-th powers) · (fibre size) = q - 1`:
the `k`-th power map is a `gcd(k, q-1)`-to-`1` surjection onto the `k`-th powers,
so the two counts multiply back to `|Fˣ| = q - 1`.  This is Lagrange /
first-isomorphism for `powMonoidHom k`, read off from the two card formulas. -/
theorem card_powers_mul_card_roots (k : ℕ) :
    Nat.card (powHom (F := F) k).range * (Fintype.card F - 1).gcd k
      = Fintype.card F - 1 := by
  rw [card_kthPowers, Nat.div_mul_cancel]
  exact Nat.gcd_dvd_left _ _

end QuadraticGaussSumSquareOQ02OQ02

/-!
### Specialisation: the quadratic case recovers the parent count

Over `ZMod p` with `p` an odd prime, `q - 1 = p - 1` and `gcd(2, p-1) = 2`, so
the map `x ↦ x²` is exactly 2-to-1 on `(ZMod p)ˣ` and there are `(p-1)/2`
nonzero squares — precisely the equidistribution count that the parent entry
obtained from the quadratic character sum `∑ χ = 0`.
-/

namespace QuadraticGaussSumSquareOQ02OQ02

/-- Over an odd prime field, `gcd(2, p-1) = 2`: every nonzero square has exactly
two square roots.  (`p` odd ⇒ `p - 1` even.) -/
theorem gcd_two_pSub_one (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    (Fintype.card (ZMod p) - 1).gcd 2 = 2 := by
  have hodd : Odd p := (Nat.Prime.odd_of_ne_two Fact.out hp)
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  rw [hcard]
  -- `p` odd ⇒ `2 ∣ p - 1`, so `gcd (p-1) 2 = 2`
  have hdvd : 2 ∣ (p - 1) := by
    obtain ⟨m, hm⟩ := hodd
    omega
  rw [Nat.gcd_comm]
  exact Nat.gcd_eq_left hdvd

/-- The number of nonzero squares in `ZMod p` (`p` odd prime) is `(p-1)/2`,
matching the parent's quadratic-character count — now read off as the `k = 2`
case of the uniform fibre law. -/
theorem card_squares_zmod (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    Nat.card (powHom (F := ZMod p) 2).range = (p - 1) / 2 := by
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  rw [card_kthPowers, gcd_two_pSub_one p hp, hcard]

end QuadraticGaussSumSquareOQ02OQ02
