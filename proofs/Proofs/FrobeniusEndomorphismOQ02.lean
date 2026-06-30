/-
  The Frobenius automorphism generates the Galois group of a finite field.

  Let `K` be a finite field of characteristic `p`, so that `K` is an extension
  of its prime subfield `𝔽_p = ZMod p` of some degree `n`, i.e. `|K| = p ^ n`.
  The parent entry (`FrobeniusEndomorphismOQ01`) packaged the Frobenius
  endomorphism `x ↦ x ^ p` as a ring homomorphism and recorded the
  finite-field identity `x ^ (p ^ n) = x`.  This file upgrades that picture to
  the level of **Galois theory**:

    * over the prime field the Frobenius `x ↦ x ^ p` is a field
      *automorphism* fixing `𝔽_p`, hence an element
      `frob ∈ Gal(K / 𝔽_p) = K ≃ₐ[ZMod p] K`;
    * the Galois group is **cyclic** of order `n = [K : 𝔽_p]`, and `frob`
      *generates* it (`zpowers frob = ⊤`);
    * the order of `frob` is exactly `n`: the `n`-fold iterate is the identity
      (`x ↦ x ^ (p ^ n) = x`), while no smaller positive iterate is;
    * consequently there is an explicit group isomorphism
      `Multiplicative (ZMod n) ≃* Gal(K / 𝔽_p)` sending the generator `1` to
      the Frobenius.

  Mathlib supplies the finite-field Galois machinery
  (`FiniteField.frobeniusAlgEquivOfAlgebraic`, its order, and the
  `IsCyclic Gal(L/K)` instance) for an arbitrary finite base field; here we
  specialise it to the prime base `ZMod p`, where the abstract `q`-power
  automorphism becomes the honest prime Frobenius `x ↦ x ^ p`, and assemble the
  classical structure theorem `Gal(K / 𝔽_p) ≃ ℤ/n`.

  Fully verified: 0 sorries, 0 axioms, no `native_decide`.
-/
import Mathlib

namespace FrobeniusEndomorphismOQ02

open Module (finrank)

variable (p : ℕ) [Fact p.Prime]

instance : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod p) K]

/-- The **Frobenius automorphism** `x ↦ x ^ p` of a finite field `K` of
characteristic `p`, viewed as an element of the Galois group
`Gal(K / 𝔽_p) = K ≃ₐ[ZMod p] K`.  Over the prime base field `ZMod p` the abstract
`q`-power automorphism (`q = |𝔽_p| = p`) is precisely the prime Frobenius. -/
noncomputable abbrev frob : K ≃ₐ[ZMod p] K :=
  FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod p) K

/-! ### The Frobenius automorphism is the prime `p`-power map -/

/-- The Galois-theoretic Frobenius acts as the honest prime Frobenius
`x ↦ x ^ p`. -/
@[simp] theorem frob_apply (x : K) : frob p x = x ^ p := by
  show x ^ Fintype.card (ZMod p) = x ^ p
  rw [ZMod.card]

/-! ### Order, cyclicity, and the generator -/

/-- The order of the Frobenius automorphism equals the degree `n = [K : 𝔽_p]`. -/
theorem orderOf_frob : orderOf (frob p : K ≃ₐ[ZMod p] K) = finrank (ZMod p) K :=
  FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (ZMod p) K

/-- The Galois group `Gal(K / 𝔽_p)` has order `n = [K : 𝔽_p]`. -/
theorem card_galoisGroup : Nat.card (K ≃ₐ[ZMod p] K) = finrank (ZMod p) K :=
  IsGalois.card_aut_eq_finrank (ZMod p) K

/-- The Galois group of a finite field over its prime subfield is **cyclic**. -/
theorem isCyclic_galoisGroup : IsCyclic (K ≃ₐ[ZMod p] K) := inferInstance

/-- The Frobenius automorphism **generates** the Galois group:
`Gal(K / 𝔽_p) = ⟨frob⟩`. -/
theorem zpowers_frob_eq_top : Subgroup.zpowers (frob p) = (⊤ : Subgroup (K ≃ₐ[ZMod p] K)) := by
  rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers, orderOf_frob, card_galoisGroup]

/-- Every automorphism in `Gal(K / 𝔽_p)` is an integer power of the Frobenius. -/
theorem mem_zpowers_frob (g : K ≃ₐ[ZMod p] K) : g ∈ Subgroup.zpowers (frob p) := by
  rw [zpowers_frob_eq_top]; exact Subgroup.mem_top g

/-- Every automorphism in `Gal(K / 𝔽_p)` is a natural-number power of the
Frobenius: `g = frob ^ k` for some `k`. -/
theorem exists_pow_frob (g : K ≃ₐ[ZMod p] K) : ∃ k : ℕ, frob p ^ k = g := by
  have hg := mem_powers_iff_mem_zpowers.mpr (mem_zpowers_frob p g)
  rwa [Submonoid.mem_powers_iff] at hg

/-! ### The `n`-fold iterate is the identity, and no smaller one is -/

/-- The `n`-th power of the Frobenius is the identity automorphism, `n = [K : 𝔽_p]`. -/
theorem frob_pow_finrank : (frob p : K ≃ₐ[ZMod p] K) ^ finrank (ZMod p) K = 1 := by
  rw [← orderOf_frob]; exact pow_orderOf_eq_one (frob p)

/-- Pointwise: iterating the Frobenius `n` times returns every element,
`x ↦ x ^ (p ^ n) = x`, since `p ^ n = |K|`. -/
theorem frob_iterate_finrank (x : K) :
    (⇑(frob p))^[finrank (ZMod p) K] x = x := by
  have hcard : p ^ finrank (ZMod p) K = Fintype.card K :=
    FiniteField.pow_finrank_eq_card p K
  calc (⇑(frob p))^[finrank (ZMod p) K] x
      = x ^ (Fintype.card (ZMod p) ^ finrank (ZMod p) K) := by
        rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    _ = x ^ Fintype.card K := by rw [ZMod.card, hcard]
    _ = x := FiniteField.pow_card x

/-- The order is **exactly** `n`: no positive power below `n = [K : 𝔽_p]` is the
identity. -/
theorem frob_pow_ne_one {m : ℕ} (hm : 0 < m) (hmn : m < finrank (ZMod p) K) :
    (frob p : K ≃ₐ[ZMod p] K) ^ m ≠ 1 := by
  intro h
  have hle := orderOf_le_of_pow_eq_one hm h
  rw [orderOf_frob] at hle
  omega

/-! ### Explicit structure theorem: `Gal(K / 𝔽_p) ≃ ℤ/n` -/

/-- **Structure theorem for the Galois group of a finite field.** There is an
explicit group isomorphism `Multiplicative (ZMod n) ≃* Gal(K / 𝔽_p)`, where
`n = [K : 𝔽_p]`; the additive generator `1` corresponds to the Frobenius. -/
noncomputable def galoisGroupMulEquivZMod :
    Multiplicative (ZMod (finrank (ZMod p) K)) ≃* (K ≃ₐ[ZMod p] K) := by
  have h : Nat.card (K ≃ₐ[ZMod p] K) = finrank (ZMod p) K := card_galoisGroup p
  exact h ▸ zmodCyclicMulEquiv (inferInstance : IsCyclic (K ≃ₐ[ZMod p] K))

end FrobeniusEndomorphismOQ02
