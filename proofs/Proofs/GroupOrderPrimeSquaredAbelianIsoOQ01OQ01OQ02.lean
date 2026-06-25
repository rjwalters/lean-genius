/-
  Explicit Isomorphisms for Groups of Order p² — the Structure Theorem

  Follow-up open question OQ-01-OQ-01-OQ-02
  (parent: group-order-prime-squared-abelian-oq-01-oq-01, the *exponent* refinement,
   grandparent: group-order-prime-squared-abelian-oq-01).

  The grandparent proves that a group `G` of order `p²` (`p` prime) is abelian and splits
  into two isomorphism types; the parent recasts the split through the single numerical
  invariant `Monoid.exponent G ∈ {p, p²}`. Those entries characterise the two types
  *up to a predicate* (cyclic vs. exponent-`p`). This follow-up upgrades the invariant
  characterisation to an honest **structure theorem**: it produces the explicit group
  isomorphisms

      exponent p²  (cyclic)        G ≃* Multiplicative (ZMod (p²))
      exponent p   (elem. abelian) G ≃* Multiplicative (ZMod p) × Multiplicative (ZMod p)

  so the abstract dichotomy becomes a concrete identification of `G` with one of the two
  groups `ℤ/p²` and `(ℤ/p)²`.

  ## Contents

  * `cyclicMulEquiv` — the cyclic case: a cyclic group of order `p²` is `≃*` to
    `Multiplicative (ZMod (p²))`. Built from Mathlib's `zmodCyclicMulEquiv` by rewriting
    `Nat.card G = p²`.
  * `elemAbelianMulEquiv` — the non-cyclic case: an order-`p²` group with `gᵖ = 1` for all
    `g` is `≃*` to `Multiplicative (ZMod p) × Multiplicative (ZMod p)`. The additive group
    `Additive G` is annihilated by `p`, hence a `ZMod p`-vector space; its cardinality `p²`
    forces dimension `2`, giving a basis `≅ (ZMod p)²`, which is transported back to `G`.
  * `mulEquiv_zmod_sq_or_prod` — every group of order `p²` is isomorphic to exactly one of
    the two groups `ℤ/p²`, `(ℤ/p)²`.
  * `mulEquiv_zmod_sq_of_exponent_sq` / `mulEquiv_prod_of_exponent_prime` — the structure
    theorem stated through the parent's exponent invariant: `exponent G = p²` pins `G` to
    `ℤ/p²`, and `exponent G = p` pins `G` to `(ℤ/p)²`.

  Everything is elementary; no axioms, no sorries. The abelian-ness and the dichotomy are
  imported from the ancestor files.
-/
import Mathlib
import Proofs.GroupOrderPrimeSquaredAbelian
import Proofs.GroupOrderPrimeSquaredAbelianExponentOQ01

namespace GroupOrderPrimeSqIso

open GroupOrderPrimeSq GroupOrderPrimeSqExponent
open Module

variable {G : Type*} [Group G]

/-! ## Finiteness helper -/

omit [Group G] in
/-- A group of cardinality `p²` (`p` prime) is finite. -/
private theorem finite_of_card_eq_prime_sq {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p ^ 2) : Finite G :=
  Nat.finite_of_card_ne_zero (hG ▸ pow_ne_zero 2 hp.pos.ne')

/-! ## The cyclic case: `G ≃* ℤ/p²` -/

/-- **A cyclic group of order `p²` is isomorphic to `Multiplicative (ZMod (p²))`.**
Mathlib's `zmodCyclicMulEquiv` gives `Multiplicative (ZMod (Nat.card G)) ≃* G` for any
cyclic `G`; rewriting `Nat.card G = p²` and inverting yields the explicit isomorphism.
(Primality of `p` plays no role here — only the value `Nat.card G = p²` is used.) -/
noncomputable def cyclicMulEquiv {p : ℕ} (hG : Nat.card G = p ^ 2)
    (hc : IsCyclic G) : G ≃* Multiplicative (ZMod (p ^ 2)) := by
  have e : Multiplicative (ZMod (Nat.card G)) ≃* G := zmodCyclicMulEquiv hc
  rw [hG] at e
  exact e.symm

/-! ## The elementary-abelian case: `G ≃* (ℤ/p)²`

The core analytic input is that the *additive* group `Additive G` of a non-cyclic
order-`p²` group is annihilated by `p`, so it carries a `ZMod p`-module (vector-space)
structure. Counting cardinalities pins the dimension at `2`. -/

/-- **A non-cyclic group of order `p²` is isomorphic to
`Multiplicative (ZMod p) × Multiplicative (ZMod p)`.**

`Additive G` is a `ZMod p`-vector space (every element is `p`-torsion), and
`Nat.card (Additive G) = p² = (Nat.card (ZMod p)) ^ 2`, so its dimension is `2`. A basis
indexed by `Fin 2` gives `Additive G ≃ₗ (Fin 2 → ZMod p) ≃ₗ ZMod p × ZMod p`; transporting
across the `Additive`/`Multiplicative` adjunction and splitting the product yields the
isomorphism. -/
noncomputable def elemAbelianMulEquiv {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ 2)
    (hnc : ¬ IsCyclic G) :
    G ≃* Multiplicative (ZMod p) × Multiplicative (ZMod p) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite G := finite_of_card_eq_prime_sq hp hG
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  -- `G` is abelian (grandparent), so the canonical `Additive G` is an `AddCommGroup`.
  letI : CommGroup G :=
    { (inferInstance : Group G) with mul_comm := mul_comm_of_card_eq_prime_sq hp hG }
  -- `Additive G` is annihilated by `p`, hence a `ZMod p`-module. The instance is named
  -- (`inst`) and threaded explicitly downstream: `AddCommMonoid.zmodModule` is a reducible
  -- non-instance, so derived-instance search (`Module.Finite`/`Module.Free`) cannot rebuild
  -- it on its own and would otherwise get stuck.
  letI inst : Module (ZMod p) (Additive G) :=
    AddCommMonoid.zmodModule (fun x => by
      calc p • x
          = Additive.ofMul (x.toMul ^ p) := (ofMul_pow p x.toMul).symm
        _ = Additive.ofMul (1 : G) := by rw [pow_prime_eq_one_of_not_isCyclic hp hG hnc]
        _ = 0 := ofMul_one)
  haveI : Finite (Additive G) := inferInstanceAs (Finite G)
  haveI hmf : @Module.Finite (ZMod p) (Additive G) _ _ inst := Module.Finite.of_finite
  haveI hfree : @Module.Free (ZMod p) (Additive G) _ _ inst :=
    @Module.Free.of_divisionRing (ZMod p) (Additive G) _ _ inst
  -- Dimension is exactly `2`: `p² = (Nat.card (ZMod p)) ^ finrank = p ^ finrank`.
  have hcardZ : Nat.card (ZMod p) = p := by
    rw [Nat.card_eq_fintype_card, ZMod.card]
  have hcard : Nat.card (Additive G) = Nat.card (ZMod p) ^ finrank (ZMod p) (Additive G) :=
    @Module.natCard_eq_pow_finrank (ZMod p) (Additive G) _ _ inst hmf
  have hcardG : Nat.card (Additive G) = p ^ 2 := hG
  rw [hcardG, hcardZ] at hcard
  have hrank : finrank (ZMod p) (Additive G) = 2 :=
    (Nat.pow_right_injective hp.two_le hcard).symm
  -- Basis of size `2` ⇒ linear equivalence to `(ZMod p)²`.
  let b : Basis (Fin 2) (ZMod p) (Additive G) :=
    @Module.finBasisOfFinrankEq (ZMod p) (Additive G) _ _ _ inst hfree hmf 2 hrank
  let eLin : Additive G ≃ₗ[ZMod p] ZMod p × ZMod p :=
    b.equivFun.trans (LinearEquiv.finTwoArrow (ZMod p) (ZMod p))
  -- Transport across `Additive ⊣ Multiplicative` and split the product.
  exact (AddEquiv.toMultiplicativeRight eLin.toAddEquiv).trans
    (MulEquiv.prodMultiplicative (ZMod p) (ZMod p))

/-! ## The structure theorem -/

/-- **Classification by explicit isomorphism.** A group of order `p²` (`p` prime) is
isomorphic either to `Multiplicative (ZMod (p²))` (the cyclic type `ℤ/p²`) or to
`Multiplicative (ZMod p) × Multiplicative (ZMod p)` (the elementary-abelian type
`(ℤ/p)²`). The two cases are mutually exclusive (grandparent dichotomy). -/
theorem mulEquiv_zmod_sq_or_prod {p : ℕ} (hp : p.Prime) (hG : Nat.card G = p ^ 2) :
    Nonempty (G ≃* Multiplicative (ZMod (p ^ 2))) ∨
      Nonempty (G ≃* Multiplicative (ZMod p) × Multiplicative (ZMod p)) := by
  by_cases hc : IsCyclic G
  · exact Or.inl ⟨cyclicMulEquiv hG hc⟩
  · exact Or.inr ⟨elemAbelianMulEquiv hp hG hc⟩

/-- **Exponent `p²` ⟹ `G ≃* ℤ/p²`.** Stated through the parent's invariant: the value
`exponent G = p²` is, by the parent, equivalent to `G` being cyclic, which pins the
isomorphism type to `Multiplicative (ZMod (p²))`. -/
noncomputable def mulEquiv_zmod_sq_of_exponent_sq {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p ^ 2) (hexp : Monoid.exponent G = p ^ 2) :
    G ≃* Multiplicative (ZMod (p ^ 2)) :=
  cyclicMulEquiv hG ((exponent_eq_sq_iff_isCyclic hp hG).mp hexp)

/-- **Exponent `p` ⟹ `G ≃* (ℤ/p)²`.** Dually, the value `exponent G = p` characterises
the non-cyclic (elementary-abelian) type, pinning the isomorphism type to
`Multiplicative (ZMod p) × Multiplicative (ZMod p)`. -/
noncomputable def mulEquiv_prod_of_exponent_prime {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p ^ 2) (hexp : Monoid.exponent G = p) :
    G ≃* Multiplicative (ZMod p) × Multiplicative (ZMod p) :=
  elemAbelianMulEquiv hp hG ((exponent_eq_prime_iff_not_isCyclic hp hG).mp hexp)

end GroupOrderPrimeSqIso
