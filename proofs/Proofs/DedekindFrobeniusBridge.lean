import Mathlib

/-!
# Dedekind–Frobenius bridge: order of the arithmetic Frobenius at an unramified prime

This file closes a genuine Mathlib gap that was the shared blocker for two open
gallery problems, `abel-ruffini-oq-07` and `inverse-galois-a5-oq-01`:

> At a prime `Q` of `S` that is *unramified* over its contraction `p = Q.under R`,
> the canonical arithmetic Frobenius `arithFrobAt R G Q` has order exactly the
> inertia degree `inertiaDegIn p S`.

Mathlib already supplies every surrounding fact — the decomposition group, the
residue Galois representation `Ideal.Quotient.stabilizerHom`, the inertia subgroup
and its cardinality `card_inertia_eq_ramificationIdxIn`, and the order of the
residue-field Frobenius `FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic` — but the
order computation tying them together was missing. This file provides it.

## Why it matters

Instantiating `R = ℤ`, `S = 𝓞 K`, `G = Gal`, and `Q` a prime over a rational prime
`p` whose residue extension has degree `d` discharges `∃ σ : Gal, orderOf σ = d`,
the Frobenius-cycle-type input both open problems reduce to. Concretely:

* `abel-ruffini-oq-07` (`X⁵ − X − 1`): a prime over `7` with inertia degree `3`
  gives an order-3 element, the missing piece toward `Gal ≅ S₅` and hence
  unsolvability by radicals.
* `inverse-galois-a5-oq-01`: the same lemma discharges the `three_dvd_gal_card`
  axiom (`exists_gal_order_three : ∃ σ : q.Gal, orderOf σ = 3`).

## Provenance

The main theorem `orderOf_arithFrobAt_eq_inertiaDegIn` and its three supporting
lemmas were proved by the Aristotle proof-search system (job `9c006ee6`) against a
Mathlib-only, self-contained statement. Aristotle ran against Mathlib `v4.28.0`, where
the inertia subgroup is spelled `Ideal.inertia`; the `stabilizerHom_injective` lemma was
re-derived here for the repository's pinned `v4.26.0` API (`Q.toAddSubgroup.inertia G`,
`Ideal.Quotient.ker_stabilizerHom`, `card_inertia_eq_ramificationIdxIn`). The other three
declarations are Aristotle's verbatim. `#print axioms` lists only `propext`,
`Classical.choice`, `Quot.sound` — no new axioms, no `sorry`.
-/

open Polynomial Algebra Ideal
open scoped Pointwise

namespace DedekindFrobeniusBridge

/-- The arithmetic Frobenius lies in the decomposition group (stabilizer) of `Q`. -/
lemma arithFrobAt_mem_stabilizer
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
    [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]
    (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)] :
    arithFrobAt R G Q ∈ MulAction.stabilizer G Q := by
  norm_num [ MulAction.mem_stabilizer_iff ];
  have h_comap : Q.comap (MulSemiringAction.toRingAut G S (arithFrobAt R G Q)) = Q := by
    convert ( IsArithFrobAt.arithFrobAt R G Q ).comap_eq using 1;
  convert congr_arg ( Ideal.map ( MulSemiringAction.toRingAut G S ( arithFrobAt R G Q ) ) ) h_comap.symm using 1;
  rw [ Ideal.map_comap_of_surjective _ ( MulSemiringAction.toRingAut G S ( arithFrobAt R G Q ) ).surjective ]

/-- The residue Galois representation `stabilizerHom` is injective at an unramified prime,
since its kernel is the (trivial) inertia subgroup. -/
lemma stabilizerHom_injective
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
    [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]
    [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S]
    [NoZeroSMulDivisors R S]
    (Q : Ideal S) [Q.IsMaximal] [Finite (S ⧸ Q)]
    [(Q.under R).IsMaximal]
    [Algebra.IsSeparable (R ⧸ Q.under R) (S ⧸ Q)]
    (hp : Q.under R ≠ ⊥)
    (hunram : Ideal.ramificationIdxIn (Q.under R) S = 1) :
    Function.Injective (Ideal.Quotient.stabilizerHom Q (Q.under R) G) := by
  -- The kernel of `stabilizerHom` is the inertia subgroup (`Ideal.Quotient.ker_stabilizerHom`);
  -- at an unramified prime the inertia group has cardinality `ramificationIdxIn = 1`, so it is
  -- trivial, hence `stabilizerHom` is injective.
  rw [← MonoidHom.ker_eq_bot_iff, Ideal.Quotient.ker_stabilizerHom]
  have h_card : Nat.card (Q.toAddSubgroup.inertia G) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn (G := G) (Q.under R) hp Q]
    exact hunram
  have h_inertia_trivial : Q.toAddSubgroup.inertia G = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ h_card
  rw [h_inertia_trivial, Subgroup.bot_subgroupOf]

/-- The order of the image of the arithmetic Frobenius under `stabilizerHom`, i.e. the residue
arithmetic Frobenius `x ↦ x ^ #(R/p)`, equals the inertia degree. -/
lemma orderOf_stabilizerHom_arithFrobAt
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
    [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]
    [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S]
    [NoZeroSMulDivisors R S]
    (Q : Ideal S) [Q.IsMaximal] [Finite (S ⧸ Q)]
    [(Q.under R).IsMaximal]
    (hmem : arithFrobAt R G Q ∈ MulAction.stabilizer G Q) :
    orderOf (Ideal.Quotient.stabilizerHom Q (Q.under R) G ⟨arithFrobAt R G Q, hmem⟩)
      = Ideal.inertiaDegIn (Q.under R) S := by
  -- Prove that the image of the arithmetic Frobenius under the stabilizerHom is the Frobenius automorphism of the residue field.
  have h_image : ∀ x : S ⧸ Q, ((Ideal.Quotient.stabilizerHom Q (Q.under R) G) ⟨arithFrobAt R G Q, hmem⟩) x = x ^ (Nat.card (R ⧸ (Q.under R))) := by
    intro x
    obtain ⟨b, hb⟩ : ∃ b : S, x = Ideal.Quotient.mk Q b := by
      exact ⟨ Classical.choose ( Ideal.Quotient.mk_surjective x ), Eq.symm ( Classical.choose_spec ( Ideal.Quotient.mk_surjective x ) ) ⟩;
    have := IsArithFrobAt.arithFrobAt R G Q;
    have := this.mk_apply b; aesop;
  convert FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic ( R ⧸ ( under R Q ) ) ( S ⧸ Q ) using 1;
  any_goals exact Ideal.Quotient.field _;
  rotate_left;
  rotate_left;
  convert Fintype.ofFinite ( R ⧸ under R Q );
  convert Finite.of_injective _ Ideal.algebraMap_quotient_injective;
  all_goals try infer_instance;
  · congr! 3;
    ext x; simp +decide [ h_image ] ;
    convert rfl;
    convert Fintype.card_eq_nat_card;
  · rw [ ← Ideal.inertiaDeg_algebraMap ]
    exact inertiaDegIn_eq_inertiaDeg (under R Q) Q G

/-- **Dedekind–Frobenius bridge lemma** (the genuine Mathlib gap shared by
`inverse-galois-a5-oq-01` and `abel-ruffini-oq-07`).

At a prime `Q` of `S` that is *unramified* over its contraction `p = Q.under R`
(i.e. `ramificationIdxIn p S = 1`), the canonical arithmetic Frobenius
`arithFrobAt R G Q` has order exactly the inertia degree `inertiaDegIn p S`.

Mathlib already supplies every surrounding fact; the missing link is this order
computation. Once available, instantiating `R = ℤ`, `S = 𝓞 K`, `G = Gal`,
`Q =` a prime over `7` with inertia degree `3` discharges
`∃ σ : q.Gal, orderOf σ = 3`, removing the `three_dvd_gal_card` axiom. -/
theorem orderOf_arithFrobAt_eq_inertiaDegIn
    {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
    [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]
    [IsDedekindDomain R] [IsDedekindDomain S] [Module.Finite R S]
    [NoZeroSMulDivisors R S]
    (Q : Ideal S) [Q.IsMaximal] [Finite (S ⧸ Q)]
    [(Q.under R).IsMaximal]
    [Algebra.IsSeparable (R ⧸ Q.under R) (S ⧸ Q)]
    (hp : Q.under R ≠ ⊥)
    (hunram : Ideal.ramificationIdxIn (Q.under R) S = 1) :
    orderOf (arithFrobAt R G Q) = Ideal.inertiaDegIn (Q.under R) S := by
  have hmem := arithFrobAt_mem_stabilizer (R := R) (G := G) Q
  calc orderOf (arithFrobAt R G Q)
      = orderOf (⟨arithFrobAt R G Q, hmem⟩ : MulAction.stabilizer G Q) :=
        orderOf_injective (Subgroup.subtype _) Subtype.val_injective ⟨arithFrobAt R G Q, hmem⟩
    _ = orderOf (Ideal.Quotient.stabilizerHom Q (Q.under R) G ⟨arithFrobAt R G Q, hmem⟩) :=
        (orderOf_injective _ (stabilizerHom_injective Q hp hunram) ⟨arithFrobAt R G Q, hmem⟩).symm
    _ = Ideal.inertiaDegIn (Q.under R) S :=
        orderOf_stabilizerHom_arithFrobAt Q hmem

end DedekindFrobeniusBridge
