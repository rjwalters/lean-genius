/-
  pq-Groups: Isomorphism uniqueness — abelian thread + full cyclic case
  (lagrange-theorem-oq-01-oq-01-oq-02)

  This answers the abelian portion of OQ-01-OQ-01-OQ-02 from Lagrange's Theorem OQ-01.

  **Open Question (OQ-01-OQ-01-OQ-02)**: The parent classification
  (entry `lagrange-theorem-oq-01-oq-01`) shows that for distinct primes `p < q`
  the *number* of isomorphism classes of groups of order `pq` is one when
  `p ∤ (q-1)` (only `ℤ/pq`) and two when `p ∣ (q-1)` (the cyclic group and a
  non-abelian semidirect product). The OQ asks to upgrade this *counting*
  statement to genuine *isomorphism uniqueness* using Mathlib's group-isomorphism
  machinery (`MulEquiv`): "any two groups of order `pq` are isomorphic to each
  other, for each of the two cases."

  This file resolves the **abelian** thread completely and self-containedly
  (depending only on Mathlib): *every* abelian group of order `pq` is cyclic, and
  hence any two abelian groups of order `pq` are isomorphic — each isomorphic to
  `Multiplicative (ZMod (pq))`. Crucially this needs **no** divisibility
  hypothesis, so it pins down the abelian isomorphism class in *both* branches of
  the classification (in the `p ∣ (q-1)` branch the two classes are exactly
  "abelian = cyclic `ℤ/pq`" and "non-abelian = `ℤ/q ⋊ ℤ/p`"; this file fully
  resolves the first).

  **Proof of the key step** (`pq_abelian_isCyclic`): Cauchy's theorem
  (`exists_prime_orderOf_dvd_card`) supplies `a` of order `p` and `b` of order `q`.
  Since the group is abelian, `a` and `b` commute, and as `p, q` are coprime
  `Commute.orderOf_mul_eq_mul_orderOf_of_coprime` gives `orderOf (a*b) = pq = |G|`,
  so `isCyclic_of_orderOf_eq_card` makes `G` cyclic. Then
  `mulEquivOfCyclicCardEq` / `zmodCyclicMulEquiv` deliver the isomorphisms.

  **The cyclic case (Part IV) is now resolved too**, self-containedly from Mathlib's
  Sylow theory: when `¬ p ∣ (q-1)` and `¬ q ∣ (p-1)`, *every* group of order `pq`
  (not merely the abelian ones) is cyclic. The Sylow counts `nₚ, n_q` are forced to
  `1` (each divides the index of a Sylow subgroup and is `≡ 1` modulo its prime), so
  both Sylow subgroups are normal; a finite group all of whose Sylow subgroups are
  normal is nilpotent (`isNilpotent_of_finite_tfae`), and a finite nilpotent group of
  squarefree order is cyclic (it is a Z-group — `IsZGroup.of_squarefree` — and a
  nilpotent Z-group is cyclic). For `p < q` the side condition `¬ q ∣ (p-1)` is
  automatic, recovering the classical criterion. Consequently any two groups of order
  `pq` in this branch are isomorphic (`pq_cyclic_iso`), e.g. all groups of order `15`
  or `35`.

  **Scope.** All three isomorphism classes are now resolved. The `p ∣ (q-1)`
  *non-abelian* uniqueness — "any two non-cyclic groups of order `pq` are isomorphic"
  — is proved in Part IX (`pq_noncyclic_iso`), built on the full internal
  semidirect-product recognition `G ≃* ℤ/q ⋊ ℤ/p` (Part VIII), the common range of
  nontrivial actions into the cyclic `Aut(ℤ/q)` (Part VII), and the fact that a
  trivial action collapses to the cyclic direct product (Part IX). The parent
  dependency `Proofs.SylowTheoremOQ01` does not compile on
  Mathlib v4.26.0 (renamed/removed lemmas), so this file deliberately avoids it and
  imports only Mathlib, remaining fully machine-checked with `0` sorries and `0`
  axioms (every theorem depends on exactly `[propext, Classical.choice, Quot.sound]`).

  **Key Mathlib tools**:
  - `exists_prime_orderOf_dvd_card` (Cauchy) and
    `Commute.orderOf_mul_eq_mul_orderOf_of_coprime` — produce an element of order `pq`.
  - `isCyclic_of_orderOf_eq_card` — a generator of full order makes `G` cyclic.
  - `mulEquivOfCyclicCardEq` — two cyclic groups of equal `Nat.card` are isomorphic.
  - `zmodCyclicMulEquiv` — a cyclic group `≅ Multiplicative (ZMod (Nat.card G))`.
  - `card_sylow_modEq_one`, `Sylow.card_dvd_index` — Sylow's counting theorem (Part IV).
  - `Sylow.normal_of_subsingleton`, `isNilpotent_of_finite_tfae` — all-Sylow-normal ⟹
    nilpotent; `IsZGroup.of_squarefree` and the nilpotent-Z-group `IsCyclic` instance.

  References:
  - Dummit, D. & Foote, R. (2004). Abstract Algebra, §4.5, Theorem 14.
  - Conrad, K. "Groups of order pq." Expository notes.

  Tags: group-theory, lagrange, pq-groups, classification, isomorphism, MulEquiv,
        cyclic-groups, abelian-groups, Sylow, Z-group, nilpotent, ZMod, finite-groups
-/

import Mathlib

open Subgroup Fintype

namespace LagrangeOQ01OQ01OQ02

/-!
## Part I: Abelian groups of order `pq` are cyclic

A finite abelian group whose order is a product of two distinct primes is cyclic.
Cauchy's theorem gives an element `a` of order `p` and an element `b` of order
`q`; the group being abelian they commute, and as `p, q` are coprime the product
`a * b` has order `pq = |G|`, so `G` is cyclic.  No divisibility hypothesis on
`p, q` is needed, so this also identifies the abelian class inside the non-cyclic
`p ∣ (q-1)` branch of the classification.
-/

/-- **Abelian groups of order `pq` are cyclic.** For distinct primes `p ≠ q`,
    every abelian group of order `pq` is cyclic (squarefree order). -/
theorem pq_abelian_isCyclic {G : Type*} [CommGroup G] [Fintype G]
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hcard : Fintype.card G = p * q) : IsCyclic G := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨a, ha⟩ : ∃ a : G, orderOf a = p :=
    exists_prime_orderOf_dvd_card p (by rw [hcard]; exact Dvd.intro q rfl)
  obtain ⟨b, hb⟩ : ∃ b : G, orderOf b = q :=
    exists_prime_orderOf_dvd_card q (by rw [hcard]; exact Dvd.intro_left p rfl)
  have hco : (orderOf a).Coprime (orderOf b) := by
    rw [ha, hb]; exact (Nat.coprime_primes hp hq).2 hpq
  have hmul : orderOf (a * b) = p * q := by
    rw [(Commute.all a b).orderOf_mul_eq_mul_orderOf_of_coprime hco, ha, hb]
  exact isCyclic_of_orderOf_eq_card (a * b) (by rw [hmul, Nat.card_eq_fintype_card, hcard])

/-!
## Part II: Abelian isomorphism uniqueness

Two cyclic groups of the same cardinality are isomorphic (`mulEquivOfCyclicCardEq`),
and a cyclic group is isomorphic to `Multiplicative (ZMod (Nat.card G))`
(`zmodCyclicMulEquiv`).  Combined with Part I, this gives the abelian uniqueness.
-/

/-- **Abelian-case uniqueness.** For distinct primes `p ≠ q`, any two abelian
    groups of order `pq` are isomorphic. -/
theorem pq_abelian_iso {G H : Type*} [CommGroup G] [CommGroup H] [Fintype G] [Fintype H]
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hG : Fintype.card G = p * q) (hH : Fintype.card H = p * q) :
    Nonempty (G ≃* H) := by
  haveI : IsCyclic G := pq_abelian_isCyclic hp hq hpq hG
  haveI : IsCyclic H := pq_abelian_isCyclic hp hq hpq hH
  refine ⟨mulEquivOfCyclicCardEq ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hG, hH]

/-- **Abelian-case canonical form.** For distinct primes `p ≠ q`, every abelian
    group of order `pq` is isomorphic to `Multiplicative (ZMod (pq))`. -/
theorem pq_abelian_iso_zmod {G : Type*} [CommGroup G] [Fintype G]
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hcard : Fintype.card G = p * q) :
    Nonempty (G ≃* Multiplicative (ZMod (p * q))) := by
  haveI hc : IsCyclic G := pq_abelian_isCyclic hp hq hpq hcard
  have hN : Nat.card G = p * q := by rw [Nat.card_eq_fintype_card, hcard]
  exact ⟨hN ▸ (zmodCyclicMulEquiv hc).symm⟩

/-!
## Part III: Concrete corollaries

For each squarefree order `pq` the abelian isomorphism class is now a direct
instance of the theorems above.  Order `15 = 3·5` and `35 = 5·7` lie in the
cyclic branch, while order `6 = 2·3` lies in the non-cyclic branch (`2 ∣ 2`) where
`S₃` is the other class — yet in every case the *abelian* group of that order is
uniquely `ℤ/pq`.
-/

/-- Every abelian group of order `6` is isomorphic to `ℤ/6` (the non-abelian class
    of that order being `S₃`). -/
theorem order_6_abelian_unique
    {G : Type*} [CommGroup G] [Fintype G] (hG : Fintype.card G = 6) :
    Nonempty (G ≃* Multiplicative (ZMod 6)) :=
  pq_abelian_iso_zmod (p := 2) (q := 3) (by norm_num) (by norm_num) (by norm_num)
    (by rw [hG])

/-- Every abelian group of order `15` is isomorphic to `ℤ/15`. -/
theorem order_15_abelian_unique
    {G : Type*} [CommGroup G] [Fintype G] (hG : Fintype.card G = 15) :
    Nonempty (G ≃* Multiplicative (ZMod 15)) :=
  pq_abelian_iso_zmod (p := 3) (q := 5) (by norm_num) (by norm_num) (by norm_num)
    (by rw [hG])

/-- Every abelian group of order `35` is isomorphic to `ℤ/35`. -/
theorem order_35_abelian_unique
    {G : Type*} [CommGroup G] [Fintype G] (hG : Fintype.card G = 35) :
    Nonempty (G ≃* Multiplicative (ZMod 35)) :=
  pq_abelian_iso_zmod (p := 5) (q := 7) (by norm_num) (by norm_num) (by norm_num)
    (by rw [hG])

/-- Any two abelian groups of order `15` are isomorphic to each other. -/
theorem order_15_abelian_pair
    {G H : Type*} [CommGroup G] [CommGroup H] [Fintype G] [Fintype H]
    (hG : Fintype.card G = 15) (hH : Fintype.card H = 15) :
    Nonempty (G ≃* H) :=
  pq_abelian_iso (p := 3) (q := 5) (by norm_num) (by norm_num) (by norm_num)
    (by rw [hG]) (by rw [hH])

/-!
## Part IV: The cyclic case — *every* group of order `pq` is cyclic

Part II showed the *abelian* groups of order `pq` form a single isomorphism class.
Sylow theory now upgrades this to the full **cyclic branch** of the classification:
when neither prime divides the other minus one (`¬ p ∣ (q-1)` and `¬ q ∣ (p-1)`),
*both* Sylow subgroups are normal — with **no** commutativity hypothesis on `G`.
A finite group all of whose Sylow subgroups are normal is nilpotent, and a finite
nilpotent group of squarefree order is cyclic (it is a *Z-group* — every Sylow
subgroup is cyclic — and a nilpotent Z-group is cyclic).

For `p < q` the side condition `¬ q ∣ (p-1)` is automatic (`0 < p-1 < q`), so the
single hypothesis `p ∤ (q-1)` already forces cyclicity, recovering the classical
statement "`|G| = pq`, `p < q`, `p ∤ q-1 ⟹ G` cyclic" (e.g. every group of order
`15` or `35` is cyclic, whereas order `6 = 2·3` escapes because `2 ∣ (3-1)`).

**Key Mathlib tools**:
- `card_sylow_modEq_one`, `Sylow.card_dvd_index` — Sylow's counting theorem forces
  `nₚ = n_q = 1`.
- `Sylow.normal_of_subsingleton`, `isNilpotent_of_finite_tfae` — all Sylow normal ⟹ nilpotent.
- `IsZGroup.of_squarefree` and the nilpotent-Z-group `IsCyclic` instance — finish.
-/

/-- For a group of order `pq` (`p ≠ q` primes) with `p ∤ (q-1)`, there is exactly one
    Sylow `p`-subgroup. The count `nₚ` divides the index `q` of a Sylow `p`-subgroup and
    satisfies `nₚ ≡ 1 (mod p)`; the alternative `nₚ = q` would give `q ≡ 1 (mod p)`,
    i.e. `p ∣ (q-1)`, which is excluded. -/
private theorem pq_card_sylow_one {G : Type*} [Group G] [Fintype G] {p q : ℕ}
    [Fact p.Prime] (hq : Nat.Prime q) (hpq : p ≠ q)
    (hcard : Fintype.card G = p * q) (hpd : ¬ p ∣ (q - 1)) :
    Nat.card (Sylow p G) = 1 := by
  have hp : Nat.Prime p := Fact.out
  have hpnq : ¬ p ∣ q := (hp.coprime_iff_not_dvd).mp ((Nat.coprime_primes hp hq).mpr hpq)
  -- a Sylow `p`-subgroup has order `p`, hence index `q`
  have hcardP : Nat.card (default : Sylow p G) = p := by
    rw [Sylow.card_eq_multiplicity, Nat.card_eq_fintype_card, hcard,
        Nat.factorization_mul hp.pos.ne' hq.pos.ne', Finsupp.add_apply,
        hp.factorization_self, Nat.factorization_eq_zero_of_not_dvd hpnq, add_zero, pow_one]
  have hidx : (default : Sylow p G).index = q := by
    have hmc := (default : Sylow p G).card_mul_index
    rw [hcardP, Nat.card_eq_fintype_card, hcard] at hmc
    exact Nat.eq_of_mul_eq_mul_left hp.pos hmc
  have hdvd : Nat.card (Sylow p G) ∣ q := hidx ▸ (default : Sylow p G).card_dvd_index
  have hmod : Nat.card (Sylow p G) ≡ 1 [MOD p] := card_sylow_modEq_one p G
  rcases hq.eq_one_or_self_of_dvd _ hdvd with h1 | hqeq
  · exact h1
  · exact absurd ((Nat.modEq_iff_dvd' hq.one_lt.le).mp (hqeq ▸ hmod).symm) hpd

/-- **Cyclic case (full).** For distinct primes `p ≠ q` with `¬ p ∣ (q-1)` and
    `¬ q ∣ (p-1)`, *every* group of order `pq` is cyclic — not merely the abelian ones.
    Both Sylow subgroups are forced normal (Sylow counting), making `G` nilpotent; being
    a Z-group of squarefree order it is then cyclic. -/
theorem pq_isCyclic {G : Type*} [Group G] [Fintype G] {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hpd : ¬ p ∣ (q - 1)) (hqd : ¬ q ∣ (p - 1))
    (hcard : Fintype.card G = p * q) : IsCyclic G := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  -- squarefree order ⟹ Z-group (every Sylow subgroup is cyclic of prime order)
  haveI : IsZGroup G := by
    apply IsZGroup.of_squarefree
    rw [Nat.card_eq_fintype_card, hcard]
    exact (Nat.squarefree_mul ((Nat.coprime_primes hp hq).mpr hpq)).mpr
      ⟨hp.prime.squarefree, hq.prime.squarefree⟩
  -- every Sylow subgroup of `G` is normal
  have hnorm : ∀ (r : ℕ) (_ : Fact r.Prime) (P : Sylow r G), (P : Subgroup G).Normal := by
    intro r hr P
    by_cases hrp : r = p
    · subst hrp
      haveI : Subsingleton (Sylow r G) :=
        (Nat.card_eq_one_iff_unique.mp (pq_card_sylow_one hq hpq hcard hpd)).1
      exact Sylow.normal_of_subsingleton P
    · by_cases hrq : r = q
      · subst hrq
        haveI : Subsingleton (Sylow r G) :=
          (Nat.card_eq_one_iff_unique.mp
            (pq_card_sylow_one (p := r) (q := p) hp (Ne.symm hpq)
              (by rw [hcard]; ring) hqd)).1
        exact Sylow.normal_of_subsingleton P
      · -- `r ∤ pq`: the Sylow `r`-subgroup is trivial, hence normal
        have hrnp : ¬ r ∣ p * q := by
          intro hdv
          rcases (Nat.Prime.dvd_mul hr.out).mp hdv with h | h
          · exact hrp ((Nat.prime_dvd_prime_iff_eq hr.out hp).mp h)
          · exact hrq ((Nat.prime_dvd_prime_iff_eq hr.out hq).mp h)
        have hPbot : (P : Subgroup G) = ⊥ := by
          apply Subgroup.eq_bot_of_card_eq
          rw [Sylow.card_eq_multiplicity, Nat.card_eq_fintype_card, hcard,
              Nat.factorization_eq_zero_of_not_dvd hrnp, pow_zero]
        rw [hPbot]; infer_instance
  -- all Sylow subgroups normal ⟹ `G` nilpotent ⟹ (Z-group, squarefree) cyclic
  haveI : Group.IsNilpotent G := (isNilpotent_of_finite_tfae (G := G)).out 3 0 |>.mp hnorm
  infer_instance

/-- **Cyclic-case uniqueness.** Under the same hypotheses, any two groups of order `pq`
    are isomorphic to each other (each being cyclic of cardinality `pq`). -/
theorem pq_cyclic_iso {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H] {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (hpd : ¬ p ∣ (q - 1)) (hqd : ¬ q ∣ (p - 1))
    (hG : Fintype.card G = p * q) (hH : Fintype.card H = p * q) :
    Nonempty (G ≃* H) := by
  haveI : IsCyclic G := pq_isCyclic hp hq hpq hpd hqd hG
  haveI : IsCyclic H := pq_isCyclic hp hq hpq hpd hqd hH
  refine ⟨mulEquivOfCyclicCardEq ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hG, hH]

/-- **Classical cyclic criterion.** For primes `p < q` with `p ∤ (q-1)`, every group of
    order `pq` is cyclic. The side condition `¬ q ∣ (p-1)` is automatic since
    `0 < p-1 < q`. -/
theorem pq_isCyclic_of_lt {G : Type*} [Group G] [Fintype G] {p q : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hlt : p < q)
    (hpd : ¬ p ∣ (q - 1)) (hcard : Fintype.card G = p * q) : IsCyclic G := by
  refine pq_isCyclic hp hq (Nat.ne_of_lt hlt) hpd ?_ hcard
  intro hdvd
  have hp2 := hp.two_le
  have hle := Nat.le_of_dvd (by omega) hdvd
  omega

/-!
## Part V: Concrete corollaries of the cyclic branch

Orders `15 = 3·5` and `35 = 5·7` lie in the cyclic branch (`3 ∤ 4`, `5 ∤ 6`), so *every*
group of those orders is cyclic — strengthening the abelian-only statements of Part III.
-/

/-- Every group of order `15` is cyclic (not just the abelian ones): `15 = 3·5`, `3 ∤ 4`. -/
theorem order_15_cyclic {G : Type*} [Group G] [Fintype G] (hG : Fintype.card G = 15) :
    IsCyclic G :=
  pq_isCyclic_of_lt (p := 3) (q := 5) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [hG])

/-- Every group of order `35` is cyclic: `35 = 5·7`, `5 ∤ 6`. -/
theorem order_35_cyclic {G : Type*} [Group G] [Fintype G] (hG : Fintype.card G = 35) :
    IsCyclic G :=
  pq_isCyclic_of_lt (p := 5) (q := 7) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [hG])

/-- Any two groups of order `15` are isomorphic to each other. -/
theorem order_15_iso {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    (hG : Fintype.card G = 15) (hH : Fintype.card H = 15) : Nonempty (G ≃* H) := by
  haveI : IsCyclic G := order_15_cyclic hG
  haveI : IsCyclic H := order_15_cyclic hH
  exact ⟨mulEquivOfCyclicCardEq
    (by rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hG, hH])⟩

/-
  ## Part VI — Non-abelian uniqueness infrastructure: the iso type of a semidirect
  product is determined by the *range* of its action map.

  The only branch of OQ-01-OQ-01-OQ-02 not settled above is the `p ∣ (q-1)`
  *non-abelian* uniqueness: any two non-cyclic groups of order `pq` are isomorphic.
  Classically each such group is an internal semidirect product `ℤ/q ⋊ ℤ/p` for some
  nontrivial action `ℤ/p →* Aut(ℤ/q)`, and the proof reduces to: *different nontrivial
  actions still give isomorphic products.*

  This part proves the structural engine for that reduction, fully and self-containedly
  from Mathlib. The key observation is that the isomorphism type of `N ⋊[φ] G` depends
  only on the **image** `φ.range ≤ MulAut N` of the action map, not on the particular
  homomorphism `φ`:

  - `autOfRangeEq` / `exists_mulEquiv_comp_of_range_eq`: two injective homs `f, g` with
    `f.range = g.range` differ by a source automorphism `α`, i.e. `g = f ∘ α`. The
    witness is the composite `G ≃* g.range ≃* f.range ≃* G` built from
    `MonoidHom.ofInjective` and `MulEquiv.subgroupCongr`.
  - `semidirectProductIsoOfRangeEq`: feeding that `α` into Mathlib's
    `SemidirectProduct.congr` (with `fn = id` on `N`) yields `N ⋊[g] G ≃* N ⋊[f] G`.
  - `injective_of_prime_card`: a nontrivial hom out of a group of prime order is
    injective (its kernel divides the prime, so is `⊥` or `⊤`; `⊤` would force the map
    to be `1`).
  - `semidirectProductIso_of_nontrivial_range_eq`: the capstone — two *nontrivial*
    action maps from a prime-order group with equal range give isomorphic semidirect
    products.

  **What remains for full non-abelian uniqueness** (both facts are now closed below;
  see Parts VII and VIII):
  1. *Internal recognition* (**RESOLVED in Part VIII**): every group of order `pq`
     (`p < q`) is `≃*` to an internal semidirect product `Q ⋊ P` of its Sylow
     subgroups (`Q` the normal Sylow `q`-subgroup). See
     `exists_internalSemidirect_of_card_pq`, built on Mathlib's
     `SemidirectProduct.mulEquivSubgroup`.
  2. *Common range* (**RESOLVED in Part VII**): any two nontrivial `φ₁, φ₂ : ℤ/p →*
     Aut(ℤ/q)` have equal range — the unique order-`p` subgroup of the cyclic group
     `Aut(ℤ/q) ≅ (ℤ/q)ˣ`. See `range_eq_of_nontrivial_prime_card`.

  Given (1) and (2), `semidirectProductIso_of_nontrivial_range_eq` closes the
  non-abelian case; Part VII supplies (2) and the hypothesis-free capstone
  `semidirectProductIso_of_nontrivial_into_cyclic`, Part VIII supplies (1). The only
  residual mathematical input is that the conjugation action is *nontrivial* in the
  non-cyclic case. This part delivers the reusable middle link with `0` sorries and
  `0` axioms.
-/

variable {Γ Δ : Type*} [Group Γ] [Group Δ]

/-- The source automorphism `α : Γ ≃* Γ` witnessing that two injective homomorphisms
    `f g : Γ →* Δ` with equal range differ by precomposition: `g = f ∘ α`. The witness is
    the composite `Γ ≃* g.range ≃* f.range ≃* Γ`. -/
noncomputable def autOfRangeEq {f g : Γ →* Δ} (hf : Function.Injective f)
    (hg : Function.Injective g) (hr : f.range = g.range) : Γ ≃* Γ :=
  (MonoidHom.ofInjective hg).trans
    ((MulEquiv.subgroupCongr hr.symm).trans (MonoidHom.ofInjective hf).symm)

/-- The defining property of `autOfRangeEq`: `g x = f (α x)` for all `x`. -/
theorem autOfRangeEq_spec {f g : Γ →* Δ} (hf : Function.Injective f)
    (hg : Function.Injective g) (hr : f.range = g.range) (x : Γ) :
    g x = f (autOfRangeEq hf hg hr x) := by
  rw [autOfRangeEq]
  simp only [MulEquiv.trans_apply]
  rw [MonoidHom.apply_ofInjective_symm hf, MulEquiv.subgroupCongr_apply,
      MonoidHom.ofInjective_apply hg]

/-- Two injective homomorphisms with the same range differ by an automorphism of the
    source: there is `α : Γ ≃* Γ` with `g = f ∘ α`. -/
theorem exists_mulEquiv_comp_of_range_eq {f g : Γ →* Δ} (hf : Function.Injective f)
    (hg : Function.Injective g) (hr : f.range = g.range) :
    ∃ α : Γ ≃* Γ, ∀ x, g x = f (α x) :=
  ⟨autOfRangeEq hf hg hr, autOfRangeEq_spec hf hg hr⟩

/-- **Range determines the semidirect product.** If two action maps `f g : Γ →* MulAut N`
    are injective and have equal range, the associated semidirect products are isomorphic:
    the isomorphism type of `N ⋊ Γ` depends only on the *image* of the action map. The
    isomorphism keeps `N` fixed and twists `Γ` by `autOfRangeEq`, via
    `SemidirectProduct.congr`. -/
noncomputable def semidirectProductIsoOfRangeEq {N : Type*} [Group N]
    {f g : Γ →* MulAut N} (hf : Function.Injective f) (hg : Function.Injective g)
    (hr : f.range = g.range) :
    SemidirectProduct N Γ g ≃* SemidirectProduct N Γ f :=
  SemidirectProduct.congr (MulEquiv.refl N) (autOfRangeEq hf hg hr) <| by
    intro x
    ext n
    simp only [MulEquiv.trans_apply, MulEquiv.refl_apply, autOfRangeEq_spec hf hg hr x]

/-- A homomorphism out of a group of prime order is injective unless it is trivial: its
    kernel has order dividing the prime, hence is `⊥` (injective) or `⊤` (forcing the map
    to be `1`). -/
theorem injective_of_prime_card [Fintype Γ] {p : ℕ} (hp : p.Prime)
    (hcard : Fintype.card Γ = p) {f : Γ →* Δ} (hf : f ≠ 1) : Function.Injective f := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have hNat : Nat.card Γ = p := by rw [Nat.card_eq_fintype_card, hcard]
  have hdvd : Nat.card f.ker ∣ p := hNat ▸ Subgroup.card_subgroup_dvd_card f.ker
  rcases (hp.eq_one_or_self_of_dvd _ hdvd) with h1 | hpeq
  · exact f.ker.eq_bot_of_card_eq h1
  · exfalso
    apply hf
    have htop : f.ker = ⊤ := Subgroup.eq_top_of_card_eq f.ker (by rw [hpeq, hNat])
    ext x
    have hx : x ∈ f.ker := htop ▸ Subgroup.mem_top x
    simpa [MonoidHom.mem_ker] using hx

/-- **Capstone (non-abelian `pq` thread).** Two *nontrivial* action maps from a group of
    prime order `p` with equal range give isomorphic semidirect products. With the two
    standard facts noted above (internal recognition; all nontrivial `ℤ/p`-actions on
    `ℤ/q` share the unique order-`p` subgroup of the cyclic `Aut(ℤ/q)`), this pins the
    non-abelian isomorphism class of groups of order `pq`. -/
theorem semidirectProductIso_of_nontrivial_range_eq {N : Type*} [Group N] [Fintype Γ]
    {p : ℕ} (hp : p.Prime) (hcard : Fintype.card Γ = p)
    {f g : Γ →* MulAut N} (hf : f ≠ 1) (hg : g ≠ 1) (hr : f.range = g.range) :
    Nonempty (SemidirectProduct N Γ g ≃* SemidirectProduct N Γ f) :=
  ⟨semidirectProductIsoOfRangeEq (injective_of_prime_card hp hcard hf)
    (injective_of_prime_card hp hcard hg) hr⟩

/-
  ## Part VII — Common range: discharging the hypothesis of Part VI's capstone.

  Part VI's `semidirectProductIso_of_nontrivial_range_eq` *assumes* `f.range = g.range`.
  Here we **prove** that hypothesis for the case relevant to `pq`-groups: when the
  target `K` (`= Aut N`) is a finite **cyclic** group, any two nontrivial maps out of
  a group of prime order automatically have equal range. This settles the second of
  the two "documented standard facts" listed at the top of Part VI (*common range*),
  leaving only *internal recognition* (the Mathlib normal-complement gap) for full
  non-abelian uniqueness.

  The engine is **uniqueness of subgroups of a given order in a cyclic group**: every
  subgroup `H` of a finite cyclic `K` equals the `(Nat.card H)`-torsion subgroup
  `(powMonoidHom (Nat.card H)).ker` — the unique subgroup of that order. Indeed `H` is
  contained in it (`h ^ (Nat.card H) = 1` for `h ∈ H`, Lagrange) and that torsion
  subgroup has card `gcd(|K|, Nat.card H) = Nat.card H`, so the inclusion is an
  equality (`Subgroup.eq_of_le_of_card_ge`). The torsion-card computation is Mathlib's
  `IsCyclic.card_powMonoidHom_ker`. Hence two subgroups of equal order coincide, and
  the two prime-order ranges (both `≅ Γ` via `MonoidHom.ofInjective`) are equal.
-/

section CommonRange

variable {K : Type*} [CommGroup K] [Finite K] [IsCyclic K]

/-- **Subgroups of a finite cyclic group are pinned down by their order.** A subgroup
    `H` of a finite cyclic group equals the `(Nat.card H)`-torsion subgroup
    `(powMonoidHom (Nat.card H)).ker`, the unique subgroup of that order. -/
theorem subgroup_eq_powMonoidHom_ker (H : Subgroup K) :
    H = (powMonoidHom (Nat.card H) : K →* K).ker := by
  have hdvd : Nat.card H ∣ Nat.card K := Subgroup.card_subgroup_dvd_card H
  have hcardker : Nat.card (powMonoidHom (Nat.card H) : K →* K).ker = Nat.card H := by
    rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right_iff_dvd.2 hdvd]
  have hle : H ≤ (powMonoidHom (Nat.card H) : K →* K).ker := by
    intro x hx
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    have h1 : (⟨x, hx⟩ : H) ^ Nat.card H = 1 := pow_card_eq_one'
    have h2 := congrArg (Subgroup.subtype H) h1
    rw [map_pow, map_one] at h2
    simpa using h2
  exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcardker)

/-- **Uniqueness of subgroups of given order in a cyclic group.** Two subgroups of a
    finite cyclic group with the same cardinality are equal. -/
theorem subgroup_eq_of_card_eq {H₁ H₂ : Subgroup K} (h : Nat.card H₁ = Nat.card H₂) :
    H₁ = H₂ := by
  rw [subgroup_eq_powMonoidHom_ker H₁, subgroup_eq_powMonoidHom_ker H₂, h]

/-- **Common range.** Any two *nontrivial* homomorphisms from a group of prime order
    into a finite cyclic group have the same range — both are the unique subgroup of
    order `p` of the cyclic target. This discharges the `f.range = g.range` hypothesis
    of `semidirectProductIso_of_nontrivial_range_eq`. -/
theorem range_eq_of_nontrivial_prime_card [Fintype Γ]
    {p : ℕ} (hp : p.Prime) (hcard : Fintype.card Γ = p)
    {f g : Γ →* K} (hf : f ≠ 1) (hg : g ≠ 1) :
    f.range = g.range := by
  have hif : Function.Injective f := injective_of_prime_card hp hcard hf
  have hig : Function.Injective g := injective_of_prime_card hp hcard hg
  apply subgroup_eq_of_card_eq
  rw [(Nat.card_congr (MonoidHom.ofInjective hif).toEquiv).symm,
      (Nat.card_congr (MonoidHom.ofInjective hig).toEquiv).symm]

/-- **Capstone (hypothesis-free, cyclic-`Aut` case).** When `Aut N` is finite cyclic,
    *any* two nontrivial action maps from a group of prime order `p` give isomorphic
    semidirect products — no equal-range hypothesis required, since Part VII supplies
    it automatically. Combined with internal recognition (every non-cyclic group of
    order `pq` is such a semidirect product), this pins the non-abelian isomorphism
    class of groups of order `pq`: `Aut (ℤ/q) ≅ (ℤ/q)ˣ` is cyclic for prime `q`. -/
theorem semidirectProductIso_of_nontrivial_into_cyclic {N : Type*} [Group N]
    [Finite (MulAut N)] [IsCyclic (MulAut N)] [Fintype Γ]
    {p : ℕ} (hp : p.Prime) (hcard : Fintype.card Γ = p)
    {f g : Γ →* MulAut N} (hf : f ≠ 1) (hg : g ≠ 1) :
    Nonempty (SemidirectProduct N Γ g ≃* SemidirectProduct N Γ f) := by
  letI : CommGroup (MulAut N) := IsCyclic.commGroup
  exact semidirectProductIso_of_nontrivial_range_eq hp hcard hf hg
    (range_eq_of_nontrivial_prime_card hp hcard hf hg)

end CommonRange

/-
  ## Part VIII — Internal recognition: every group of order `pq` (`p < q`) is an
  internal semidirect product `Q ⋊ P` with `Q` the *normal* Sylow `q`-subgroup.

  This supplies the *first* of Part VI's two standard facts — internal recognition —
  the one previously flagged as a Mathlib gap. In fact Mathlib provides the missing
  link, `SemidirectProduct.mulEquivSubgroup`, which turns a normal subgroup together
  with a complement into an internal semidirect product `H ⋊ K ≃* G`. For `|G| = pq`
  with `p < q`:

  - the Sylow `q`-subgroup is **normal** — its count divides `p` and is `≡ 1 (mod q)`,
    forcing `1` because `q > p` (so `q ∤ (p-1)` automatically), via `pq_card_sylow_one`
    with the two primes swapped;
  - the Sylow `p`-subgroup is a **complement** of coprime order
    (`|Q|·|P| = q·p = |G|`, `gcd(q,p)=1`), via `Subgroup.isComplement'_of_coprime`;
  - `mulEquivSubgroup` then assembles `G ≃* Q ⋊ P`.

  With Part VII (common range) and Part VI (range determines the product), the
  structural reduction of non-abelian `pq`-uniqueness is now backed by lemmas all in
  hand; the only residual mathematical input is that the conjugation action is
  *nontrivial* in the non-cyclic case (a trivial action would make `G ≅ Q × P` cyclic).
-/

/-- **Internal semidirect recognition for groups of order `pq`.** For primes `p < q`
    with `|G| = pq`, `G` is (isomorphic to) an internal semidirect product `Q ⋊ P` of
    its Sylow subgroups, with `Q` the normal Sylow `q`-subgroup (`|Q| = q`) and `P` a
    Sylow `p`-subgroup (`|P| = p`). This discharges the *internal recognition* fact
    that Part VI listed as a Mathlib gap, using `SemidirectProduct.mulEquivSubgroup`. -/
theorem exists_internalSemidirect_of_card_pq {G : Type*} [Group G] [Fintype G]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpltq : p < q)
    (hcard : Fintype.card G = p * q) :
    ∃ (Q P : Subgroup G) (_ : Q.Normal) (φ : P →* MulAut Q),
      Nat.card Q = q ∧ Nat.card P = p ∧
        Nonempty (SemidirectProduct Q P φ ≃* G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hpq : p ≠ q := Nat.ne_of_lt hpltq
  have hpnq : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
  have hqnp : ¬ q ∣ p := fun h => absurd (Nat.le_of_dvd hp.pos h) (by omega)
  set Q := (default : Sylow q G) with hQ
  set P := (default : Sylow p G) with hP
  -- Cardinalities of the two Sylow subgroups.
  have hcardP : Nat.card (P : Subgroup G) = p := by
    rw [hP, Sylow.card_eq_multiplicity, Nat.card_eq_fintype_card, hcard,
        Nat.factorization_mul hp.pos.ne' hq.pos.ne', Finsupp.add_apply,
        hp.factorization_self, Nat.factorization_eq_zero_of_not_dvd hpnq, add_zero, pow_one]
  have hcardQ : Nat.card (Q : Subgroup G) = q := by
    rw [hQ, Sylow.card_eq_multiplicity, Nat.card_eq_fintype_card, hcard,
        Nat.factorization_mul hp.pos.ne' hq.pos.ne', Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hqnp, hq.factorization_self, zero_add, pow_one]
  -- The Sylow `q`-subgroup is unique (count `≡ 1 mod q` divides `p`, and `q > p`),
  -- hence normal.
  have hsylowq : Nat.card (Sylow q G) = 1 :=
    pq_card_sylow_one (p := q) (q := p) hp (Ne.symm hpq) (by rw [hcard]; ring)
      (by intro h; have := Nat.le_of_dvd (by have := hp.two_le; omega) h; omega)
  haveI : Subsingleton (Sylow q G) := (Nat.card_eq_one_iff_unique.mp hsylowq).1
  haveI hQnormal : (Q : Subgroup G).Normal := Sylow.normal_of_subsingleton Q
  -- `P` is a complement of `Q` (coprime orders multiplying to `|G|`).
  have hcompl : (Q : Subgroup G).IsComplement' (P : Subgroup G) := by
    apply Subgroup.isComplement'_of_coprime
    · rw [hcardQ, hcardP, Nat.card_eq_fintype_card, hcard]; ring
    · rw [hcardQ, hcardP]; exact (Nat.coprime_primes hq hp).mpr (Ne.symm hpq)
  exact ⟨(Q : Subgroup G), (P : Subgroup G), hQnormal, _, hcardQ, hcardP,
    ⟨SemidirectProduct.mulEquivSubgroup hcompl⟩⟩

/-
  ## Part IX — Nontrivial action and FULL non-abelian uniqueness.

  Parts VI–VIII reduced non-abelian `pq`-uniqueness to one residual mathematical
  input: the conjugation action of the internal semidirect decomposition is
  *nontrivial* whenever `G` is non-cyclic. We discharge it here and assemble the
  complete statement.

  - `semidirectProduct_trivial_isCyclic`: a *trivial* action over coprime cyclic
    factors collapses the semidirect product to the **direct** product `N × Γ`
    (`SemidirectProduct.mulEquivProd`), which is cyclic (`Group.isCyclic_prod_iff`).
  - `action_ne_one_of_not_isCyclic`: the contrapositive — a non-cyclic semidirect
    product over coprime cyclic factors must have a nontrivial action.
  - `pq_noncyclic_iso`: **any two non-cyclic groups of order `pq` (`p < q`) are
    isomorphic.** Each is internally `Q ⋊ P` (Part VIII); the actions are nontrivial
    (above); we transport one group's action onto the other's factors with
    `SemidirectProduct.congr'` (using `Q₁ ≃* Q₂`, `P₁ ≃* P₂` from
    `mulEquivOfCyclicCardEq`), and finish with Part VII's capstone
    `semidirectProductIso_of_nontrivial_into_cyclic`, valid because `MulAut Q` is
    cyclic for prime-order `Q` (`IsCyclic.mulAutMulEquiv` lands in `(ZMod q)ˣ`, cyclic
    by `ZMod.isCyclic_units_prime`).

  Together with Part IV (every group of order `pq` is cyclic when `p ∤ q-1`) and
  Parts I–III (abelian groups of order `pq` are cyclic), this completes the
  isomorphism-uniqueness upgrade of the `pq`-classification: in the `p ∣ q-1` branch
  the non-cyclic class is a single isomorphism type.
-/

/-- **Trivial action ⟹ cyclic.** A semidirect product `N ⋊[1] Γ` with the trivial
    action map, over finite cyclic factors of coprime order, *is* the direct product
    `N × Γ` and hence cyclic. -/
theorem semidirectProduct_trivial_isCyclic {N Γ : Type*} [Group N] [Group Γ]
    [Finite N] [Finite Γ] [IsCyclic N] [IsCyclic Γ]
    (hcop : (Nat.card N).Coprime (Nat.card Γ)) :
    IsCyclic (SemidirectProduct N Γ (1 : Γ →* MulAut N)) := by
  rw [(SemidirectProduct.mulEquivProd (N := N) (G := Γ)).isCyclic]
  exact Group.isCyclic_prod_iff.mpr ⟨inferInstance, inferInstance, hcop⟩

/-- **Non-cyclic ⟹ nontrivial action.** Contrapositive of the previous lemma: a
    non-cyclic semidirect product over coprime cyclic factors has a nontrivial action. -/
theorem action_ne_one_of_not_isCyclic {N Γ : Type*} [Group N] [Group Γ]
    [Finite N] [Finite Γ] [IsCyclic N] [IsCyclic Γ]
    (hcop : (Nat.card N).Coprime (Nat.card Γ)) {φ : Γ →* MulAut N}
    (hnc : ¬ IsCyclic (SemidirectProduct N Γ φ)) : φ ≠ 1 := by
  rintro rfl
  exact hnc (semidirectProduct_trivial_isCyclic hcop)

/-- **Full non-abelian uniqueness for groups of order `pq`.** Any two *non-cyclic*
    groups `G`, `H` of order `pq` (`p < q` primes) are isomorphic. This closes the
    non-abelian thread of OQ-01-OQ-01-OQ-02: in the `p ∣ q-1` branch of the
    `pq`-classification the non-cyclic isomorphism class is unique. -/
theorem pq_noncyclic_iso {G H : Type*} [Group G] [Group H] [Fintype G] [Fintype H]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpltq : p < q)
    (hG : Fintype.card G = p * q) (hH : Fintype.card H = p * q)
    (hGnc : ¬ IsCyclic G) (hHnc : ¬ IsCyclic H) :
    Nonempty (G ≃* H) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hpq : p ≠ q := Nat.ne_of_lt hpltq
  -- Internal recognition (Part VIII): both groups are internal semidirect products.
  obtain ⟨QG, PG, _, φ, hcardQG, hcardPG, ⟨eG⟩⟩ :=
    exists_internalSemidirect_of_card_pq hp hq hpltq hG
  obtain ⟨QH, PH, _, ψ, hcardQH, hcardPH, ⟨eH⟩⟩ :=
    exists_internalSemidirect_of_card_pq hp hq hpltq hH
  -- All four prime-order factors are cyclic.
  haveI : IsCyclic QG := isCyclic_of_prime_card hcardQG
  haveI : IsCyclic PG := isCyclic_of_prime_card hcardPG
  haveI : IsCyclic QH := isCyclic_of_prime_card hcardQH
  haveI : IsCyclic PH := isCyclic_of_prime_card hcardPH
  -- The factor orders `q` and `p` are coprime.
  have hcopH : (Nat.card QH).Coprime (Nat.card PH) := by
    rw [hcardQH, hcardPH]; exact (Nat.coprime_primes hq hp).mpr (Ne.symm hpq)
  -- Isomorphisms between the like-order Sylow factors of `G` and `H`.
  let e_Q : QG ≃* QH := mulEquivOfCyclicCardEq (hcardQG.trans hcardQH.symm)
  let e_P : PG ≃* PH := mulEquivOfCyclicCardEq (hcardPG.trans hcardPH.symm)
  -- Transport `G`'s action onto `H`'s factors, obtaining `QG ⋊[φ] PG ≃* QH ⋊[φ'] PH`.
  let φ' : PH →* MulAut QH :=
    (MulAut.congr e_Q : MulAut QG →* MulAut QH).comp (φ.comp (e_P.symm : PH →* PG))
  have t : SemidirectProduct QG PG φ ≃* SemidirectProduct QH PH φ' :=
    SemidirectProduct.congr' e_Q e_P
  -- Both transported actions are nontrivial: their semidirect products are `≃* G`,`H`,
  -- which are non-cyclic.
  have hψ : ψ ≠ 1 :=
    action_ne_one_of_not_isCyclic hcopH (fun hc => hHnc ((eH.isCyclic).mp hc))
  have hφ' : φ' ≠ 1 :=
    action_ne_one_of_not_isCyclic hcopH
      (fun hc => hGnc (((t.symm.trans eG).isCyclic).mp hc))
  -- `MulAut QH` is cyclic (prime-order cyclic `QH`, so `MulAut QH ≃* (ZMod q)ˣ`).
  haveI : IsCyclic (MulAut QH) := by
    have e := IsCyclic.mulAutMulEquiv QH
    rw [e.isCyclic, hcardQH]
    exact ZMod.isCyclic_units_prime hq
  haveI : Fintype PH := Fintype.ofFinite _
  have hcardPH' : Fintype.card PH = p := by
    rw [← Nat.card_eq_fintype_card]; exact hcardPH
  -- Part VII capstone: nontrivial actions into a cyclic `Aut` give isomorphic products.
  obtain ⟨s⟩ := semidirectProductIso_of_nontrivial_into_cyclic
    (N := QH) (Γ := PH) hp hcardPH' hφ' hψ
  -- Stitch: `G ≃* QG⋊[φ]PG ≃* QH⋊[φ']PH ≃* QH⋊[ψ]PH ≃* H`.
  exact ⟨eG.symm.trans (t.trans (s.symm.trans eH))⟩

end LagrangeOQ01OQ01OQ02
