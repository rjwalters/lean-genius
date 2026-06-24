/-
  pq-Groups: Abelian isomorphism uniqueness
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

  **Scope / what is deferred.** The *general* (not-necessarily-abelian)
  uniqueness statements — "for `p ∤ (q-1)`, any two groups of order `pq` are
  isomorphic" (cyclic case) and "any two non-cyclic groups of order `pq` are
  isomorphic" (the `p ∣ (q-1)` non-abelian case) — depend on the parent's Sylow
  classification `pq_unique_when_coprime` and on a full internal
  semidirect-product recognition `ℤ/q ⋊ ℤ/p`, respectively. They are left as the
  open directions (see this entry's open questions). NOTE: at the time of writing,
  the parent dependency `Proofs.SylowTheoremOQ01` does not compile on Mathlib
  v4.26.0 (renamed/removed lemmas such as `Nat.Prime.eq_of_dvd_of_prime`,
  `orderOf_eq_one_iff_eq_one`), which is an independent repair task; the present
  file deliberately avoids that dependency and imports only Mathlib so it is fully
  machine-checked with `0` sorries and `0` axioms.

  **Key Mathlib tools**:
  - `exists_prime_orderOf_dvd_card` (Cauchy) and
    `Commute.orderOf_mul_eq_mul_orderOf_of_coprime` — produce an element of order `pq`.
  - `isCyclic_of_orderOf_eq_card` — a generator of full order makes `G` cyclic.
  - `mulEquivOfCyclicCardEq` — two cyclic groups of equal `Nat.card` are isomorphic.
  - `zmodCyclicMulEquiv` — a cyclic group `≅ Multiplicative (ZMod (Nat.card G))`.

  References:
  - Dummit, D. & Foote, R. (2004). Abstract Algebra, §4.5, Theorem 14.
  - Conrad, K. "Groups of order pq." Expository notes.

  Tags: group-theory, lagrange, pq-groups, classification, isomorphism, MulEquiv,
        cyclic-groups, abelian-groups, ZMod, finite-groups
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

end LagrangeOQ01OQ01OQ02
