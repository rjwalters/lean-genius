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

/-!
## Part IV: Non-abelian uniqueness — the semidirect-product reparametrization engine

The non-abelian branch (`p ∣ q - 1`) of the classification has *two* isomorphism
classes of order `pq`: the cyclic group `ℤ/pq` (Parts I–III) and a non-abelian
semidirect product `ℤ/q ⋊_φ ℤ/p`. The **existence** of the non-abelian class is
constructed in the sibling file `LagrangeTheoremOQ01OQ01OQ01ApproachB`
(`approachBGroup`). The remaining content of this open question is the
**uniqueness** of that non-abelian class: any two nontrivial actions
`φ, ψ : ℤ/p →* MulAut (ℤ/q)` yield *isomorphic* semidirect products.

This part develops the structural engine for that uniqueness, in full generality
and with `0` sorries:

* `semidirectProduct_reparam_iso` — the reparametrization isomorphism: if two
  actions `φ, ψ : G →* MulAut N` differ by an automorphism `α` of the acting
  group (`φ = ψ ∘ α`), then `N ⋊[φ] G ≃* N ⋊[ψ] G`. This is the specialization
  of Mathlib's `SemidirectProduct.congr` to `fn = id_N`, `fg = α`.

* `exists_mulEquiv_comp_of_range_eq` — pure group theory: two *injective*
  homomorphisms `φ, ψ : G →* H` with the **same image** differ by a source
  automorphism `α : G ≃* G` (namely `α = ψ⁻¹ ∘ φ` on the common image). This is
  the algebraic heart of the uniqueness.

* `semidirectProduct_iso_of_range_eq` — combining the two: injective actions with
  equal image give isomorphic semidirect products.

Specializing to `N = ℤ/q`, `G = ℤ/p`, the uniqueness of the non-abelian class
reduces to the two nontrivial actions having the *same image* inside
`MulAut (ℤ/q)`. We prove the key enabling fact
`mulAut_multiplicative_zmod_isCyclic`: for `q` prime, `MulAut (ℤ/q)` is **cyclic**
(of order `q - 1`). In a finite cyclic group there is a *unique* subgroup of each
order, so the two order-`p` images automatically coincide — the final
`unique subgroup of order p in a cyclic group` step and the Sylow-theoretic
*recognition* that every non-abelian group of order `pq` actually *is* such a
semidirect product are the remaining open directions (the latter blocked on the
parent `Proofs.SylowTheoremOQ01`, which does not compile on Mathlib v4.26.0).
-/

/-- **Reparametrization engine.** If two actions `φ, ψ : G →* MulAut N` of a group
`G` on `N` differ by an automorphism `α` of `G` (i.e. `φ g = ψ (α g)` for all `g`),
then the semidirect products are isomorphic: `N ⋊[φ] G ≃* N ⋊[ψ] G`. Specialization
of `SemidirectProduct.congr` with the identity on `N` and `α` on `G`. -/
theorem semidirectProduct_reparam_iso {N G : Type*} [Group N] [Group G]
    {φ ψ : G →* MulAut N} (α : G ≃* G) (h : ∀ g, φ g = ψ (α g)) :
    Nonempty (N ⋊[φ] G ≃* N ⋊[ψ] G) :=
  ⟨SemidirectProduct.congr (MulEquiv.refl N) α fun g => MulEquiv.ext fun y => by
    simp only [MulEquiv.trans_apply, MulEquiv.refl_apply, h]⟩

/-- **Equal image ⇒ source automorphism.** Two injective homomorphisms
`φ, ψ : G →* H` with the same image differ by an automorphism of the source:
there is `α : G ≃* G` with `φ g = ψ (α g)` for all `g`. (Concretely `α` is
`ψ`-corestriction inverted and composed with `φ`-corestriction across the common
range.) -/
theorem exists_mulEquiv_comp_of_range_eq {G H : Type*} [Group G] [Group H]
    {φ ψ : G →* H} (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hr : φ.range = ψ.range) :
    ∃ α : G ≃* G, ∀ g, φ g = ψ (α g) := by
  refine ⟨(MonoidHom.ofInjective hφ).trans
            ((MulEquiv.subgroupCongr hr).trans (MonoidHom.ofInjective hψ).symm), fun x => ?_⟩
  simp only [MulEquiv.trans_apply, MonoidHom.apply_ofInjective_symm,
    MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]

/-- **Semidirect uniqueness from equal image.** If two actions
`φ, ψ : G →* MulAut N` are injective and have the same image, the semidirect
products `N ⋊[φ] G` and `N ⋊[ψ] G` are isomorphic. -/
theorem semidirectProduct_iso_of_range_eq {N G : Type*} [Group N] [Group G]
    {φ ψ : G →* MulAut N} (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hr : φ.range = ψ.range) :
    Nonempty (N ⋊[φ] G ≃* N ⋊[ψ] G) := by
  obtain ⟨α, hα⟩ := exists_mulEquiv_comp_of_range_eq hφ hψ hr
  exact semidirectProduct_reparam_iso α hα

/-!
### Part IV·b: the acting target `MulAut (ℤ/q)` is cyclic

For `q` prime, `MulAut (Multiplicative (ZMod q)) ≃* (ZMod q)ˣ` (automorphisms of a
cyclic group are units of `ZMod` of its order), and `(ZMod q)ˣ` is cyclic
(`isCyclic_units_prime`). Hence `MulAut (ℤ/q)` is cyclic of order `q - 1`. This is
the fact that forces the two order-`p` action images to coincide.
-/

/-- **`MulAut (ℤ/q)` is cyclic** for `q` prime. Via
`IsCyclic.mulAutMulEquiv : MulAut G ≃* (ZMod (Nat.card G))ˣ` with
`G = Multiplicative (ZMod q)` (so `Nat.card G = q`) and `isCyclic_units_prime`. -/
theorem mulAut_multiplicative_zmod_isCyclic {q : ℕ} (hq : q.Prime) :
    IsCyclic (MulAut (Multiplicative (ZMod q))) := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  haveI : IsCyclic (ZMod q)ˣ := ZMod.isCyclic_units_prime hq
  have hcard : Nat.card (Multiplicative (ZMod q)) = q := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod q) ≃ ZMod q),
      Nat.card_eq_fintype_card, ZMod.card]
  have e0 : MulAut (Multiplicative (ZMod q)) ≃*
      (ZMod (Nat.card (Multiplicative (ZMod q))))ˣ :=
    IsCyclic.mulAutMulEquiv (G := Multiplicative (ZMod q))
  rw [hcard] at e0
  exact (MulEquiv.isCyclic e0).mpr inferInstance

/-!
### Part IV·c: nontrivial actions are injective

The acting group `ℤ/p` has prime order, so any nonzero homomorphism out of it is
injective (its kernel, a subgroup of a group of prime order, is either trivial or
everything, and "everything" means the trivial homomorphism).
-/

/-- A nontrivial homomorphism out of `Multiplicative (ZMod p)` (`p` prime) is
injective: the kernel is `⊥` or `⊤`, and `⊤` would make the map trivial. -/
theorem injective_of_ne_one_zmod {p : ℕ} (hp : p.Prime) {H : Type*} [Group H]
    {φ : Multiplicative (ZMod p) →* H} (hφ : φ ≠ 1) : Function.Injective φ := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  have hcard : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod p) ≃ ZMod p),
      Nat.card_eq_fintype_card, ZMod.card]
  haveI : Fact (Nat.card (Multiplicative (ZMod p))).Prime := ⟨by rw [hcard]; exact hp⟩
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases φ.ker.eq_bot_or_eq_top_of_prime_card with h | h
  · exact h
  · exact absurd (MonoidHom.ext fun x => by
      have hx : x ∈ φ.ker := h ▸ Subgroup.mem_top x
      simpa [MonoidHom.mem_ker] using hx) hφ

/-- **Non-abelian uniqueness, conditional form.** For distinct primes `p, q` with
`p ∣ q - 1`, any two *nontrivial* actions `φ, ψ : ℤ/p →* MulAut (ℤ/q)` whose images
coincide give isomorphic non-abelian groups of order `pq`:
`ℤ/q ⋊[φ] ℤ/p ≃* ℤ/q ⋊[ψ] ℤ/p`. The image-coincidence hypothesis is automatic
because `MulAut (ℤ/q)` is cyclic (`mulAut_multiplicative_zmod_isCyclic`) and a
finite cyclic group has a unique subgroup of order `p`; discharging that final
step is the remaining open direction. -/
theorem pq_nonabelian_iso_of_range_eq {p q : ℕ} (hp : p.Prime)
    {φ ψ : Multiplicative (ZMod p) →* MulAut (Multiplicative (ZMod q))}
    (hφ : φ ≠ 1) (hψ : ψ ≠ 1) (hr : φ.range = ψ.range) :
    Nonempty
      ((Multiplicative (ZMod q) ⋊[φ] Multiplicative (ZMod p)) ≃*
       (Multiplicative (ZMod q) ⋊[ψ] Multiplicative (ZMod p))) :=
  semidirectProduct_iso_of_range_eq
    (injective_of_ne_one_zmod hp hφ) (injective_of_ne_one_zmod hp hψ) hr

end LagrangeOQ01OQ01OQ02
