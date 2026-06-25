import Mathlib

/-
# Groups of Order `p · q`: the Cyclic (Unique) Case

## Source
Open question from `sylow-theorems-oq-01-oq-02` (openQuestion[0], biprimal case):

> Count isomorphism classes of groups of squarefree order, starting with the
> biprimal case `n = p·q` (`p > q`): exactly 2 classes when `q ∣ p−1` (cyclic
> `ℤ/pq` and the nonabelian semidirect product), else 1 (cyclic only).

## What This Proves (0 sorries, 0 axioms)

This file settles the **`q ∤ (p−1)` direction**: a finite group of order `p·q`
with `p > q` both prime and `q ∤ (p−1)` is **cyclic**, and hence there is exactly
one isomorphism class in that case (every such group is `≅ ℤ/pq`).

Main results:
* `card_sylow_eq_one_of_card_pq` — for every prime `r`, the number of Sylow
  `r`-subgroups of `G` is `1` (so every Sylow subgroup is normal). The decisive
  arithmetic: `nᵣ ∣ p·q`, `r ∤ nᵣ`, and `nᵣ ≡ 1 [MOD r]`, combined with `q < p`
  and `q ∤ (p−1)`.
* `isCyclic_of_card_pq` — the headline: `G` is cyclic.
* `unique_isoclass_of_card_pq` — restatement: any two groups of order `p·q` with
  `q ∤ (p−1)` are isomorphic (both `≅ Multiplicative (ZMod (p·q))`).

## Method
We never construct the rational/semidirect structure by hand. Instead:
1. `Nat.card G = p·q` is squarefree, so `G` is a `Z`-group
   (`IsZGroup.of_squarefree`: all Sylow subgroups cyclic).
2. Sylow counting forces every Sylow subgroup to be normal; by the finite-group
   nilpotency TFAE (`Sylow.isNilpotent_of_finite_tfae`) `G` is nilpotent.
3. A finite nilpotent `Z`-group is cyclic (Mathlib instance
   `IsZGroup` + `Group.IsNilpotent` ⟹ `IsCyclic`).

## Honest scope
This is **one direction** of the count. The `q ∣ (p−1)` case (exactly two
classes: cyclic plus a unique nonabelian semidirect product) needs an
isomorphism-classification of semidirect products `ℤ/p ⋊ ℤ/q`, which is not yet
in Mathlib and remains open. See `meta.json` open questions.
-/

namespace SylowOrderPQ

open scoped Classical

variable {G : Type*} [Group G]

/-- **Sylow count is one for every prime.** If `Nat.card G = p · q` with `p > q`
    both prime and `q ∤ (p − 1)`, then for every prime `r` the number of Sylow
    `r`-subgroups equals `1`. -/
theorem card_sylow_eq_one_of_card_pq [Finite G] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hqp : q < p)
    (hcard : Nat.card G = p * q) (hndvd : ¬ q ∣ (p - 1))
    (r : ℕ) [hr : Fact r.Prime] :
    Nat.card (Sylow r G) = 1 := by
  have hp2 := hp.two_le
  have hq2 := hq.two_le
  -- General facts about `nᵣ = Nat.card (Sylow r G)`.
  set nr := Nat.card (Sylow r G) with hnr
  have hmod : nr ≡ 1 [MOD r] := card_sylow_modEq_one r G
  have hrnd : ¬ r ∣ nr := not_dvd_card_sylow r G
  -- Is `r` one of the two primes dividing `|G|`?
  by_cases hdvd : r ∣ Nat.card G
  · -- `r ∣ p·q` and `r` prime, so `r = p` or `r = q`.
    rw [hcard] at hdvd
    -- `nᵣ ∣ p·q`.
    obtain ⟨P⟩ : Nonempty (Sylow r G) := inferInstance
    have hnr_dvd : nr ∣ p * q := by
      have h1 : nr ∣ (P : Subgroup G).index := Sylow.card_dvd_index P
      have h2 : (P : Subgroup G).index ∣ Nat.card G := (P : Subgroup G).index_dvd_card
      simpa [hcard] using h1.trans h2
    rcases (hr.out.dvd_mul.mp hdvd) with hrp | hrq
    · -- r = p
      have hrep : r = p := (Nat.prime_dvd_prime_iff_eq hr.out hp).mp hrp
      subst hrep
      -- `r ∤ nᵣ` and `r` prime ⟹ `Coprime r nᵣ`; with `nᵣ ∣ r·q` get `nᵣ ∣ q`.
      have hcop : Nat.Coprime nr r := (Nat.coprime_comm.mp ((hr.out.coprime_iff_not_dvd).mpr hrnd))
      have hnq : nr ∣ q := hcop.dvd_of_dvd_mul_left hnr_dvd
      rcases (Nat.dvd_prime hq).mp hnq with h1 | hqeq
      · exact h1
      · -- `nᵣ = q` would give `q ≡ 1 [MOD r]`, i.e. `r ∣ q - 1`, impossible (`q < r`).
        exfalso
        have hmod' : q ≡ 1 [MOD r] := hqeq ▸ hmod
        have hdvd' : r ∣ q - 1 := (Nat.modEq_iff_dvd' (by omega)).mp hmod'.symm
        have hle : r ≤ q - 1 := Nat.le_of_dvd (by omega) hdvd'
        omega
    · -- r = q
      have hreq : r = q := (Nat.prime_dvd_prime_iff_eq hr.out hq).mp hrq
      subst hreq
      have hcop : Nat.Coprime nr r := (Nat.coprime_comm.mp ((hr.out.coprime_iff_not_dvd).mpr hrnd))
      -- `nᵣ ∣ p·q`, coprime to `r = q`, so `nᵣ ∣ p`.
      have hnp : nr ∣ p := hcop.dvd_of_dvd_mul_right hnr_dvd
      rcases (Nat.dvd_prime hp).mp hnp with h1 | hpeq
      · exact h1
      · -- `nᵣ = p` would give `p ≡ 1 [MOD r]`, i.e. `r ∣ p - 1`, contradicting `q ∤ p-1`.
        exfalso
        have hmod' : p ≡ 1 [MOD r] := hpeq ▸ hmod
        have hdvd' : r ∣ p - 1 := (Nat.modEq_iff_dvd' (by omega)).mp hmod'.symm
        exact hndvd hdvd'
  · -- `r ∤ |G|`: every Sylow `r`-subgroup is trivial, so there is exactly one.
    have htriv : ∀ S : Sylow r G, (S : Subgroup G) = ⊥ := by
      intro S
      rw [Subgroup.eq_bot_iff_card]
      obtain ⟨k, hk⟩ := S.isPGroup'.exists_card_eq
      have hcd : Nat.card (S : Subgroup G) ∣ Nat.card G := Subgroup.card_subgroup_dvd_card _
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk, hk0, pow_zero]
      · exact absurd ((dvd_pow_self r hkpos.ne').trans (hk ▸ hcd)) hdvd
    have hsub : Subsingleton (Sylow r G) := ⟨fun P Q => Sylow.ext ((htriv P).trans (htriv Q).symm)⟩
    exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, inferInstance⟩

/-- **Cyclic case of the order-`pq` classification.** A finite group of order
    `p · q` (`p > q` primes) with `q ∤ (p − 1)` is cyclic. -/
theorem isCyclic_of_card_pq [Finite G] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hqp : q < p)
    (hcard : Nat.card G = p * q) (hndvd : ¬ q ∣ (p - 1)) :
    IsCyclic G := by
  -- (1) `|G| = p·q` is squarefree ⟹ `G` is a Z-group.
  have hsf : Squarefree (Nat.card G) := by
    rw [hcard]
    have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr (by omega)
    exact (Nat.squarefree_mul hcop).mpr ⟨hp.squarefree, hq.squarefree⟩
  haveI : IsZGroup G := IsZGroup.of_squarefree hsf
  -- (2) Every Sylow subgroup is normal (count `= 1` ⟹ `Subsingleton`).
  have hnormal : ∀ (s : ℕ) (_ : Fact s.Prime) (P : Sylow s G), (↑P : Subgroup G).Normal := by
    intro s hs P
    haveI := hs
    haveI : Subsingleton (Sylow s G) :=
      Nat.card_eq_one_iff_unique.mp
        (card_sylow_eq_one_of_card_pq hp hq hqp hcard hndvd s) |>.1
    exact Sylow.normal_of_subsingleton P
  -- (3) All Sylow normal ⟹ nilpotent (finite-group TFAE).
  haveI : Group.IsNilpotent G := ((isNilpotent_of_finite_tfae (G := G)).out 3 0).mp hnormal
  -- (4) finite nilpotent Z-group ⟹ cyclic (Mathlib instance).
  infer_instance

/-- **Uniqueness of the isomorphism class.** Any two finite groups `G`, `H` of
    order `p · q` (`p > q` primes) with `q ∤ (p − 1)` are isomorphic — both are
    cyclic of order `p · q`. -/
theorem unique_isoclass_of_card_pq {H : Type*} [Group H] [Finite G] [Finite H]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q < p)
    (hndvd : ¬ q ∣ (p - 1))
    (hG : Nat.card G = p * q) (hH : Nat.card H = p * q) :
    Nonempty (G ≃* H) := by
  haveI : IsCyclic G := isCyclic_of_card_pq hp hq hqp hG hndvd
  haveI : IsCyclic H := isCyclic_of_card_pq hp hq hqp hH hndvd
  exact ⟨mulEquivOfCyclicCardEq (by rw [hG, hH])⟩

end SylowOrderPQ
