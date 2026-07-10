import Mathlib
import Proofs.AbelRuffiniOQ04OQ01OQ03

/-!
# Abel–Ruffini OQ04·OQ01·OQ03 — sharpness of the order-`pq` classification

`AbelRuffiniOQ04OQ01OQ03.lean` proves the **positive half** of the classical order-`pq`
classification and its *necessity* contrapositive:

* `isCyclic_of_card_eq_prime_mul_prime_of_not_dvd` — for primes `p < q` with `p ∤ q − 1`,
  every group of order `p·q` is cyclic;
* `dvd_sub_one_of_not_isCyclic_card_eq_prime_mul_prime` — conversely, if *some* group of
  order `p·q` fails to be cyclic then `p ∣ q − 1`.

The second statement is only meaningful once a non-cyclic group of order `p·q` is known to
*exist* in the regime `p ∣ q − 1`.  This file supplies that missing **existence witness**,
turning the necessity direction into a genuine sharp characterisation:

> a non-cyclic group of order `p·q` exists  **iff**  `p ∣ q − 1`.

## The construction

When `p ∣ q − 1`, the automorphism group of the cyclic group `N = ℤ/q` — which is cyclic of
order `q − 1` (`IsCyclic.card_mulAut`, `Nat.totient_prime`) — contains, by Cauchy's theorem
(`exists_prime_orderOf_dvd_card`), an automorphism `σ` of order `p`.  The semidirect product

  `N ⋊ ⟨σ⟩`   (with `⟨σ⟩ ≤ MulAut N` acting through the inclusion)

then has order `q · p` (`SemidirectProduct.card`) and is **nonabelian**: the generators
`inr σ` and `inl n` fail to commute for any `n` moved by `σ`, because a direct computation of
left components gives `(inr σ · inl n).left = σ n ≠ n = (inl n · inr σ).left`.  A nonabelian
group of squarefree order `pq` is automatically non-cyclic (cyclic ⟹ abelian).

This is the elementary content behind "the nonabelian group of order `21` exists" (`p = 3`,
`q = 7`, `3 ∣ 6`), the smallest case where the abelian/cyclic conclusion genuinely fails.

## Main results

* `semidirectProduct_subtype_zpowers_not_comm` — the abstract nonabelian witness: a
  prime-order automorphism yields a nonabelian semidirect product.
* `exists_nonabelian_of_dvd_card_mulAut` — existence of a nonabelian group of order
  `p · |N|` from `p ∣ |MulAut N|`, for any finite `N`.
* `exists_noncyclic_group_of_card_eq_prime_mul_prime_of_dvd_sub_one` — the witness: for
  `p ∣ q − 1`, a non-cyclic group of order `p·q` exists.
* `exists_noncyclic_card_eq_prime_mul_prime_iff_dvd_sub_one` — the sharp biconditional,
  combining this witness with the base file's necessity direction.
* `exists_noncyclic_group_of_card_twentyone` — the concrete order-`21` instance.

Everything is `0`-sorry / `0`-axiom and imports only Mathlib together with the base file.
-/

namespace AbelRuffiniSylowElim

open scoped Classical

/-- **Abstract nonabelian witness.**  If `σ` is an automorphism of prime order `p > 1` of a
group `N`, then the semidirect product of `N` by the cyclic subgroup `⟨σ⟩ ≤ MulAut N` acting
through the inclusion is nonabelian: taking `n` moved by `σ`, the generators `inr σ` and
`inl n` do not commute, since the left component of `inr σ · inl n` is `σ n` whereas that of
`inl n · inr σ` is `n`. -/
theorem semidirectProduct_subtype_zpowers_not_comm {N : Type*} [Group N] {p : ℕ}
    (hp : 1 < p) {σ : MulAut N} (hσ : orderOf σ = p) :
    ∃ a b : SemidirectProduct N (Subgroup.zpowers σ) (Subgroup.zpowers σ).subtype,
      a * b ≠ b * a := by
  -- `σ` is a nontrivial automorphism, so it moves some element.
  have hσ1 : σ ≠ 1 := by intro h; rw [h, orderOf_one] at hσ; omega
  have hmove : ∃ n : N, σ n ≠ n := by
    by_contra h
    push_neg at h
    exact hσ1 (MulEquiv.ext h)
  obtain ⟨n, hn⟩ := hmove
  set g : (Subgroup.zpowers σ) := ⟨σ, Subgroup.mem_zpowers σ⟩ with hg
  refine ⟨SemidirectProduct.inr g, SemidirectProduct.inl n, ?_⟩
  intro hcomm
  -- Left components of the two products.
  have h1 : (SemidirectProduct.inr g * SemidirectProduct.inl n).left = σ n := by
    rw [SemidirectProduct.mul_left, SemidirectProduct.left_inr,
        SemidirectProduct.right_inr, SemidirectProduct.left_inl, one_mul]
  have h2 : (SemidirectProduct.inl n * SemidirectProduct.inr g).left = n := by
    rw [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
        SemidirectProduct.right_inl, SemidirectProduct.left_inr, map_one]
    simp
  rw [hcomm, h2] at h1
  exact hn h1.symm

/-- **Existence of a nonabelian group of order `p · |N|`.**  For any finite group `N`, if the
prime `p` divides `|MulAut N|` then Cauchy supplies an automorphism `σ` of order `p`, and the
semidirect product `N ⋊ ⟨σ⟩` is a nonabelian group of order `p · |N|`. -/
theorem exists_nonabelian_of_dvd_card_mulAut {N : Type} [Group N] [Finite N] {p : ℕ}
    [hp : Fact p.Prime] (hdvd : p ∣ Nat.card (MulAut N)) :
    ∃ (M : Type) (_ : Group M) (_ : Finite M),
      Nat.card M = p * Nat.card N ∧ ∃ a b : M, a * b ≠ b * a := by
  haveI : Fintype (MulAut N) := Fintype.ofFinite _
  have hdvd' : p ∣ Fintype.card (MulAut N) := by rwa [Nat.card_eq_fintype_card] at hdvd
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card p hdvd'
  refine ⟨SemidirectProduct N (Subgroup.zpowers σ) (Subgroup.zpowers σ).subtype,
    inferInstance, Finite.of_equiv _ SemidirectProduct.equivProd.symm, ?_, ?_⟩
  · rw [SemidirectProduct.card, Nat.card_zpowers, hσ, mul_comm]
  · exact semidirectProduct_subtype_zpowers_not_comm hp.out.one_lt hσ

/-- **The sharpness witness.**  For a prime `q` and a prime `p` with `p ∣ q − 1`, there is a
non-cyclic group of order `p·q`.  Take `N = ℤ/q`, cyclic of order `q`, whose automorphism
group is cyclic of order `q − 1`; since `p ∣ q − 1` it contains an order-`p` automorphism, and
the resulting semidirect product `N ⋊ ⟨σ⟩` is nonabelian — hence non-cyclic — of order `p·q`.

This is the exact converse of the base file's necessity theorem
`dvd_sub_one_of_not_isCyclic_card_eq_prime_mul_prime`. -/
theorem exists_noncyclic_group_of_card_eq_prime_mul_prime_of_dvd_sub_one
    {p q : ℕ} [hp : Fact p.Prime] (hq : q.Prime) (hpq : p ∣ q - 1) :
    ∃ (M : Type) (_ : Group M) (_ : Finite M), Nat.card M = p * q ∧ ¬ IsCyclic M := by
  haveI : NeZero q := ⟨hq.pos.ne'⟩
  have hNq : Nat.card (Multiplicative (ZMod q)) = q := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hdvd : p ∣ Nat.card (MulAut (Multiplicative (ZMod q))) := by
    rw [IsCyclic.card_mulAut, hNq, Nat.totient_prime hq]; exact hpq
  obtain ⟨M, instG, instF, hcard, a, b, hab⟩ :=
    exists_nonabelian_of_dvd_card_mulAut (N := Multiplicative (ZMod q)) hdvd
  haveI := instG; haveI := instF
  refine ⟨M, instG, instF, ?_, ?_⟩
  · rw [hcard, hNq]
  · intro hcyc
    haveI := hcyc
    letI : CommGroup M := IsCyclic.commGroup
    exact hab (mul_comm a b)

/-- **Sharp classification of order-`pq` groups.**  For primes `p < q`, a non-cyclic group of
order `p·q` exists **iff** `p ∣ q − 1`.  Equivalently, *every* group of order `p·q` is cyclic
iff `p ∤ q − 1`.  The forward direction is the base file's necessity theorem
`dvd_sub_one_of_not_isCyclic_card_eq_prime_mul_prime`; the reverse is the semidirect-product
witness `exists_noncyclic_group_of_card_eq_prime_mul_prime_of_dvd_sub_one`.  Together they make
the elementary divisibility criterion `p ∣ q − 1` the *exact* boundary between the unique-cyclic
regime and the regime admitting a nonabelian (Frobenius-type) group. -/
theorem exists_noncyclic_card_eq_prime_mul_prime_iff_dvd_sub_one
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    (∃ (M : Type) (_ : Group M) (_ : Finite M), Nat.card M = p * q ∧ ¬ IsCyclic M)
      ↔ p ∣ (q - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  constructor
  · rintro ⟨M, instG, instF, hcard, hnc⟩
    haveI := instG; haveI := instF
    exact dvd_sub_one_of_not_isCyclic_card_eq_prime_mul_prime hp hq hpq hcard hnc
  · exact fun hdvd =>
      exists_noncyclic_group_of_card_eq_prime_mul_prime_of_dvd_sub_one hq hdvd

/-- **The nonabelian group of order `21` exists** (`21 = 3·7`, `3 ∣ 6`).  The smallest instance
of the sharpness witness: since `3 ∣ 7 − 1`, there is a non-cyclic group of order `21` — the
Frobenius group `ℤ/7 ⋊ ℤ/3`.  This is exactly the case ruling out "every order-`pq` group is
cyclic": contrast `isCyclic_of_card_thirtythree` (`33 = 3·11`, `3 ∤ 10`, forced cyclic). -/
theorem exists_noncyclic_group_of_card_twentyone :
    ∃ (M : Type) (_ : Group M) (_ : Finite M), Nat.card M = 21 ∧ ¬ IsCyclic M := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨M, instG, instF, hcard, hnc⟩ :=
    exists_noncyclic_group_of_card_eq_prime_mul_prime_of_dvd_sub_one
      (p := 3) (q := 7) (by norm_num) (by norm_num)
  exact ⟨M, instG, instF, hcard.trans (by norm_num), hnc⟩

end AbelRuffiniSylowElim
