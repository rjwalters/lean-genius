import Mathlib
import Proofs.GaussWilsonNonCyclic

/-!
# Sylow-2 Boundary Shapes in (ZMod n)ˣ — the Cyclic Half (OQ-02, S3 ACT)

## Problem (gauss-wilson-non-cyclic-oq-02)

Does the 2-torsion bound of the parent entry extend to characterize when
the Sylow 2-subgroup of `(ZMod n)ˣ` is *elementary abelian* versus
*cyclic*?

## This file (S3 scope)

The **cyclic half**, fully proved: the Sylow 2-subgroup of the finite
abelian group `(ZMod n)ˣ` is cyclic iff its 2-torsion has rank ≤ 1, i.e.
iff every square root of 1 is `±1` — and, remarkably, this Sylow-local
condition already detects the **global** cyclic classification:

* `two_torsion_pm_one_iff_isCyclic` :
  `(∀ x : (ZMod n)ˣ, x² = 1 → x = 1 ∨ x = -1) ↔ IsCyclic (ZMod n)ˣ`
  (`n ≥ 3`). Forward = contrapositive of the parent's
  `exists_third_sqrt_of_not_cyclic`; reverse = a cyclic group has at
  most two square roots of 1 (`IsCyclic.card_pow_eq_one_le`) while
  `{1, -1, x}` would be three.

Two kernel-`decide` anchors pin the **exponent** phenomenon that the
elementary-abelian half (S4 target) is about — rank does not see it:

* `zmod8_units_sq_eq_one` : `(ZMod 8)ˣ` has exponent 2 (elementary
  abelian, `S₂ ≅ C₂ × C₂`).
* `zmod16_units_exists_order_four` : `(ZMod 16)ˣ` has an element of
  order 4 (`S₂ ≅ C₂ × C₄` — same 2-rank as `n = 8`, different exponent).

## S4 (the elementary-abelian half; Sylow-free formulation) — PROVED

`units_pow_four_imp_sq_iff` (for `n ≠ 0`):

`(∀ x : (ZMod n)ˣ, x⁴ = 1 → x² = 1) ↔`
`(∀ p, p.Prime → Odd p → p ∣ n → p % 4 = 3) ∧ n.factorization 2 ≤ 3`.

("No element of order 4" is exactly "the Sylow 2-subgroup is elementary
abelian" for a finite abelian group.) Route: multiplicative induction
(`Nat.recOnPosPrimePosCoprime`) with CRT unit-group splitting
(`ZMod.chineseRemainder` + `Units.mapEquiv` + `MulEquiv.prodUnits`);
odd prime powers via cyclicity (`ZMod.isCyclic_units_of_prime_pow`) and
`v₂(p−1) = 1 ⟺ p ≡ 3 (mod 4)`; the 2-adic cap `a ≤ 3` via
`ZMod.orderOf_five` (`5` has order `2^(a−2)` in `(ZMod 2^a)ˣ`) — the
structure lemma the S3 hand-off predicted would be a Mathlib gap landed
in `Mathlib.RingTheory.ZMod.UnitsCyclic`, so no gap remained. The
order-4 witness is produced by the reusable helper
`exists_pow_four_ne_sq` (`orderOf g = 4m` ⟹ `g^m` violates the
collapse), which avoids `orderOf_pow`/gcd bookkeeping entirely.

Sorries: 0. Axioms: 0 (kernel `decide` only — no `native_decide`).
-/

namespace GaussWilsonNonCyclicOQ02

open GaussWilsonNonCyclic

/-- For `n ≥ 3`, `-1 ≠ 1` in `(ZMod n)ˣ`: otherwise `2 = 0` in
`ZMod n`, forcing `n ∣ 2`. (The parent proves this privately; re-derived
here via `CharP.cast_eq_zero_iff`.) -/
theorem neg_one_ne_one_units {n : ℕ} (hn : 3 ≤ n) [NeZero n] :
    (-1 : (ZMod n)ˣ) ≠ 1 := by
  intro h
  have hv : (-1 : ZMod n) = 1 := by
    have hval := congrArg (Units.val : (ZMod n)ˣ → ZMod n) h
    simpa using hval
  have h2 : ((2 : ℕ) : ZMod n) = 0 := by
    push_cast
    linear_combination -hv
  have hdvd : n ∣ 2 := (CharP.cast_eq_zero_iff (ZMod n) n 2).mp h2
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- **The cyclic half of OQ-02.** The Sylow 2-subgroup of `(ZMod n)ˣ`
is cyclic — equivalently, rank₂ ≤ 1, equivalently every square root of
unity is `±1` — if and only if `(ZMod n)ˣ` is itself cyclic. The
Sylow-local shape detects the global classification: rank₂ ≤ 1 already
forces `n ∈ {1, 2, 4, p^k, 2p^k}`.

Forward: contrapositive of the parent's
`exists_third_sqrt_of_not_cyclic` (a non-cyclic unit group carries a
third square root of 1). Reverse: in a cyclic group `y² = 1` has at
most two solutions, but `1`, `-1`, and a putative third root `x` are
pairwise distinct. -/
theorem two_torsion_pm_one_iff_isCyclic {n : ℕ} (hn : 3 ≤ n) [NeZero n] :
    (∀ x : (ZMod n)ˣ, x ^ 2 = 1 → x = 1 ∨ x = -1) ↔ IsCyclic (ZMod n)ˣ := by
  constructor
  · intro h
    by_contra hncyc
    obtain ⟨x, hx_sq, hx1, hxn1⟩ := exists_third_sqrt_of_not_cyclic hn hncyc
    rcases h (unitOfSqEqOne x hx_sq) (unitOfSqEqOne_sq x hx_sq) with h1 | h1
    · exact unitOfSqEqOne_ne_one hx_sq hx1 h1
    · exact unitOfSqEqOne_ne_neg_one hx_sq hxn1 h1
  · intro hcyc x hx_sq
    by_contra hne
    push_neg at hne
    obtain ⟨hne1, hnen1⟩ := hne
    have hcard2 : (Finset.univ.filter fun y : (ZMod n)ˣ => y ^ 2 = 1).card ≤ 2 :=
      hcyc.card_pow_eq_one_le (by norm_num)
    have hne_1_n1 : (-1 : (ZMod n)ˣ) ≠ 1 := neg_one_ne_one_units hn
    have hsub : ({1, -1, x} : Finset (ZMod n)ˣ) ⊆
        Finset.univ.filter fun y : (ZMod n)ˣ => y ^ 2 = 1 := by
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hy with rfl | rfl | rfl
      · simp
      · simp
      · exact hx_sq
    have hcard3 : ({1, -1, x} : Finset (ZMod n)ˣ).card = 3 := by
      rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          rintro (h | h)
          · exact hne_1_n1 h.symm
          · exact hne1 h.symm),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_singleton]
          intro h
          exact hnen1 h.symm),
        Finset.card_singleton]
    have := Finset.card_le_card hsub
    omega

/-- `(ZMod 8)ˣ` is elementary abelian: every unit squares to 1
(`S₂(8) ≅ C₂ × C₂`, rank 2, exponent 2). Kernel `decide`. -/
theorem zmod8_units_sq_eq_one : ∀ x : (ZMod 8)ˣ, x ^ 2 = 1 := by decide

/-- `(ZMod 16)ˣ` is NOT elementary abelian: it carries an element of
order 4 (`S₂(16) ≅ C₂ × C₄` — same 2-rank as `n = 8`, larger exponent;
this is exactly the invariant OQ-02 adds beyond OQ-03's square-root
count, which is `2^rank = 4` for both). Kernel `decide`. -/
theorem zmod16_units_exists_order_four :
    ∃ x : (ZMod 16)ˣ, x ^ 4 = 1 ∧ x ^ 2 ≠ 1 := by decide

/-! ## S4: the elementary-abelian half

The Sylow-free criterion for "no element of order 4 in `(ZMod n)ˣ`",
i.e. the Sylow 2-subgroup of `(ZMod n)ˣ` is elementary abelian. -/

/-- **Order-4 witness factory.** In any group, if `orderOf g = 4 * m` with
`m ≠ 0`, then `g ^ m` is a fourth root of unity that is not a square root of
unity — the exact violation of the exponent-collapse `x⁴ = 1 → x² = 1`. -/
theorem exists_pow_four_ne_sq {G : Type*} [Group G] {g : G} {m : ℕ} (hm : m ≠ 0)
    (horder : orderOf g = 4 * m) : (g ^ m) ^ 4 = 1 ∧ (g ^ m) ^ 2 ≠ 1 := by
  constructor
  · rw [← pow_mul]
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [horder]
    exact ⟨1, by ring⟩
  · intro h
    rw [← pow_mul] at h
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [horder] at hdvd
    have hle := Nat.le_of_dvd (by omega) hdvd
    omega

/-- The exponent-collapse property transfers along group isomorphisms. -/
theorem pow_four_imp_sq_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hG : ∀ x : G, x ^ 4 = 1 → x ^ 2 = 1) : ∀ y : H, y ^ 4 = 1 → y ^ 2 = 1 := by
  intro y hy
  have h4 : (e.symm y) ^ 4 = 1 := by
    rw [← map_pow, hy, map_one]
  have h2 := hG _ h4
  have h2' := congrArg e h2
  rwa [map_pow, map_one, e.apply_symm_apply] at h2'

/-- The exponent-collapse property on a product is the conjunction of the
componentwise properties. -/
theorem pow_four_imp_sq_prod_iff {G H : Type*} [Group G] [Group H] :
    (∀ x : G × H, x ^ 4 = 1 → x ^ 2 = 1) ↔
      ((∀ x : G, x ^ 4 = 1 → x ^ 2 = 1) ∧ ∀ y : H, y ^ 4 = 1 → y ^ 2 = 1) := by
  constructor
  · intro h
    constructor
    · intro x hx
      have h1 : ((x, (1 : H)) : G × H) ^ 4 = 1 := by
        rw [Prod.ext_iff]
        simpa using hx
      have h2 := h _ h1
      rw [Prod.ext_iff] at h2
      simpa using h2.1
    · intro y hy
      have h1 : (((1 : G), y) : G × H) ^ 4 = 1 := by
        rw [Prod.ext_iff]
        simpa using hy
      have h2 := h _ h1
      rw [Prod.ext_iff] at h2
      simpa using h2.2
  · rintro ⟨hG, hH⟩ x hx
    rw [Prod.ext_iff] at hx ⊢
    simp only [Prod.pow_fst, Prod.pow_snd, Prod.fst_one, Prod.snd_one] at hx ⊢
    exact ⟨hG _ hx.1, hH _ hx.2⟩

/-- **Odd prime powers**: `(ZMod p^a)ˣ` (cyclic of order `p^(a−1)(p−1)`)
has no element of order 4 iff `p ≡ 3 (mod 4)` — i.e. iff `v₂(p−1) = 1`. -/
theorem pow_four_imp_sq_units_odd_prime_pow_iff {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    {a : ℕ} (ha : 0 < a) :
    (∀ x : (ZMod (p ^ a))ˣ, x ^ 4 = 1 → x ^ 2 = 1) ↔ p % 4 = 3 := by
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero a hp.pos.ne'⟩
  have hp2 : p ≠ 2 := by
    rintro rfl
    have := Nat.odd_iff.mp hodd
    omega
  have hpm : p % 2 = 1 := Nat.odd_iff.mp hodd
  have hp2le := hp.two_le
  have hcard : Nat.card (ZMod (p ^ a))ˣ = p ^ (a - 1) * (p - 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime_pow hp ha]
  constructor
  · -- collapse ⟹ p % 4 = 3 (contrapositive: p ≡ 1 mod 4 gives an order-4 unit)
    intro hNFT
    by_contra hmod
    have h4 : 4 ∣ p - 1 := by omega
    haveI hcyc : IsCyclic (ZMod (p ^ a))ˣ := ZMod.isCyclic_units_of_prime_pow p hp hp2 a
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod (p ^ a))ˣ)
    obtain ⟨m, hm⟩ := h4
    have horder : orderOf g = 4 * (p ^ (a - 1) * m) := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard, hm]
      ring
    have hm0 : p ^ (a - 1) * m ≠ 0 := by
      have hm' : m ≠ 0 := by omega
      exact Nat.mul_ne_zero (pow_ne_zero _ hp.pos.ne') hm'
    obtain ⟨h41, h2ne⟩ := exists_pow_four_ne_sq hm0 horder
    exact h2ne (hNFT _ h41)
  · -- p % 4 = 3 ⟹ collapse: orderOf x ∣ gcd(4, card) ∣ 2
    intro hmod x hx4
    have hord : orderOf x ∣ 4 := orderOf_dvd_of_pow_eq_one hx4
    have hcarddvd : orderOf x ∣ p ^ (a - 1) * (p - 1) := hcard ▸ orderOf_dvd_natCard x
    have h4card : ¬ (4 ∣ p ^ (a - 1) * (p - 1)) := by
      intro hdvd
      have h2p : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr
        fun h => hp2 h.symm
      have hcop : Nat.Coprime 4 (p ^ (a - 1)) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
        exact Nat.Coprime.pow 2 (a - 1) h2p
      have h4p1 : 4 ∣ p - 1 := hcop.dvd_of_dvd_mul_left hdvd
      omega
    apply orderOf_dvd_iff_pow_eq_one.mp
    have hord' : orderOf x ∣ 2 ^ 2 := by
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num]
      exact hord
    obtain ⟨i, hi, hoi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord'
    interval_cases i
    · rw [hoi]; norm_num
    · rw [hoi]; norm_num
    · exfalso
      rw [hoi] at hcarddvd
      norm_num at hcarddvd
      exact h4card hcarddvd

/-- **Powers of two**: `(ZMod 2^a)ˣ` has no element of order 4 iff `a ≤ 3`.
For `a ≥ 4` the unit `5` has order `2^(a−2) ≥ 4` (`ZMod.orderOf_five`); for
`a ≤ 3` the group has exponent ≤ 2 (kernel `decide`). -/
theorem pow_four_imp_sq_units_two_pow_iff {a : ℕ} (ha : 0 < a) :
    (∀ x : (ZMod (2 ^ a))ˣ, x ^ 4 = 1 → x ^ 2 = 1) ↔ a ≤ 3 := by
  constructor
  · intro hNFT
    by_contra hgt
    push Not at hgt
    obtain ⟨e, rfl⟩ : ∃ e, a = e + 2 + 2 := ⟨a - 4, by omega⟩
    have hcop : Nat.Coprime 5 (2 ^ (e + 2 + 2)) :=
      Nat.Coprime.pow_right _ (by norm_num)
    set u : (ZMod (2 ^ (e + 2 + 2)))ˣ := ZMod.unitOfCoprime 5 hcop with hu
    have hcoe : ((u : ZMod (2 ^ (e + 2 + 2)))) = 5 := by
      rw [hu, ZMod.coe_unitOfCoprime]
      simp
    have h5 : orderOf u = 2 ^ (e + 2) := by
      have h := ZMod.orderOf_five (e + 2)
      rw [← hcoe, orderOf_units] at h
      exact h
    have horder : orderOf u = 4 * 2 ^ e := by
      rw [h5, pow_add]
      ring
    obtain ⟨h41, h2ne⟩ := exists_pow_four_ne_sq (pow_ne_zero e two_ne_zero) horder
    exact h2ne (hNFT _ h41)
  · intro hle
    interval_cases a
    · decide
    · decide
    · decide

/-- **S4 (elementary-abelian half, Sylow-free form).** For `n ≠ 0`, every
fourth root of unity in `(ZMod n)ˣ` is already a square root of unity —
equivalently, the Sylow 2-subgroup of `(ZMod n)ˣ` is elementary abelian —
iff every odd prime factor of `n` is `≡ 3 (mod 4)` and `2^4 ∤ n`. -/
theorem units_pow_four_imp_sq_iff {n : ℕ} (hn : n ≠ 0) :
    (∀ x : (ZMod n)ˣ, x ^ 4 = 1 → x ^ 2 = 1) ↔
      ((∀ p : ℕ, p.Prime → Odd p → p ∣ n → p % 4 = 3) ∧ n.factorization 2 ≤ 3) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    have hp' : p.Prime := hp
    rcases eq_or_ne p 2 with rfl | hp2
    · -- 2-power block
      rw [pow_four_imp_sq_units_two_pow_iff hk]
      constructor
      · intro hle
        refine ⟨fun q hq hqodd hqdvd => ?_, ?_⟩
        · have hq2 : q = 2 :=
            (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hqdvd)
          rw [hq2] at hqodd
          have := Nat.odd_iff.mp hqodd
          omega
        · rw [Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
          exact hle
      · rintro ⟨-, h2⟩
        rwa [Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same] at h2
    · -- odd prime-power block
      have hodd : Odd p := hp'.odd_of_ne_two hp2
      rw [pow_four_imp_sq_units_odd_prime_pow_iff hp' hodd hk]
      constructor
      · intro h3
        refine ⟨fun q hq hqodd hqdvd => ?_, ?_⟩
        · have hqp : q = p :=
            (Nat.prime_dvd_prime_iff_eq hq hp').mp (hq.dvd_of_dvd_pow hqdvd)
          rwa [hqp]
        · rw [Nat.Prime.factorization_pow hp', Finsupp.single_apply]
          simp [hp2]
      · rintro ⟨hq, -⟩
        exact hq p hp' hodd (dvd_pow_self p (by omega))
  | zero => exact absurd rfl hn
  | one =>
    constructor
    · intro _
      refine ⟨fun q hq _ hqdvd => ?_, by simp⟩
      have := Nat.le_of_dvd one_pos hqdvd
      have := hq.two_le
      omega
    · intro _
      decide
  | coprime a b ha hb hab iha ihb =>
    have ha0 : a ≠ 0 := by omega
    have hb0 : b ≠ 0 := by omega
    have e : (ZMod (a * b))ˣ ≃* (ZMod a)ˣ × (ZMod b)ˣ :=
      (Units.mapEquiv (ZMod.chineseRemainder hab).toMulEquiv).trans MulEquiv.prodUnits
    have hsplit : (∀ x : (ZMod (a * b))ˣ, x ^ 4 = 1 → x ^ 2 = 1) ↔
        ((∀ x : (ZMod a)ˣ, x ^ 4 = 1 → x ^ 2 = 1) ∧
          ∀ x : (ZMod b)ˣ, x ^ 4 = 1 → x ^ 2 = 1) := by
      rw [← pow_four_imp_sq_prod_iff]
      exact ⟨pow_four_imp_sq_of_mulEquiv e, pow_four_imp_sq_of_mulEquiv e.symm⟩
    rw [hsplit, iha ha0, ihb hb0]
    constructor
    · rintro ⟨⟨hqa, h2a⟩, hqb, h2b⟩
      refine ⟨fun q hq hqodd hqdvd => ?_, ?_⟩
      · rcases (Nat.Prime.dvd_mul hq).mp hqdvd with h | h
        · exact hqa q hq hqodd h
        · exact hqb q hq hqodd h
      · rw [Nat.factorization_mul ha0 hb0, Finsupp.add_apply]
        by_cases h2 : 2 ∣ a
        · have hb2 : ¬ 2 ∣ b := by
            intro hb2
            have h21 : (2 : ℕ) ∣ 1 := by
              have hg := Nat.dvd_gcd h2 hb2
              rwa [Nat.Coprime.gcd_eq_one hab] at hg
            omega
          rw [Nat.factorization_eq_zero_of_not_dvd hb2]
          omega
        · rw [Nat.factorization_eq_zero_of_not_dvd h2]
          omega
    · rintro ⟨hq, h2⟩
      have hf : a.factorization 2 ≤ 3 ∧ b.factorization 2 ≤ 3 := by
        rw [Nat.factorization_mul ha0 hb0, Finsupp.add_apply] at h2
        omega
      exact ⟨⟨fun q hq' hodd hdvd => hq q hq' hodd (hdvd.mul_right b), hf.1⟩,
        fun q hq' hodd hdvd => hq q hq' hodd (hdvd.mul_left a), hf.2⟩

/-- Sanity anchors: `n = 24 = 2³·3` satisfies both conditions (3 ≡ 3 mod 4,
`v₂ = 3`), `n = 16` fails the 2-adic cap, `n = 5` fails the odd condition. -/
example : ∀ x : (ZMod 24)ˣ, x ^ 4 = 1 → x ^ 2 = 1 := by decide
example : ∃ x : (ZMod 5)ˣ, x ^ 4 = 1 ∧ x ^ 2 ≠ 1 := by decide

#check @exists_pow_four_ne_sq
#check @pow_four_imp_sq_units_odd_prime_pow_iff
#check @pow_four_imp_sq_units_two_pow_iff
#check @units_pow_four_imp_sq_iff

end GaussWilsonNonCyclicOQ02
