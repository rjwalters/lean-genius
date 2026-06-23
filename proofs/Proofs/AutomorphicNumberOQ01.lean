import Mathlib

/-!
# Automorphic numbers and the four idempotents modulo `10 ^ k`

## What This Proves

A natural number `n` with `k` digits is **automorphic** when its square ends in the
same `k` digits, i.e. `n ^ 2 ≡ n (mod 10 ^ k)`.  Classical examples are
`5, 6, 25, 76, 376, 625, …`.  Reducing modulo `10 ^ k`, an automorphic residue is
exactly an **idempotent** of the ring `ZMod (10 ^ k)` (`e * e = e`).

The main theorem is that for every `k ≥ 1` the ring `ZMod (10 ^ k)` has **exactly
four idempotents**:

```
automorphic_idempotent_count :
  (Finset.univ.filter (fun e : ZMod (10 ^ k) => e * e = e)).card = 4
```

The four idempotents are `0`, `1`, and the two non-trivial automorphic residues
(the ones ending in `…5` / `…6`, `…25` / `…76`, etc.).

## Strategy

* **Prime-power local structure.** For a prime `p` and `k ≥ 1` the only idempotents
  of `ZMod (p ^ k)` are `0` and `1` (`idem_eq_zero_or_one`).  Writing
  `e = (n : ZMod (p ^ k))` with `n < p ^ k`, idempotency gives `p ^ k ∣ n * (n - 1)`,
  and as `gcd n (n-1) = 1` the prime power lands entirely on one factor, forcing
  `n = 0` or `n = 1`.
* **Counting.** Hence `ZMod (p ^ k)` has exactly two idempotents
  (`idem_card_prime_pow`).
* **Chinese Remainder.** Since `10 ^ k = 2 ^ k * 5 ^ k` with coprime factors,
  `ZMod (10 ^ k) ≃+* ZMod (2 ^ k) × ZMod (5 ^ k)`.  Idempotents transport across a
  ring isomorphism and split componentwise across a product, so the count is
  `2 * 2 = 4`.

## Status

Fully machine-checked: `0` sorries, `0` axioms.
-/

namespace AutomorphicNumberOQ01

open Finset

/-- The only idempotents of `ZMod (p ^ k)` (`p` prime, `k ≥ 1`) are `0` and `1`. -/
theorem idem_eq_zero_or_one {p : ℕ} [hp : Fact p.Prime] {k : ℕ} (hk : 0 < k)
    (e : ZMod (p ^ k)) (he : e * e = e) : e = 0 ∨ e = 1 := by
  haveI : NeZero (p ^ k) := ⟨pow_ne_zero k hp.out.pos.ne'⟩
  set n := e.val with hn
  have hlt : n < p ^ k := ZMod.val_lt e
  have hcast : (n : ZMod (p ^ k)) = e := by
    first
      | exact ZMod.natCast_rightInverse e
      | exact ZMod.natCast_zmod_val e
  have hle : n ≤ n * n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · first
        | exact le_mul_of_one_le_left (Nat.zero_le n) h
        | exact Nat.le_mul_of_pos_left n h
        | nlinarith [h]
  have hsq : ((n * n : ℕ) : ZMod (p ^ k)) = ((n : ℕ) : ZMod (p ^ k)) := by
    push_cast; rw [hcast, he]
  have hdvd0 : ((n * n - n : ℕ) : ZMod (p ^ k)) = 0 := by
    rw [Nat.cast_sub hle, hsq, sub_self]
  have hdvd : p ^ k ∣ n * n - n := (ZMod.natCast_eq_zero_iff _ _).mp hdvd0
  have hfac : ∀ a : ℕ, a * a - a = a * (a - 1) := by
    intro a
    cases a with
    | zero => rfl
    | succ m =>
      have h1 : (m + 1) * (m + 1) = (m + 1) * m + (m + 1) := by ring
      simp only [Nat.succ_sub_one]; rw [h1]; omega
  rw [hfac n] at hdvd
  by_cases hpn : p ∣ n
  · by_cases hn0 : n = 0
    · left; rw [← hcast, hn0]; simp
    · have hpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hpnm : ¬ p ∣ (n - 1) := by
        intro hd
        have h2 : p ∣ n - (n - 1) := Nat.dvd_sub hpn hd
        rw [Nat.sub_sub_self hpos] at h2
        have h3 := Nat.le_of_dvd Nat.one_pos h2
        have h4 := hp.out.two_le
        omega
      have hcop : Nat.Coprime (p ^ k) (n - 1) :=
        ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpnm).pow_left k
      have hdk : p ^ k ∣ n := hcop.dvd_of_dvd_mul_right hdvd
      exact absurd (Nat.eq_zero_of_dvd_of_lt hdk hlt) hn0
  · have hcop : Nat.Coprime (p ^ k) n :=
      ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hpn).pow_left k
    have hdvd1 : p ^ k ∣ (n - 1) := hcop.dvd_of_dvd_mul_left hdvd
    have hz : n - 1 = 0 :=
      Nat.eq_zero_of_dvd_of_lt hdvd1 (lt_of_le_of_lt (Nat.sub_le n 1) hlt)
    have hn1 : n = 1 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exact absurd (h ▸ dvd_zero p) hpn
      · omega
    right; rw [← hcast, hn1]; simp

/-- `ZMod (p ^ k)` (`p` prime, `k ≥ 1`) has exactly two idempotents, `0` and `1`. -/
theorem idem_card_prime_pow {p : ℕ} [hp : Fact p.Prime] {k : ℕ} (hk : 0 < k) :
    Fintype.card {e : ZMod (p ^ k) // e * e = e} = 2 := by
  haveI : Fact (1 < p ^ k) := ⟨by
    first
      | exact Nat.one_lt_pow hk.ne' hp.out.one_lt
      | exact lt_of_lt_of_le hp.out.one_lt (Nat.le_self_pow hk.ne' p)
      | (have h2 := Nat.le_self_pow hk.ne' p
         have h1 := hp.out.one_lt
         omega)⟩
  rw [Fintype.card_subtype (fun e : ZMod (p ^ k) => e * e = e)]
  have hset : (univ.filter (fun e : ZMod (p ^ k) => e * e = e)) = {0, 1} := by
    ext e
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    constructor
    · intro he; exact idem_eq_zero_or_one hk e he
    · rintro (rfl | rfl) <;> simp
  rw [hset]
  first
    | exact Finset.card_pair zero_ne_one
    | exact Finset.card_doubleton zero_ne_one

/-- Idempotents transport across a multiplicative isomorphism.  (Only the multiplicative
structure matters, so this is stated for a `MulEquiv`; ring isomorphisms coerce via
`RingEquiv.toMulEquiv`.) -/
def idemCongr {R S : Type*} [Mul R] [Mul S] (f : R ≃* S) :
    {e : R // e * e = e} ≃ {e : S // e * e = e} where
  toFun e := ⟨f e.1, by rw [← map_mul, e.2]⟩
  invFun e := ⟨f.symm e.1, by rw [← map_mul, e.2]⟩
  left_inv e := by simp
  right_inv e := by simp

/-- An idempotent of a product ring is a pair of idempotents. -/
def idemProd {R S : Type*} [Mul R] [Mul S] :
    {e : R × S // e * e = e} ≃ ({a : R // a * a = a} × {b : S // b * b = b}) where
  toFun e := (⟨e.1.1, (Prod.ext_iff.mp e.2).1⟩, ⟨e.1.2, (Prod.ext_iff.mp e.2).2⟩)
  invFun p := ⟨(p.1.1, p.2.1), by
    show (p.1.1 * p.1.1, p.2.1 * p.2.1) = (p.1.1, p.2.1)
    rw [p.1.2, p.2.2]⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Main theorem.** For every `k ≥ 1` the ring `ZMod (10 ^ k)` has exactly four
idempotents — equivalently, four `k`-digit automorphic residues modulo `10 ^ k`. -/
theorem automorphic_idempotent_count (k : ℕ) (hk : 0 < k) :
    (univ.filter (fun e : ZMod (10 ^ k) => e * e = e)).card = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : NeZero ((10 : ℕ) ^ k) := ⟨pow_ne_zero k (by norm_num)⟩
  haveI : NeZero ((2 : ℕ) ^ k * 5 ^ k) :=
    ⟨mul_ne_zero (pow_ne_zero k (by norm_num)) (pow_ne_zero k (by norm_num))⟩
  have hcop : Nat.Coprime (2 ^ k) (5 ^ k) := by
    rw [Nat.coprime_pow_left_iff hk, Nat.coprime_pow_right_iff hk]; decide
  have h10 : (10 : ℕ) ^ k = 2 ^ k * 5 ^ k := by
    rw [show (10 : ℕ) = 2 * 5 from rfl, mul_pow]
  -- Count idempotents over the coprime product modulus `2 ^ k * 5 ^ k`.
  have key : Fintype.card {e : ZMod (2 ^ k * 5 ^ k) // e * e = e} = 4 := by
    rw [Fintype.card_congr (idemCongr (ZMod.chineseRemainder hcop).toMulEquiv),
        Fintype.card_congr (idemProd (R := ZMod (2 ^ k)) (S := ZMod (5 ^ k))),
        Fintype.card_prod,
        idem_card_prime_pow (p := 2) hk,
        idem_card_prime_pow (p := 5) hk]
  -- Transport along the type equality `ZMod (10 ^ k) = ZMod (2 ^ k * 5 ^ k)`, avoiding a
  -- rewrite under the dependent `NeZero` instance.
  have hcast : {e : ZMod (10 ^ k) // e * e = e} ≃ {e : ZMod (2 ^ k * 5 ^ k) // e * e = e} :=
    Equiv.cast (congrArg (fun N => {e : ZMod N // e * e = e}) h10)
  rw [← Fintype.card_subtype (fun e : ZMod (10 ^ k) => e * e = e),
      Fintype.card_congr hcast, key]

/-! ## Concrete automorphic numbers

The two non-trivial idempotents modulo `10 ^ k` are the familiar automorphic
numbers; here are small decidable instances of `e * e = e`. -/

/-- `5` is automorphic mod `10`: `5 ^ 2 = 25` ends in `5`. -/
example : (5 : ZMod 10) * 5 = 5 := by decide

/-- `6` is automorphic mod `10`: `6 ^ 2 = 36` ends in `6`. -/
example : (6 : ZMod 10) * 6 = 6 := by decide

/-- `25` is automorphic mod `100`: `25 ^ 2 = 625` ends in `25`. -/
example : (25 : ZMod 100) * 25 = 25 := by decide

/-- `76` is automorphic mod `100`: `76 ^ 2 = 5776` ends in `76`. -/
example : (76 : ZMod 100) * 76 = 76 := by decide

end AutomorphicNumberOQ01
