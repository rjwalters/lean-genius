import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic

/-
# Uniqueness of the Two-Squares Representation of a Prime (OQ-02)

## What This Proves

Sibling `InfinitudePrimes4k1OQ01` proved Fermat's theorem on sums of two squares:
an odd prime `p` is a sum of two squares iff `p ≡ 1 (mod 4)`. That settles
*existence*. This file settles *uniqueness*: the representation is essentially
unique.

Concretely, if a prime `p` is written as a sum of two squares in two ways,

    p = a² + b² = c² + d²       (a b c d : ℕ)

then `{a, b} = {c, d}` as unordered pairs:

    (a = c ∧ b = d) ∨ (a = d ∧ b = c).

Combined with OQ-01 this gives the complete picture: every prime `p ≡ 1 (mod 4)`
is a sum of two squares in *exactly one way* (up to order), every prime
`p ≡ 3 (mod 4)` in no way, and `2 = 1² + 1²` uniquely.

Mathlib provides the *existence* half (`Nat.Prime.sq_add_sq`) and the Gaussian
integer machinery, but does **not** package the uniqueness statement at the level
of `ℕ` representations. This file builds it from scratch by elementary means.

## The Proof Idea (Euler's argument, no Gaussian integers)

Two Brahmagupta–Fibonacci identities express `p² = (a²+b²)(c²+d²)` as a sum of
two squares in two ways:

    (ac + bd)² + (ad − bc)² = (a²+b²)(c²+d²)
    (ac − bd)² + (ad + bc)² = (a²+b²)(c²+d²)

The crux is that `p ∣ (ad − bc)(ad + bc)`, because

    (ad)² − (bc)² = d²(a²+b²) − b²(c²+d²) = p·(d² − b²).

Euclid's lemma forces `p ∣ (ad − bc)` or `p ∣ (ad + bc)`. Each of `ad − bc` and
`ad + bc` has absolute value `≤ p` (its square is `≤ p²`), so the divisible one is
forced to be `0` or `±p`. The `±p` branch makes the *other* square vanish, which
is impossible because all of `a, b, c, d` are positive (a prime is never a perfect
square). Hence one of `ad − bc`, `ad + bc` is `0`, and a short "equal norm +
cross-product" cancellation upgrades that to equality of the pairs.

## Status
- [x] Complete proof, 0 sorries, 0 axioms.
- [x] Fully elementary: only `ring`, `nlinarith`, `omega`, Euclid's lemma, casts.

## Mathlib Dependencies
- `Nat.Prime`, `Nat.Prime.eq_one_or_self_of_dvd`, `dvd_pow_self`.
- `Nat.prime_iff_prime_int` and `Prime.dvd_mul` for Euclid over `ℤ`.
- Basic `Int`/`Nat` casting lemmas, `le_of_mul_le_mul_left`.
-/

namespace InfinitudePrimes4k1OQ02

open Nat

/-! ## Step 0: squaring is injective on `ℕ`. -/

private theorem nat_sq_inj {a x : ℕ} (h : a ^ 2 = x ^ 2) : a = x := by
  rcases lt_trichotomy a x with hlt | heq | hgt
  · exfalso
    have : a ^ 2 < x ^ 2 := by nlinarith [hlt, Nat.zero_le a]
    omega
  · exact heq
  · exfalso
    have : x ^ 2 < a ^ 2 := by nlinarith [hgt, Nat.zero_le x]
    omega

/-! ## Step 1: a prime is never a perfect square, so both legs are positive. -/

/-- If a prime `p` equals `a² + b²`, then both `a` and `b` are positive.
    (Otherwise `p` would be a perfect square, impossible for a prime.) -/
theorem pos_of_prime_eq_sq_add_sq {p a b : ℕ} (hp : Nat.Prime p)
    (h : p = a ^ 2 + b ^ 2) : 0 < a ∧ 0 < b := by
  -- A prime can't be a perfect square.
  have not_sq : ∀ n : ℕ, p ≠ n ^ 2 := by
    intro n hn
    have hdvd : n ∣ p := by rw [hn]; exact dvd_pow_self n (by norm_num)
    rcases hp.eq_one_or_self_of_dvd n hdvd with h1 | hpe
    · rw [h1] at hn; norm_num at hn; exact hp.ne_one hn
    · rw [hpe] at hn; nlinarith [hp.two_le, hn]
  refine ⟨?_, ?_⟩
  · rcases Nat.eq_zero_or_pos a with ha | ha
    · exact absurd (show p = b ^ 2 by rw [h, ha]; ring) (not_sq b)
    · exact ha
  · rcases Nat.eq_zero_or_pos b with hb | hb
    · exact absurd (show p = a ^ 2 by rw [h, hb]; ring) (not_sq a)
    · exact hb

/-! ## Step 2: the proportionality cancellation.

If two pairs have the same norm and equal cross product `a·y = b·x`, they are
equal. Proof: `a²(x²+y²) = a²x² + (a·y)² = a²x² + (b·x)² = x²(a²+b²)`, and the two
norms agree, so `a² = x²`, hence `a = x` and then `b = y`. -/

/-- Equal norm together with `a·y = b·x` forces `(a, b) = (x, y)` (over `ℕ`). -/
theorem pair_eq_of_cross {a b x y : ℕ} (hcross : a * y = b * x)
    (hnorm : a ^ 2 + b ^ 2 = x ^ 2 + y ^ 2) (hpos : 0 < a ^ 2 + b ^ 2) :
    a = x ∧ b = y := by
  have key : a ^ 2 * (a ^ 2 + b ^ 2) = x ^ 2 * (a ^ 2 + b ^ 2) :=
    calc a ^ 2 * (a ^ 2 + b ^ 2) = a ^ 2 * (x ^ 2 + y ^ 2) := by rw [hnorm]
      _ = a ^ 2 * x ^ 2 + (a * y) ^ 2 := by ring
      _ = a ^ 2 * x ^ 2 + (b * x) ^ 2 := by rw [hcross]
      _ = x ^ 2 * (a ^ 2 + b ^ 2) := by ring
  have hsq : a ^ 2 = x ^ 2 := Nat.eq_of_mul_eq_mul_right hpos key
  have hbsq : b ^ 2 = y ^ 2 := by omega
  exact ⟨nat_sq_inj hsq, nat_sq_inj hbsq⟩

/-! ## Step 3: the Brahmagupta–Fibonacci identities (over `ℤ`). -/

theorem brahmagupta_diff (a b c d : ℤ) :
    (a * c + b * d) ^ 2 + (a * d - b * c) ^ 2 = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  ring

theorem brahmagupta_sum (a b c d : ℤ) :
    (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  ring

/-! ## Step 4: the divisibility identity `(ad)² − (bc)² = p·(d² − b²)`. -/

theorem cross_factor_dvd {p : ℤ} {a b c d : ℤ} (hab : p = a ^ 2 + b ^ 2)
    (hcd : p = c ^ 2 + d ^ 2) :
    (a * d - b * c) * (a * d + b * c) = p * (d ^ 2 - b ^ 2) := by
  have : (a * d - b * c) * (a * d + b * c)
       = d ^ 2 * (a ^ 2 + b ^ 2) - b ^ 2 * (c ^ 2 + d ^ 2) := by ring
  rw [this, ← hab, ← hcd]; ring

/-! ## Step 5: the main uniqueness theorem. -/

set_option maxHeartbeats 400000 in
/-- **Uniqueness of the two-squares representation of a prime.**

If a prime `p` is written as a sum of two squares in two ways,
`p = a² + b² = c² + d²`, then the two representations agree up to order:
`(a = c ∧ b = d) ∨ (a = d ∧ b = c)`. -/
theorem two_squares_unique {p a b c d : ℕ} (hp : Nat.Prime p)
    (hab : p = a ^ 2 + b ^ 2) (hcd : p = c ^ 2 + d ^ 2) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  -- All four legs are positive.
  obtain ⟨ha, hb⟩ := pos_of_prime_eq_sq_add_sq hp hab
  obtain ⟨hc, hd⟩ := pos_of_prime_eq_sq_add_sq hp hcd
  -- Integer versions of the data.
  have hP : (p : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by exact_mod_cast hab
  have hQ : (p : ℤ) = (c : ℤ) ^ 2 + (d : ℤ) ^ 2 := by exact_mod_cast hcd
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hA : (0 : ℤ) < (a : ℤ) := by exact_mod_cast ha
  have hB : (0 : ℤ) < (b : ℤ) := by exact_mod_cast hb
  have hC : (0 : ℤ) < (c : ℤ) := by exact_mod_cast hc
  have hD : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
  have hp_pos : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  -- p ∣ (AD − BC)(AD + BC).
  have hfac : ((a : ℤ) * d - b * c) * ((a : ℤ) * d + b * c) = (p : ℤ) * (d ^ 2 - b ^ 2) :=
    cross_factor_dvd hP hQ
  have hdvd : (p : ℤ) ∣ ((a : ℤ) * d - b * c) * ((a : ℤ) * d + b * c) := ⟨_, hfac⟩
  -- Norm identity p² = (A²+B²)(C²+D²), used for the bounds.
  have hpp : (p : ℤ) ^ 2 = ((a : ℤ) ^ 2 + b ^ 2) * ((c : ℤ) ^ 2 + d ^ 2) := by
    rw [← hP, ← hQ]; ring
  -- Both candidate squares are ≤ p² (cheap: linear over the square-atoms).
  have hbound_diff : ((a : ℤ) * d - b * c) ^ 2 ≤ (p : ℤ) ^ 2 := by
    linarith [sq_nonneg ((a : ℤ) * c + b * d), hpp, brahmagupta_diff (a : ℤ) b c d]
  have hbound_sum : ((a : ℤ) * d + b * c) ^ 2 ≤ (p : ℤ) ^ 2 := by
    linarith [sq_nonneg ((a : ℤ) * c - b * d), hpp, brahmagupta_sum (a : ℤ) b c d]
  -- ad + bc is strictly positive (all legs positive).
  have hsum_pos : (0 : ℤ) < (a : ℤ) * d + b * c := by positivity
  -- Euclid: p divides one of the two factors.
  rcases (hpz.dvd_mul.mp hdvd) with hdvd_diff | hdvd_sum
  · -- Case p ∣ (AD − BC). It is `0` or `±p`; the `±p` branch is impossible.
    have hzero : (a : ℤ) * d - b * c = 0 := by
      obtain ⟨k, hk⟩ := hdvd_diff
      have hp2pos : (0 : ℤ) < (p : ℤ) ^ 2 := by positivity
      have hsq_eq : ((a : ℤ) * d - b * c) ^ 2 = (p : ℤ) ^ 2 * k ^ 2 := by rw [hk]; ring
      have hk2 : (p : ℤ) ^ 2 * k ^ 2 ≤ (p : ℤ) ^ 2 := by rw [← hsq_eq]; exact hbound_diff
      have hk2le : k ^ 2 ≤ 1 :=
        le_of_mul_le_mul_left (by linarith [hk2] : (p : ℤ) ^ 2 * k ^ 2 ≤ (p : ℤ) ^ 2 * 1) hp2pos
      have hk_le : k ≤ 1 := by nlinarith [hk2le, sq_nonneg (k - 1)]
      have hk_ge : -1 ≤ k := by nlinarith [hk2le, sq_nonneg (k + 1)]
      rcases (by omega : k = -1 ∨ k = 0 ∨ k = 1) with rfl | rfl | rfl
      · exfalso
        have hpos2 : (0 : ℤ) < (a : ℤ) * c + b * d := by positivity
        have hdiff_sq : ((a : ℤ) * d - b * c) ^ 2 = (p : ℤ) ^ 2 := by rw [hk]; ring
        have hcomp : ((a : ℤ) * c + b * d) ^ 2 = 0 := by
          linarith [brahmagupta_diff (a : ℤ) b c d, hpp, hdiff_sq]
        nlinarith [hcomp, mul_pos hpos2 hpos2]
      · rw [hk]; ring
      · exfalso
        have hpos2 : (0 : ℤ) < (a : ℤ) * c + b * d := by positivity
        have hdiff_sq : ((a : ℤ) * d - b * c) ^ 2 = (p : ℤ) ^ 2 := by rw [hk]; ring
        have hcomp : ((a : ℤ) * c + b * d) ^ 2 = 0 := by
          linarith [brahmagupta_diff (a : ℤ) b c d, hpp, hdiff_sq]
        nlinarith [hcomp, mul_pos hpos2 hpos2]
    -- AD = BC ⇒ cross condition; equal norms ⇒ pairs equal.
    have hcross : a * d = b * c := by
      have : (a : ℤ) * d = b * c := by linarith [hzero]
      exact_mod_cast this
    have hnorm : a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2 := by omega
    have hposn : 0 < a ^ 2 + b ^ 2 := by positivity
    exact Or.inl (pair_eq_of_cross hcross hnorm hposn)
  · -- Case p ∣ (AD + BC). Here 0 < AD + BC ≤ p, so AD + BC = p exactly.
    have hle : (a : ℤ) * d + b * c ≤ (p : ℤ) := by
      nlinarith [hbound_sum, hsum_pos, hp_pos]
    have heq : (a : ℤ) * d + b * c = (p : ℤ) := by
      obtain ⟨k, hk⟩ := hdvd_sum
      have hkpos : 0 < k := by
        rcases mul_pos_iff.mp (hk ▸ hsum_pos) with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · linarith [hp_pos]
      have hk_le1 : k ≤ 1 := by
        have hmul : (p : ℤ) * k ≤ (p : ℤ) * 1 := by rw [mul_one, ← hk]; exact hle
        exact le_of_mul_le_mul_left hmul hp_pos
      have : k = 1 := le_antisymm hk_le1 hkpos
      rw [hk, this, mul_one]
    -- Companion square (AC − BD)² vanishes ⇒ AC = BD.
    have heq_sq : ((a : ℤ) * d + b * c) ^ 2 = (p : ℤ) ^ 2 := by rw [heq]
    have hcomp : ((a : ℤ) * c - b * d) ^ 2 = 0 := by
      linarith [brahmagupta_sum (a : ℤ) b c d, hpp, heq_sq]
    have hACBD : (a : ℤ) * c = b * d := by
      have hsub : (a : ℤ) * c - b * d = 0 := by
        rw [pow_two, mul_self_eq_zero] at hcomp; exact hcomp
      linarith [hsub]
    have hcross : a * c = b * d := by exact_mod_cast hACBD
    have hnorm : a ^ 2 + b ^ 2 = d ^ 2 + c ^ 2 := by omega
    have hposn : 0 < a ^ 2 + b ^ 2 := by positivity
    obtain ⟨h1, h2⟩ := pair_eq_of_cross hcross hnorm hposn
    exact Or.inr ⟨h1, h2⟩

/-! ## Step 6: corollaries packaging existence (OQ-01) + uniqueness. -/

/-- Any two representations of a prime coincide as unordered pairs. This is
    `two_squares_unique` restated as a `Multiset` equality. -/
theorem representation_unique_up_to_order {p a b c d : ℕ} (hp : Nat.Prime p)
    (hab : p = a ^ 2 + b ^ 2) (hcd : p = c ^ 2 + d ^ 2) :
    ({a, b} : Multiset ℕ) = {c, d} := by
  rcases two_squares_unique hp hab hcd with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]; exact Multiset.pair_comm d c

/-- `2 = 1² + 1²` is the *only* way to write `2` as a sum of two squares. -/
theorem two_repr_unique {a b : ℕ} (h : (2 : ℕ) = a ^ 2 + b ^ 2) :
    a = 1 ∧ b = 1 := by
  rcases two_squares_unique Nat.prime_two h (by norm_num : (2 : ℕ) = 1 ^ 2 + 1 ^ 2) with
    ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> exact ⟨h1, h2⟩

end InfinitudePrimes4k1OQ02
