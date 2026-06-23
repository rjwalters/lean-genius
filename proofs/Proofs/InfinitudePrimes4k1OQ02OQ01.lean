import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic

/-
# Sharpness of Two-Squares Uniqueness: Products of Primes Have Multiple Representations (OQ-02-OQ-01)

## What This Proves

Sibling `InfinitudePrimes4k1OQ02` proved that a **prime** `p` has an *essentially
unique* representation as a sum of two squares: if `p = a² + b² = c² + d²`, then
`{a, b} = {c, d}`. This file proves that uniqueness statement is **sharp** — it is
a genuinely prime phenomenon that fails the moment we leave the primes.

Concretely, if `p` and `q` are two **odd primes** written as sums of two squares,

    p = a² + b²,    q = c² + d²,

then the composite `n = p·q` has (at least) **two distinct** representations as a
sum of two squares, obtained from the two Brahmagupta–Fibonacci identities:

    n = (ac + bd)² + (ad − bc)²
    n = (ac − bd)² + (ad + bc)²

and the two unordered pairs of summands are genuinely different. The canonical
witness is

    65 = 5 · 13 = 1² + 8² = 4² + 7².

So while a prime is a sum of two squares in *exactly one* way, a product of two
odd primes is a sum of two squares in *at least two* ways. Uniqueness is exactly
the boundary between prime and composite.

## The Proof Idea

The two Brahmagupta–Fibonacci identities are pure `ring` facts. The mathematical
content is that the two resulting unordered pairs of squares are *distinct*. We
show the pair `{(ac+bd)², (ad−bc)²}` cannot equal `{(ac−bd)², (ad+bc)²}` by
refuting both ways the larger summand `(ac+bd)²` could match:

  * `(ac+bd)² = (ac−bd)²` forces `4·abcd = 0`, impossible since all of
    `a, b, c, d` are positive (a prime is never a perfect square).
  * `(ac+bd)² = (ad+bc)²` factors as `(a−b)(a+b)(c−d)(c+d) = 0`, forcing `a = b`
    or `c = d`; but an *odd* prime `a² + b²` cannot have `a = b` (that would make
    it `2a²`, even).

## Status
- [x] Complete proof, 0 sorries, 0 axioms.
- [x] Fully elementary: `ring`, `nlinarith`, `omega`, casts, Euclid-free.

## Mathlib Dependencies
- `Nat.Prime`, `Nat.Prime.eq_one_or_self_of_dvd`, `dvd_pow_self`.
- `Int.natAbs_mul_self'`, basic `Int`/`Nat` casting lemmas.
-/

namespace InfinitudePrimes4k1OQ02OQ01

open Nat

/-! ## Step 0: a prime is never a perfect square, so both legs are positive.

Reproduced from the sibling uniqueness file so this entry is self-contained. -/

/-- If a prime `p` equals `a² + b²`, then both `a` and `b` are positive. -/
theorem pos_of_prime_eq_sq_add_sq {p a b : ℕ} (hp : Nat.Prime p)
    (h : p = a ^ 2 + b ^ 2) : 0 < a ∧ 0 < b := by
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

/-! ## Step 1: an odd prime sum of two squares has distinct legs `a ≠ b`. -/

/-- If an **odd** prime `p` equals `a² + b²`, then `a ≠ b`. (Otherwise `p = 2a²`
    would be even.) -/
theorem ne_of_odd_prime_eq_sq_add_sq {p a b : ℕ} (hp : Nat.Prime p) (hodd : Odd p)
    (h : p = a ^ 2 + b ^ 2) : a ≠ b := by
  intro hab
  have hdvd : (2 : ℕ) ∣ p := ⟨a ^ 2, by rw [h, hab]; ring⟩
  have hp2 : 2 = p := (hp.eq_one_or_self_of_dvd 2 hdvd).resolve_left (by norm_num)
  rw [← hp2] at hodd
  exact (by decide : ¬ Odd 2) hodd

/-! ## Step 2: the two Brahmagupta–Fibonacci identities (over `ℤ`). -/

theorem brahmagupta_diff (a b c d : ℤ) :
    (a * c + b * d) ^ 2 + (a * d - b * c) ^ 2 = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  ring

theorem brahmagupta_sum (a b c d : ℤ) :
    (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 = (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  ring

/-! ## Step 3: the integer core — the two pairs of squares are distinct. -/

/-- The mathematical heart: for positive `a, b, c, d` with `a ≠ b` and `c ≠ d`,
    the two Brahmagupta pairs of squares are distinct as unordered pairs. -/
theorem squares_multiset_ne {a b c d : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a ≠ b) (hcd : c ≠ d) :
    ({(a * c + b * d) ^ 2, (a * d - b * c) ^ 2} : Multiset ℤ)
      ≠ {(a * c - b * d) ^ 2, (a * d + b * c) ^ 2} := by
  intro heq
  -- `(ac+bd)²` lies in the second pair, so it equals one of its two members.
  have hmem : ((a * c + b * d) ^ 2) ∈
      ({(a * c - b * d) ^ 2, (a * d + b * c) ^ 2} : Multiset ℤ) := by
    rw [← heq]; exact Multiset.mem_cons_self _ _
  rcases Multiset.mem_cons.mp hmem with h1 | h1
  · -- `(ac+bd)² = (ac−bd)²` ⇒ `4abcd = 0`, impossible.
    have hpos : 0 < a * b * c * d := by positivity
    nlinarith [h1, hpos]
  · -- `(ac+bd)² = (ad+bc)²` ⇒ `(a−b)(a+b)(c−d)(c+d) = 0`.
    rw [Multiset.mem_singleton] at h1
    have hfac : (a - b) * (a + b) * ((c - d) * (c + d)) = 0 := by nlinarith [h1]
    have hsum_ab : 0 < a + b := by linarith
    have hsum_cd : 0 < c + d := by linarith
    have hda : a - b ≠ 0 := sub_ne_zero.mpr hab
    have hdc : c - d ≠ 0 := sub_ne_zero.mpr hcd
    rcases mul_eq_zero.mp hfac with hL | hR
    · rcases mul_eq_zero.mp hL with h | h
      · exact hda h
      · linarith
    · rcases mul_eq_zero.mp hR with h | h
      · exact hdc h
      · linarith

/-! ## Step 4: the main theorem over `ℕ`.

For two odd primes `p = a²+b²`, `q = c²+d²`, the composite `p·q` is a sum of two
squares in two distinct ways. We package the four summands as natural numbers via
`Int.natAbs` (the two "difference" terms can be negative before taking absolute
value, but their squares are what matter). -/

set_option maxHeartbeats 400000 in
/-- **Sharpness of two-squares uniqueness.** If `p` and `q` are odd primes with
    `p = a² + b²` and `q = c² + d²`, then `p · q` has two distinct representations
    as a sum of two squares:

    * `p·q = (ac+bd)² + |ad−bc|²`
    * `p·q = |ac−bd|² + (ad+bc)²`

    and the two unordered pairs of summands are different. -/
theorem product_two_representations {p q a b c d : ℕ}
    (hp : Nat.Prime p) (hq : Nat.Prime q) (hpodd : Odd p) (hqodd : Odd q)
    (hab : p = a ^ 2 + b ^ 2) (hcd : q = c ^ 2 + d ^ 2) :
    (a * c + b * d) ^ 2 + ((a : ℤ) * d - b * c).natAbs ^ 2 = p * q ∧
    ((a : ℤ) * c - b * d).natAbs ^ 2 + (a * d + b * c) ^ 2 = p * q ∧
    ({a * c + b * d, ((a : ℤ) * d - b * c).natAbs} : Multiset ℕ)
      ≠ {((a : ℤ) * c - b * d).natAbs, a * d + b * c} := by
  obtain ⟨ha, hb⟩ := pos_of_prime_eq_sq_add_sq hp hab
  obtain ⟨hc, hd⟩ := pos_of_prime_eq_sq_add_sq hq hcd
  have hne_ab : a ≠ b := ne_of_odd_prime_eq_sq_add_sq hp hpodd hab
  have hne_cd : c ≠ d := ne_of_odd_prime_eq_sq_add_sq hq hqodd hcd
  -- Integer positivity, used repeatedly below.
  have haZ : (0 : ℤ) < (a : ℤ) := by exact_mod_cast ha
  have hbZ : (0 : ℤ) < (b : ℤ) := by exact_mod_cast hb
  have hcZ : (0 : ℤ) < (c : ℤ) := by exact_mod_cast hc
  have hdZ : (0 : ℤ) < (d : ℤ) := by exact_mod_cast hd
  have hP : (p : ℤ) = (a : ℤ) ^ 2 + (b : ℤ) ^ 2 := by exact_mod_cast hab
  have hQ : (q : ℤ) = (c : ℤ) ^ 2 + (d : ℤ) ^ 2 := by exact_mod_cast hcd
  -- First representation: `(ac+bd)² + |ad−bc|² = p·q`.
  have eq1 : (a * c + b * d) ^ 2 + ((a : ℤ) * d - b * c).natAbs ^ 2 = p * q := by
    have h : (((a * c + b * d) ^ 2 + ((a : ℤ) * d - b * c).natAbs ^ 2 : ℕ) : ℤ)
        = ((p * q : ℕ) : ℤ) := by
      push_cast; rw [sq_abs, hP, hQ]; ring
    exact_mod_cast h
  -- Second representation: `|ac−bd|² + (ad+bc)² = p·q`.
  have eq2 : ((a : ℤ) * c - b * d).natAbs ^ 2 + (a * d + b * c) ^ 2 = p * q := by
    have h : ((((a : ℤ) * c - b * d).natAbs ^ 2 + (a * d + b * c) ^ 2 : ℕ) : ℤ)
        = ((p * q : ℕ) : ℤ) := by
      push_cast; rw [sq_abs, hP, hQ]; ring
    exact_mod_cast h
  refine ⟨eq1, eq2, ?_⟩
  -- Distinctness, directly over `ℕ`: the larger summand `ac+bd` of the first pair
  -- cannot match either summand of the second pair.
  intro hpair
  have hmem : (a * c + b * d) ∈
      ({((a : ℤ) * c - b * d).natAbs, a * d + b * c} : Multiset ℕ) := by
    rw [← hpair]; exact Multiset.mem_cons_self _ _
  rcases Multiset.mem_cons.mp hmem with h1 | h1
  · -- `ac + bd = |ac − bd|`, impossible since `|ac − bd| < ac + bd`.
    have hcast : (a : ℤ) * c + b * d = |(a : ℤ) * c - b * d| := by
      have h1' : ((a * c + b * d : ℕ) : ℤ) = (((a : ℤ) * c - b * d).natAbs : ℤ) := by
        exact_mod_cast h1
      rw [Int.natCast_natAbs] at h1'; push_cast at h1'; linarith [h1']
    have hlt : |(a : ℤ) * c - b * d| < (a : ℤ) * c + b * d := by
      rw [abs_lt]; exact ⟨by nlinarith [mul_pos haZ hcZ], by nlinarith [mul_pos hbZ hdZ]⟩
    linarith [hcast, hlt]
  · -- `ac + bd = ad + bc`, i.e. `(a − b)(c − d) = 0`, forcing `a = b` or `c = d`.
    rw [Multiset.mem_singleton] at h1
    have hZ : (a : ℤ) * c + b * d = (a : ℤ) * d + b * c := by exact_mod_cast h1
    have hfac : ((a : ℤ) - b) * ((c : ℤ) - d) = 0 := by linear_combination hZ
    rcases mul_eq_zero.mp hfac with h | h
    · exact hne_ab (by exact_mod_cast sub_eq_zero.mp h)
    · exact hne_cd (by exact_mod_cast sub_eq_zero.mp h)

/-! ## Step 5: the canonical concrete witness. -/

/-- `65 = 5 · 13` is a sum of two squares in two genuinely different ways. -/
theorem sixtyfive_two_ways :
    (65 : ℕ) = 5 * 13 ∧ (65 : ℕ) = 1 ^ 2 + 8 ^ 2 ∧ (65 : ℕ) = 4 ^ 2 + 7 ^ 2 ∧
      ({1, 8} : Multiset ℕ) ≠ {4, 7} := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  decide

end InfinitudePrimes4k1OQ02OQ01
