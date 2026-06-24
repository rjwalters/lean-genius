/-
# Fermat Two Squares OQ-06: Brahmagupta–Fibonacci Identity and the
# Non-Uniqueness of Two-Square Representations for Products

The Brahmagupta–Fibonacci identity expresses a product of two sums of squares as
a sum of two squares in *two* different ways:

  (x² + y²)(u² + v²) = (xu − yv)² + (xv + yu)²        (form 1)
                     = (xu + yv)² + (xv − yu)²        (form 2)

Multiplicative closure of the two-square property is already in Mathlib
(`sq_add_sq_mul`, `Nat.sq_add_sq_mul`), but Mathlib records only **one** of the
two forms, and says nothing about whether the two forms give genuinely different
representations.

The mathematical content of this entry is the **non-uniqueness** phenomenon: when
`x ≠ y` and `u ≠ v` (and all are positive), the two Brahmagupta forms are
essentially distinct representations — they differ even as unordered pairs of
squares.  This is the structural reason a product of two distinct primes
`≡ 1 (mod 4)` has (at least) two representations as a sum of two squares, e.g.

  65 = 5 · 13 = 1² + 8² = 4² + 7².

We also re-derive form 1 conceptually from the multiplicativity of the Gaussian
integer norm `N(a + bi) = a² + b²` (`Zsqrtd.norm_mul`), exhibiting the identity as
a shadow of `ℤ[i]` being a normed multiplicative monoid.

## Main results

* `brahmagupta_form1`, `brahmagupta_form2` — the two sign-forms of the identity.
* `gaussianInt_norm_mk` / `brahmagupta_via_norm` — the Gaussian-integer derivation.
* `sq_add_sq_mul'` — the second-form closure lemma (complementing Mathlib's
  `sq_add_sq_mul`, which gives the first form).
* `two_distinct_representations` — **headline**: the two forms are essentially
  distinct when `x ≠ y` and `u ≠ v`.
* `prime_mul_prime_two_squares_two_ways` — a product of two distinct primes
  `≡ 1 (mod 4)` is a sum of two squares in two essentially different ways.
* `sixtyfive_two_ways` — the concrete witness 65 = 1² + 8² = 4² + 7².

All results are fully machine-checked with no `sorry` and no extra axioms.
-/

import Mathlib

namespace FermatTwoSquaresOQ06

/-! ## The two Brahmagupta–Fibonacci forms -/

/-- **Brahmagupta–Fibonacci identity, first form.**
A product of two sums of two squares is a sum of two squares. -/
theorem brahmagupta_form1 (x y u v : ℤ) :
    (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2) = (x * u - y * v) ^ 2 + (x * v + y * u) ^ 2 := by
  ring

/-- **Brahmagupta–Fibonacci identity, second form.**
Swapping the sign of one cross term yields a *different* decomposition. -/
theorem brahmagupta_form2 (x y u v : ℤ) :
    (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2) = (x * u + y * v) ^ 2 + (x * v - y * u) ^ 2 := by
  ring

/-! ## Conceptual derivation via the Gaussian integer norm

The norm on `ℤ[i] = ℤ√(-1)` is `N⟨a, b⟩ = a² + b²`, and it is multiplicative.
Brahmagupta's identity is exactly `N(z · w) = N z · N w` written out in coordinates. -/

/-- The Gaussian-integer norm of `a + b·i` is `a² + b²`. -/
theorem gaussianInt_norm_mk (a b : ℤ) :
    (Zsqrtd.mk a b : ℤ√(-1)).norm = a ^ 2 + b ^ 2 := by
  simp [Zsqrtd.norm]; ring

/-- Brahmagupta's first form re-derived from multiplicativity of the Gaussian
norm `Zsqrtd.norm_mul`. The two-square property is multiplicative *because* the
norm `ℤ[i] →* ℤ` is a monoid homomorphism. -/
theorem brahmagupta_via_norm (x y u v : ℤ) :
    (x ^ 2 + y ^ 2) * (u ^ 2 + v ^ 2) = (x * u - y * v) ^ 2 + (x * v + y * u) ^ 2 := by
  have hmul := Zsqrtd.norm_mul (Zsqrtd.mk x y : ℤ√(-1)) (Zsqrtd.mk u v)
  -- compute both sides via `gaussianInt_norm_mk`
  rw [gaussianInt_norm_mk x y, gaussianInt_norm_mk u v] at hmul
  -- the product `⟨x,y⟩ * ⟨u,v⟩` has coordinates `⟨xu - yv, xv + yu⟩`
  have hprod : (Zsqrtd.mk x y : ℤ√(-1)) * Zsqrtd.mk u v
      = Zsqrtd.mk (x * u - y * v) (x * v + y * u) :=
    Zsqrtd.ext (by simp; ring) (by simp)
  rw [hprod, gaussianInt_norm_mk] at hmul
  linarith [hmul]

/-! ## Multiplicative closure (second form)

Mathlib's `sq_add_sq_mul` packages the *first* form.  Here is the *second* form,
so that both representations are available as existence statements. -/

/-- The set of sums of two squares is closed under multiplication, recorded with
the **second** Brahmagupta form (cf. Mathlib's `sq_add_sq_mul`, which records the
first form). -/
theorem sq_add_sq_mul' {R : Type*} [CommRing R] {a b x y u v : R}
    (ha : a = x ^ 2 + y ^ 2) (hb : b = u ^ 2 + v ^ 2) :
    ∃ r s : R, a * b = r ^ 2 + s ^ 2 :=
  ⟨x * u + y * v, x * v - y * u, by rw [ha, hb]; ring⟩

/-! ## Non-uniqueness: the two forms are essentially distinct

Two representations `n = a² + b²` and `n = c² + d²` are *essentially the same*
when they agree as unordered pairs of squares, i.e. `{a², b²} = {c², d²}`.  We
show the two Brahmagupta forms are essentially distinct as soon as `x ≠ y` and
`u ≠ v` (with all four positive). -/

/-- **Headline.** For positive `x, y, u, v` with `x ≠ y` and `u ≠ v`, the two
Brahmagupta forms of `(x²+y²)(u²+v²)` are essentially distinct: the multiset of
squares `{(xu−yv)², (xv+yu)²}` differs from `{(xu+yv)², (xv−yu)²}`.

The two "sum" coordinates `xv+yu` and `xu+yv` are the large entries of each
representation; they coincide only when `(x−y)(v−u) = 0`.  The "difference"
coordinates can never match a "sum" coordinate because all variables are
positive. Hence under `x ≠ y`, `u ≠ v` the representations cannot be matched. -/
theorem two_distinct_representations {x y u v : ℤ}
    (hx : 0 < x) (hy : 0 < y) (hu : 0 < u) (hv : 0 < v)
    (hxy : x ≠ y) (huv : u ≠ v) :
    ¬ ( ((x * u - y * v) ^ 2 = (x * u + y * v) ^ 2 ∧
         (x * v + y * u) ^ 2 = (x * v - y * u) ^ 2)
      ∨ ((x * u - y * v) ^ 2 = (x * v - y * u) ^ 2 ∧
         (x * v + y * u) ^ 2 = (x * u + y * v) ^ 2) ) := by
  -- positivity facts
  have hxu : 0 < x * u := mul_pos hx hu
  have hyv : 0 < y * v := mul_pos hy hv
  rintro (⟨h1, _⟩ | ⟨_, h2⟩)
  · -- form-1 "diff" coordinate equals form-2 "sum" coordinate ⇒ `4·xu·yv = 0`
    -- since `(xu+yv)² − (xu−yv)² = 4·(xu)(yv)`.
    have hkey : (x * u + y * v) ^ 2 - (x * u - y * v) ^ 2 = 4 * (x * u) * (y * v) := by
      ring
    rw [h1] at hkey
    -- LHS is now `0`, but RHS `> 0`
    nlinarith [mul_pos hxu hyv]
  · -- the two "sum" coordinates match ⇒ `(x−y)(v−u)(x+y)(u+v) = 0`
    have hkey : (x * v + y * u) ^ 2 - (x * u + y * v) ^ 2
        = (x - y) * (v - u) * ((x + y) * (u + v)) := by ring
    rw [h2] at hkey
    -- `(x+y)(u+v) > 0`, so the first factor must vanish
    have hpos : 0 < (x + y) * (u + v) := mul_pos (by linarith) (by linarith)
    have hzero : (x - y) * (v - u) * ((x + y) * (u + v)) = 0 := by linarith
    have : (x - y) * (v - u) = 0 := by
      rcases mul_eq_zero.mp hzero with h | h
      · exact h
      · exact absurd h (ne_of_gt hpos)
    rcases mul_eq_zero.mp this with h | h
    · exact hxy (by linarith)
    · exact huv (by linarith)

/-! ## Application to products of distinct primes `≡ 1 (mod 4)` -/

/-- An odd prime `p` with `p % 4 ≠ 3` has a representation `p = x² + y²` with
`x, y > 0` and `x ≠ y`. (Positivity: a zero coordinate would force `p` to be a
perfect square; `x = y` would force `p` even.) -/
theorem prime_rep_pos_ne {p : ℕ} [Fact p.Prime] (hodd : Odd p) (hp : p % 4 ≠ 3) :
    ∃ x y : ℤ, (p : ℤ) = x ^ 2 + y ^ 2 ∧ 0 < x ∧ 0 < y ∧ x ≠ y := by
  have hpprime : p.Prime := Fact.out
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) hp
  -- `hab : a ^ 2 + b ^ 2 = p`
  -- a coordinate equal to `0` would make `p` a perfect square, impossible.
  have hsquare_absurd : ∀ c : ℕ, c ^ 2 = p → False := by
    intro c hc
    have hdvd : c ∣ p := ⟨c, by rw [← hc]; ring⟩
    rcases hpprime.eq_one_or_self_of_dvd c hdvd with h1 | h1
    · rw [h1] at hc; simp at hc; have := hpprime.two_le; omega
    · rw [h1] at hc; nlinarith [hpprime.two_le]
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · exact (hsquare_absurd b (by simpa using hab)).elim
    · exact h
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with rfl | h
    · exact (hsquare_absurd a (by simpa using hab)).elim
    · exact h
  -- `a = b` would make `p = 2a²` even, contradicting oddness.
  have hne : a ≠ b := by
    rintro rfl
    have h2 : 2 ∣ p := ⟨a ^ 2, by rw [← hab]; ring⟩
    have hp2 : p = 2 := ((hpprime.eq_one_or_self_of_dvd 2 h2).resolve_left (by norm_num)).symm
    rw [hp2] at hodd
    exact (by norm_num [Nat.odd_iff] : ¬ Odd 2) hodd
  exact ⟨(a : ℤ), (b : ℤ), by rw [← hab]; push_cast; ring,
    by exact_mod_cast ha, by exact_mod_cast hb, by exact_mod_cast hne⟩

/-- **Product of two distinct primes `≡ 1 (mod 4)`** is a sum of two squares in
two essentially different ways. The two representations come from the two
Brahmagupta forms applied to representations of `p` and `q`. -/
theorem prime_mul_prime_two_squares_two_ways {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (hpodd : Odd p) (hqodd : Odd q) (hp : p % 4 ≠ 3) (hq : q % 4 ≠ 3) :
    ∃ a b c d : ℤ,
      ((p * q : ℕ) : ℤ) = a ^ 2 + b ^ 2 ∧ ((p * q : ℕ) : ℤ) = c ^ 2 + d ^ 2 ∧
      ¬ ((a ^ 2 = c ^ 2 ∧ b ^ 2 = d ^ 2) ∨ (a ^ 2 = d ^ 2 ∧ b ^ 2 = c ^ 2)) := by
  obtain ⟨x, y, hpxy, hx, hy, hxy⟩ := prime_rep_pos_ne hpodd hp
  obtain ⟨u, v, hquv, hu, hv, huv⟩ := prime_rep_pos_ne hqodd hq
  refine ⟨x * u - y * v, x * v + y * u, x * u + y * v, x * v - y * u, ?_, ?_, ?_⟩
  · push_cast; rw [hpxy, hquv]; ring
  · push_cast; rw [hpxy, hquv]; ring
  · exact two_distinct_representations hx hy hu hv hxy huv

/-! ## Concrete witness -/

/-- The smallest product of two distinct primes `≡ 1 (mod 4)`,
`65 = 5 · 13`, is a sum of two squares in two essentially different ways:
`65 = 1² + 8² = 4² + 7²`, with `{1, 64} ≠ {16, 49}`. -/
theorem sixtyfive_two_ways :
    (65 : ℤ) = 1 ^ 2 + 8 ^ 2 ∧ (65 : ℤ) = 4 ^ 2 + 7 ^ 2 ∧
      ¬ (((1 : ℤ) ^ 2 = 4 ^ 2 ∧ (8 : ℤ) ^ 2 = 7 ^ 2) ∨
         ((1 : ℤ) ^ 2 = 7 ^ 2 ∧ (8 : ℤ) ^ 2 = 4 ^ 2)) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  norm_num

end FermatTwoSquaresOQ06
