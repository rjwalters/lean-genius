import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

/-
# Lifting the Exponent for **sums** `xⁿ + yⁿ`, the even prime `p = 2`, and an
all-primes dispatch

The companion file `LiftingTheExponentOQ02` computes `v₂(xⁿ - yⁿ)`. This file
handles the **sum** `xⁿ + yⁿ`, where the behaviour at `p = 2` splits sharply on
the parity of the exponent:

* **`n` odd.**  `v₂(xⁿ + yⁿ) = v₂(x + y)` — exactly the odd-prime sum shape with
  no `v₂(n)` correction, because `2 ∤ n`. This is obtained from the *general*
  prime lemma `emultiplicity_pow_sub_pow_of_prime` (valid for **every** prime,
  `p` included, as long as `p ∤ n`) via `xⁿ + yⁿ = xⁿ - (-y)ⁿ`.

* **`n` even (and `n ≠ 0`).**  For odd `x, y`,
  `xⁿ + yⁿ ≡ 2 (mod 8)`, so `v₂(xⁿ + yⁿ) = 1` *exactly*, independent of `x, y`
  and `n`. The mechanism is the classical `odd² ≡ 1 (mod 8)`.

Mathlib supplies the **odd-prime** sum LTE `Int.emultiplicity_pow_add_pow`
(which carries a `+ vₚ(n)` term) but no `p = 2` sum statement. We fill that gap
and then package everything into a single **all-primes dispatch**
`emultiplicity_pow_add_pow_odd_exp`: for *any* prime `p` and *odd* exponent `n`,

  vₚ(xⁿ + yⁿ) = vₚ(x + y) + vₚ(n),

which specialises to `v₂(x + y)` at `p = 2` precisely because `v₂(n) = 0` for
odd `n`. The contribution is the `p = 2` analysis (both parities) and the
uniform statement; the odd-prime core is Mathlib's.
-/

namespace LiftingTheExponentOQ02OQ01

variable {x y : ℤ} {n : ℕ}

/-! ### Arithmetic helpers -/

/-- Two odd integers sum to an even integer. -/
theorem two_dvd_add_of_not_dvd (hx : ¬(2 : ℤ) ∣ x) (hy : ¬(2 : ℤ) ∣ y) :
    (2 : ℤ) ∣ x + y := by
  rcases Int.even_or_odd x with hex | hox
  · exact absurd hex.two_dvd hx
  rcases Int.even_or_odd y with hey | hoy
  · exact absurd hey.two_dvd hy
  obtain ⟨a, rfl⟩ := hox
  obtain ⟨b, rfl⟩ := hoy
  exact ⟨a + b + 1, by ring⟩

/-- If `2 ∤ x` and `2 ∣ x + y` then `2 ∤ y`. -/
theorem not_dvd_right_of_dvd_add (hx : ¬(2 : ℤ) ∣ x) (hxy : (2 : ℤ) ∣ x + y) :
    ¬(2 : ℤ) ∣ y := by
  intro hy
  exact hx (by simpa using (Dvd.dvd.sub hxy hy))

/-- An integer not divisible by `2` is odd. -/
theorem odd_of_not_two_dvd {a : ℤ} (ha : ¬(2 : ℤ) ∣ a) : Odd a := by
  rcases Int.even_or_odd a with h | h
  · exact absurd h.two_dvd ha
  · exact h

/-- `¬ (2 : ℤ) ∣ ↑n` for odd `n`. -/
theorem two_not_dvd_cast_of_odd (hn : Odd n) : ¬(2 : ℤ) ∣ (n : ℤ) := by
  obtain ⟨m, rfl⟩ := hn
  push_cast
  omega

/-- **Odd squares are `1` mod `8`.** For any odd integer `a`, `a² ≡ 1 [ZMOD 8]`. -/
theorem odd_sq_modEq_eight {a : ℤ} (ha : Odd a) : a ^ 2 ≡ 1 [ZMOD 8] := by
  obtain ⟨k, rfl⟩ := ha
  obtain ⟨j, hj⟩ := Int.even_mul_succ_self k
  refine (Int.modEq_iff_dvd.mpr ⟨-j, ?_⟩)
  -- 1 - (2k+1)^2 = 8 * (-j),  using k*(k+1) = j + j
  linear_combination (-4 : ℤ) * hj

/-! ### The odd-exponent case at `p = 2` -/

/-- **Sum LTE at `p = 2`, odd exponent (`emultiplicity` form).**
For odd `x, y` and odd `n`, `v₂(xⁿ + yⁿ) = v₂(x + y)`. There is no `v₂(n)`
correction because `2 ∤ n`. -/
theorem two_emultiplicity_pow_add_pow_odd
    (hx : ¬(2 : ℤ) ∣ x) (hy : ¬(2 : ℤ) ∣ y) (hn : Odd n) :
    emultiplicity 2 (x ^ n + y ^ n) = emultiplicity 2 (x + y) := by
  have hxy : (2 : ℤ) ∣ x + y := two_dvd_add_of_not_dvd hx hy
  rw [← sub_neg_eq_add] at hxy
  rw [← sub_neg_eq_add, ← sub_neg_eq_add, ← Odd.neg_pow hn]
  exact emultiplicity_pow_sub_pow_of_prime Int.prime_two hxy hx (two_not_dvd_cast_of_odd hn)

/-! ### The even-exponent case at `p = 2` -/

/-- For odd `x` and even `n`, `xⁿ ≡ 1 [ZMOD 8]`. -/
theorem odd_pow_even_modEq_eight (hx : ¬(2 : ℤ) ∣ x) (hn : Even n) :
    x ^ n ≡ 1 [ZMOD 8] := by
  obtain ⟨m, rfl⟩ := hn
  have hox : Odd x := odd_of_not_two_dvd hx
  have hoxm : Odd (x ^ m) := hox.pow
  have h := odd_sq_modEq_eight hoxm
  calc x ^ (m + m) = (x ^ m) ^ 2 := by ring
    _ ≡ 1 [ZMOD 8] := h

/-- **Sum LTE at `p = 2`, even exponent (`emultiplicity` form).**
For odd `x, y` and even `n ≠ 0`, `v₂(xⁿ + yⁿ) = 1` exactly: the sum is
`≡ 2 (mod 8)`. -/
theorem two_emultiplicity_pow_add_pow_even
    (hx : ¬(2 : ℤ) ∣ x) (hy : ¬(2 : ℤ) ∣ y) (hn : Even n) :
    emultiplicity 2 (x ^ n + y ^ n) = 1 := by
  have hmod : x ^ n + y ^ n ≡ 2 [ZMOD 8] := by
    have hx8 := odd_pow_even_modEq_eight hx hn
    have hy8 := odd_pow_even_modEq_eight hy hn
    calc x ^ n + y ^ n ≡ 1 + 1 [ZMOD 8] := hx8.add hy8
      _ = 2 := by ring
  -- extract z = 8 t + 2
  obtain ⟨t, ht⟩ : ∃ t, x ^ n + y ^ n = 8 * t + 2 := by
    obtain ⟨c, hc⟩ := (Int.modEq_iff_dvd.mp hmod)
    exact ⟨-c, by linarith⟩
  have h2 : (2 : ℤ) ^ 1 ∣ x ^ n + y ^ n := ⟨4 * t + 1, by rw [ht]; ring⟩
  have h4 : ¬(2 : ℤ) ^ (1 + 1) ∣ x ^ n + y ^ n := by
    rintro ⟨s, hs⟩
    rw [ht] at hs
    omega
  have : emultiplicity (2 : ℤ) (x ^ n + y ^ n) = ((1 : ℕ) : ℕ∞) :=
    emultiplicity_eq_coe.mpr ⟨h2, h4⟩
  simpa using this

/-! ### All-primes dispatch (odd exponent) -/

/-- **Unified sum LTE for an odd exponent, every prime.**
For a prime `p`, odd `n`, with `p ∣ x + y` and `p ∤ x`,

  vₚ(xⁿ + yⁿ) = vₚ(x + y) + vₚ(n).

For odd primes this is Mathlib's `Int.emultiplicity_pow_add_pow`; for `p = 2`
the `vₚ(n)` term vanishes (`2 ∤ n`) and it reduces to
`two_emultiplicity_pow_add_pow_odd`. -/
theorem emultiplicity_pow_add_pow_odd_exp
    {p : ℕ} (hp : p.Prime) (hx : ¬(p : ℤ) ∣ x) (hxy : (p : ℤ) ∣ x + y) (hn : Odd n) :
    emultiplicity (p : ℤ) (x ^ n + y ^ n)
      = emultiplicity (p : ℤ) (x + y) + emultiplicity p n := by
  rcases eq_or_ne p 2 with hp2 | hp2
  · subst hp2
    have hx' : ¬(2 : ℤ) ∣ x := by simpa using hx
    have hxy' : (2 : ℤ) ∣ x + y := by simpa using hxy
    have hy : ¬(2 : ℤ) ∣ y := not_dvd_right_of_dvd_add hx' hxy'
    have hzero : emultiplicity 2 n = 0 :=
      emultiplicity_eq_zero.mpr (by have := Nat.odd_iff.mp hn; omega)
    rw [hzero, add_zero]
    simpa using two_emultiplicity_pow_add_pow_odd hx' hy hn
  · have hp1 : Odd p := hp.odd_of_ne_two hp2
    exact Int.emultiplicity_pow_add_pow hp hp1 hxy hx hn

/-! ### `padicValInt` (schoolbook `v₂`) forms -/

/-- For odd `x, y`, odd `n`, with `x + y ≠ 0`, the sum `xⁿ + yⁿ` is nonzero. -/
theorem pow_add_pow_ne_zero_odd
    (hx : ¬(2 : ℤ) ∣ x) (hy : ¬(2 : ℤ) ∣ y) (hn : Odd n) (hadd : x + y ≠ 0) :
    x ^ n + y ^ n ≠ 0 := by
  intro h0
  have key := two_emultiplicity_pow_add_pow_odd hx hy hn
  rw [h0, emultiplicity_zero] at key
  have hfin : FiniteMultiplicity (2 : ℤ) (x + y) :=
    Int.finiteMultiplicity_iff.mpr ⟨by decide, hadd⟩
  rw [hfin.emultiplicity_eq_multiplicity] at key
  exact (ENat.coe_ne_top _) key.symm

/-- **Sum LTE at `p = 2`, odd exponent (`padicValInt` form).**
For odd `x, y`, odd `n`, and `x + y ≠ 0`, `v₂(xⁿ + yⁿ) = v₂(x + y)`. -/
theorem two_padicValInt_pow_add_pow_odd
    (hx : ¬(2 : ℤ) ∣ x) (hy : ¬(2 : ℤ) ∣ y) (hn : Odd n) (hadd : x + y ≠ 0) :
    padicValInt 2 (x ^ n + y ^ n) = padicValInt 2 (x + y) := by
  have hne0 : x ^ n + y ^ n ≠ 0 := pow_add_pow_ne_zero_odd hx hy hn hadd
  have key := two_emultiplicity_pow_add_pow_odd hx hy hn
  have hfin_lhs : FiniteMultiplicity (2 : ℤ) (x ^ n + y ^ n) :=
    Int.finiteMultiplicity_iff.mpr ⟨by decide, hne0⟩
  have hfin_add : FiniteMultiplicity (2 : ℤ) (x + y) :=
    Int.finiteMultiplicity_iff.mpr ⟨by decide, hadd⟩
  rw [hfin_lhs.emultiplicity_eq_multiplicity, hfin_add.emultiplicity_eq_multiplicity] at key
  have hmul : multiplicity (2 : ℤ) (x ^ n + y ^ n) = multiplicity (2 : ℤ) (x + y) := by
    exact_mod_cast key
  rw [padicValInt.of_ne_one_ne_zero (by decide) hne0,
      padicValInt.of_ne_one_ne_zero (by decide) hadd]
  exact_mod_cast hmul

/-- **Sum LTE at `p = 2`, even exponent (`padicValInt` form).**
For odd `x, y` and even `n ≠ 0`, `v₂(xⁿ + yⁿ) = 1`. -/
theorem two_padicValInt_pow_add_pow_even
    (hx : ¬(2 : ℤ) ∣ x) (hy : ¬(2 : ℤ) ∣ y) (hn : Even n) :
    padicValInt 2 (x ^ n + y ^ n) = 1 := by
  have hne0 : x ^ n + y ^ n ≠ 0 := by
    intro h0
    -- sum of two odds is even, so cannot be 0? we instead use it's 2 mod 8 hence ≠0
    have hmod : x ^ n + y ^ n ≡ 2 [ZMOD 8] := by
      have hx8 := odd_pow_even_modEq_eight hx hn
      have hy8 := odd_pow_even_modEq_eight hy hn
      calc x ^ n + y ^ n ≡ 1 + 1 [ZMOD 8] := hx8.add hy8
        _ = 2 := by ring
    rw [h0] at hmod
    have : (8 : ℤ) ∣ (2 - 0) := (Int.modEq_iff_dvd.mp hmod)
    omega
  have hemul := two_emultiplicity_pow_add_pow_even hx hy hn
  have hfin_lhs : FiniteMultiplicity (2 : ℤ) (x ^ n + y ^ n) :=
    Int.finiteMultiplicity_iff.mpr ⟨by decide, hne0⟩
  rw [hfin_lhs.emultiplicity_eq_multiplicity] at hemul
  have hmul : multiplicity (2 : ℤ) (x ^ n + y ^ n) = 1 := by exact_mod_cast hemul
  rw [padicValInt.of_ne_one_ne_zero (by decide) hne0]
  exact_mod_cast hmul

end LiftingTheExponentOQ02OQ01
