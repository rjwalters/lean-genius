/-
# Extended Binary GCD: Certified Bézout Coefficients (OQ-02-OQ-03)

## What This Proves
The Binary GCD (Stein's algorithm) computes only the *value* of `gcd`. This
file builds the **extended** binary GCD `binaryXgcd` / `binaryXgcdInt`, which
additionally returns a pair of Bézout coefficients `(x, y)` and proves the
certified identity

    a * x + b * y = gcd a b.

The coefficients are produced *through the binary reductions themselves*
(halving, parity-correction, subtract-and-halve), not by delegating to
Mathlib's `Int.gcdA` / `Int.gcdB`. We then show the produced identity is
equivalent to Mathlib's: both yield the same Bézout relation for `Int.gcd`.

## The Coefficient Algebra
Each Stein reduction transforms a Bézout relation for the reduced pair into
one for the original pair. The only non-obvious step is *un-halving* an even
operand: from `a' * x + b * y = g` with `b` odd we need integer `X, Y` with
`(2a') * X + b * Y = a' * x + b * y`. Since `b` is odd, exactly one of `x`,
`x + b` is even, giving the parity-correcting helper `hL` (and its mirror
`hR`). Every other reduction is a linear recombination on top of `hL` / `hR`.

## References
- Stein (1967); Knuth TAOCP §4.5.2; Menezes–van Oorschot–Vanstone, HAC 14.61
- Mathlib: `Int.gcd_eq_gcd_ab`, `Int.gcdA`, `Int.gcdB`, `Nat.gcd_mul_left`
- Companion to the binary-gcd strand (`Proofs/BinaryGcdOQ02.lean`)
-/
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

set_option linter.unusedVariables false

namespace BinaryGcdOQ02OQ03

/-! ## Part I: `Nat.gcd` reduction identities (Stein's invariants)

We reprove the four GCD-preserving reductions of the binary algorithm against
the current Mathlib API, self-contained. -/

/-- `gcd(2a, 2b) = 2·gcd(a, b)`. -/
theorem gcd_two_mul (a b : ℕ) : Nat.gcd (2 * a) (2 * b) = 2 * Nat.gcd a b :=
  Nat.gcd_mul_left 2 a b

/-- `gcd(2a, b) = gcd(a, b)` when `b` is odd (2 is coprime to `b`). -/
theorem gcd_two_mul_odd {a b : ℕ} (hb : b % 2 = 1) :
    Nat.gcd (2 * a) b = Nat.gcd a b := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · have hedvdb : Nat.gcd (2 * a) b ∣ b := Nat.gcd_dvd_right _ _
      have heodd : Odd (Nat.gcd (2 * a) b) := by
        rcases Nat.even_or_odd (Nat.gcd (2 * a) b) with he | he
        · exfalso
          have h2b : 2 ∣ b := dvd_trans he.two_dvd hedvdb
          omega
        · exact he
      have hcop : Nat.Coprime (Nat.gcd (2 * a) b) 2 := Nat.coprime_two_right.mpr heodd
      exact hcop.dvd_of_dvd_mul_left (Nat.gcd_dvd_left _ _)
    · exact Nat.gcd_dvd_right _ _
  · apply Nat.dvd_gcd
    · exact Dvd.dvd.mul_left (Nat.gcd_dvd_left a b) 2
    · exact Nat.gcd_dvd_right a b

/-- `gcd(a, 2b) = gcd(a, b)` when `a` is odd. -/
theorem gcd_two_mul_odd_right {a b : ℕ} (ha : a % 2 = 1) :
    Nat.gcd a (2 * b) = Nat.gcd a b := by
  rw [Nat.gcd_comm, gcd_two_mul_odd ha, Nat.gcd_comm]

/-- `gcd(m - n, n) = gcd(m, n)` for `n ≤ m`. -/
theorem gcd_sub_right {m n : ℕ} (h : n ≤ m) :
    Nat.gcd (m - n) n = Nat.gcd m n := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · have hd : Nat.gcd (m - n) n ∣ (m - n) + n :=
        Nat.dvd_add (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
      rwa [Nat.sub_add_cancel h] at hd
    · exact Nat.gcd_dvd_right _ _
  · apply Nat.dvd_gcd
    · exact Nat.dvd_sub (Nat.gcd_dvd_left _ _) (Nat.gcd_dvd_right _ _)
    · exact Nat.gcd_dvd_right _ _

/-- Both odd, `n ≤ m`: `gcd((m - n)/2, n) = gcd(m, n)`. -/
theorem gcd_odd_sub_half {m n : ℕ} (hm : m % 2 = 1) (hn : n % 2 = 1) (hge : n ≤ m) :
    Nat.gcd ((m - n) / 2) n = Nat.gcd m n := by
  have hhalf : 2 * ((m - n) / 2) = m - n := by omega
  calc Nat.gcd ((m - n) / 2) n
      = Nat.gcd (2 * ((m - n) / 2)) n := (gcd_two_mul_odd hn).symm
    _ = Nat.gcd (m - n) n := by rw [hhalf]
    _ = Nat.gcd m n := gcd_sub_right hge

/-- Both odd, `m ≤ n`: `gcd(m, (n - m)/2) = gcd(m, n)`. -/
theorem gcd_odd_sub_half_right {m n : ℕ} (hm : m % 2 = 1) (hn : n % 2 = 1) (hle : m ≤ n) :
    Nat.gcd m ((n - m) / 2) = Nat.gcd m n := by
  rw [Nat.gcd_comm, gcd_odd_sub_half hn hm hle, Nat.gcd_comm]

/-! ## Part II: parity-correcting "un-halving" helpers -/

/-- **Un-halve the left operand.** Given `a' * x + b * y = g` with `b` odd,
returns `(X, Y)` for the *doubled* left operand: `(2a')·X + b·Y = a'·x + b·y`.
If `x` is odd then `x + b` is even (since `b` is odd), keeping `X` integral. -/
def hL (a' b x y : ℤ) : ℤ × ℤ :=
  if x % 2 = 0 then (x / 2, y) else ((x + b) / 2, y - a')

/-- **Un-halve the right operand** (mirror of `hL`), with `a` odd. -/
def hR (a b' x y : ℤ) : ℤ × ℤ :=
  if y % 2 = 0 then (x, y / 2) else (x - b', (y + a) / 2)

theorem hL_spec {a' b x y : ℤ} (hb : b % 2 = 1) :
    2 * a' * (hL a' b x y).1 + b * (hL a' b x y).2 = a' * x + b * y := by
  unfold hL
  split_ifs with h
  · have h2 : (2 : ℤ) * (x / 2) = x := by omega
    show 2 * a' * (x / 2) + b * y = a' * x + b * y
    linear_combination a' * h2
  · have h2 : (2 : ℤ) * ((x + b) / 2) = x + b := by omega
    show 2 * a' * ((x + b) / 2) + b * (y - a') = a' * x + b * y
    linear_combination a' * h2

theorem hR_spec {a b' x y : ℤ} (ha : a % 2 = 1) :
    a * (hR a b' x y).1 + 2 * b' * (hR a b' x y).2 = a * x + b' * y := by
  unfold hR
  split_ifs with h
  · have h2 : (2 : ℤ) * (y / 2) = y := by omega
    show a * x + 2 * b' * (y / 2) = a * x + b' * y
    linear_combination b' * h2
  · have h2 : (2 : ℤ) * ((y + a) / 2) = y + a := by omega
    show a * (x - b') + 2 * b' * ((y + a) / 2) = a * x + b' * y
    linear_combination b' * h2

/-! ## Part III: the extended binary GCD on `ℕ`

The recursion follows Stein's algorithm; each Bézout step composes one
`hL` / `hR` un-halving with a linear recombination. -/

/-- **Extended binary GCD** on naturals: returns Bézout coefficients
`(x, y) : ℤ × ℤ` with `a * x + b * y = Nat.gcd a b`. -/
def binaryXgcd : ℕ → ℕ → ℤ × ℤ
  | 0, b => (0, 1)
  | a, 0 => (1, 0)
  | a + 1, b + 1 =>
    if ha : (a + 1) % 2 = 0 then
      if hb : (b + 1) % 2 = 0 then
        -- both even: gcd doubles, coefficients unchanged
        binaryXgcd ((a + 1) / 2) ((b + 1) / 2)
      else
        -- a+1 even, b+1 odd: un-halve the left operand
        hL (((a + 1) / 2 : ℕ) : ℤ) ((b + 1 : ℕ) : ℤ)
          (binaryXgcd ((a + 1) / 2) (b + 1)).1
          (binaryXgcd ((a + 1) / 2) (b + 1)).2
    else if hb : (b + 1) % 2 = 0 then
      -- a+1 odd, b+1 even: un-halve the right operand
      hR ((a + 1 : ℕ) : ℤ) (((b + 1) / 2 : ℕ) : ℤ)
        (binaryXgcd (a + 1) ((b + 1) / 2)).1
        (binaryXgcd (a + 1) ((b + 1) / 2)).2
    else if a + 1 > b + 1 then
      -- both odd, a+1 > b+1
      let p := hL ((a + 1 - (b + 1)) / 2 : ℕ) ((b + 1 : ℕ) : ℤ)
        (binaryXgcd ((a + 1 - (b + 1)) / 2) (b + 1)).1
        (binaryXgcd ((a + 1 - (b + 1)) / 2) (b + 1)).2
      (p.1, p.2 - p.1)
    else
      -- both odd, a+1 ≤ b+1
      let p := hR ((a + 1 : ℕ) : ℤ) ((b + 1 - (a + 1)) / 2 : ℕ)
        (binaryXgcd (a + 1) ((b + 1 - (a + 1)) / 2)).1
        (binaryXgcd (a + 1) ((b + 1 - (a + 1)) / 2)).2
      (p.1 - p.2, p.2)
  termination_by a b => a + b
  decreasing_by all_goals omega

/-! ## Part IV: Bézout correctness over `ℕ` -/

/-- **Bézout identity for the extended binary GCD.** -/
theorem binaryXgcd_bezout :
    ∀ a b : ℕ,
      (a : ℤ) * (binaryXgcd a b).1 + (b : ℤ) * (binaryXgcd a b).2
        = (Nat.gcd a b : ℤ) := by
  intro a b
  induction a, b using binaryXgcd.induct with
  | case1 b =>
    simp [binaryXgcd, Nat.gcd_zero_left]
  | case2 a =>
    simp [binaryXgcd, Nat.gcd_zero_right]
  | case3 a b ha hb ih =>
    simp only [binaryXgcd, ha, hb, ↓reduceDIte]
    have gk : Nat.gcd (a + 1) (b + 1)
        = 2 * Nat.gcd ((a + 1) / 2) ((b + 1) / 2) := by
      conv_lhs => rw [show a + 1 = 2 * ((a + 1) / 2) by omega,
        show b + 1 = 2 * ((b + 1) / 2) by omega]
      exact gcd_two_mul _ _
    have gkZ : ((Nat.gcd (a + 1) (b + 1) : ℕ) : ℤ)
        = 2 * ((Nat.gcd ((a + 1) / 2) ((b + 1) / 2) : ℕ) : ℤ) := by
      rw [gk]; push_cast; ring
    have ca : ((a + 1 : ℕ) : ℤ) = 2 * (((a + 1) / 2 : ℕ) : ℤ) := by omega
    have cb : ((b + 1 : ℕ) : ℤ) = 2 * (((b + 1) / 2 : ℕ) : ℤ) := by omega
    linear_combination 2 * ih
      + (binaryXgcd ((a + 1) / 2) ((b + 1) / 2)).1 * ca
      + (binaryXgcd ((a + 1) / 2) ((b + 1) / 2)).2 * cb - gkZ
  | case4 a b ha hb ih =>
    simp only [binaryXgcd, ha, hb, ↓reduceDIte]
    have hbodd : (b + 1) % 2 = 1 := by omega
    have gk : Nat.gcd (a + 1) (b + 1) = Nat.gcd ((a + 1) / 2) (b + 1) := by
      conv_lhs => rw [show a + 1 = 2 * ((a + 1) / 2) by omega]
      exact gcd_two_mul_odd hbodd
    have gkZ : ((Nat.gcd (a + 1) (b + 1) : ℕ) : ℤ)
        = ((Nat.gcd ((a + 1) / 2) (b + 1) : ℕ) : ℤ) := by exact_mod_cast gk
    have ca : ((a + 1 : ℕ) : ℤ) = 2 * (((a + 1) / 2 : ℕ) : ℤ) := by omega
    have hbZ : ((b + 1 : ℕ) : ℤ) % 2 = 1 := by omega
    have hs := hL_spec (a' := (((a + 1) / 2 : ℕ) : ℤ)) (b := ((b + 1 : ℕ) : ℤ))
      (x := (binaryXgcd ((a + 1) / 2) (b + 1)).1)
      (y := (binaryXgcd ((a + 1) / 2) (b + 1)).2) hbZ
    linear_combination
      (hL (((a + 1) / 2 : ℕ) : ℤ) ((b + 1 : ℕ) : ℤ)
        (binaryXgcd ((a + 1) / 2) (b + 1)).1
        (binaryXgcd ((a + 1) / 2) (b + 1)).2).1 * ca + hs + ih - gkZ
  | case5 a b ha hb ih =>
    simp only [binaryXgcd, ha, hb, ↓reduceDIte]
    have haodd : (a + 1) % 2 = 1 := by omega
    have gk : Nat.gcd (a + 1) (b + 1) = Nat.gcd (a + 1) ((b + 1) / 2) := by
      conv_lhs => rw [show b + 1 = 2 * ((b + 1) / 2) by omega]
      exact gcd_two_mul_odd_right haodd
    have gkZ : ((Nat.gcd (a + 1) (b + 1) : ℕ) : ℤ)
        = ((Nat.gcd (a + 1) ((b + 1) / 2) : ℕ) : ℤ) := by exact_mod_cast gk
    have cb : ((b + 1 : ℕ) : ℤ) = 2 * (((b + 1) / 2 : ℕ) : ℤ) := by omega
    have haZ : ((a + 1 : ℕ) : ℤ) % 2 = 1 := by omega
    have hs := hR_spec (a := ((a + 1 : ℕ) : ℤ)) (b' := (((b + 1) / 2 : ℕ) : ℤ))
      (x := (binaryXgcd (a + 1) ((b + 1) / 2)).1)
      (y := (binaryXgcd (a + 1) ((b + 1) / 2)).2) haZ
    linear_combination
      (hR ((a + 1 : ℕ) : ℤ) (((b + 1) / 2 : ℕ) : ℤ)
        (binaryXgcd (a + 1) ((b + 1) / 2)).1
        (binaryXgcd (a + 1) ((b + 1) / 2)).2).2 * cb + hs + ih - gkZ
  | case6 a b ha hb hgt ih =>
    simp only [binaryXgcd, ha, hb, hgt, ↓reduceDIte, ↓reduceIte, Nat.succ_eq_add_one]
    set c : ℕ := (a + 1 - (b + 1)) / 2 with hc
    have haodd : (a + 1) % 2 = 1 := by omega
    have hbodd : (b + 1) % 2 = 1 := by omega
    have gk : Nat.gcd (a + 1) (b + 1) = Nat.gcd c (b + 1) :=
      (gcd_odd_sub_half haodd hbodd (by omega)).symm
    have gkZ : ((Nat.gcd (a + 1) (b + 1) : ℕ) : ℤ)
        = ((Nat.gcd c (b + 1) : ℕ) : ℤ) := by exact_mod_cast gk
    have hle6 : b + 1 ≤ a + 1 := by omega
    have hsub6 : (a + 1) - (b + 1) = 2 * c := by omega
    have cdiff : ((a + 1 : ℕ) : ℤ) - ((b + 1 : ℕ) : ℤ) = 2 * ((c : ℕ) : ℤ) := by
      rw [← Nat.cast_sub hle6, hsub6]; push_cast; ring
    have hbZ : ((b + 1 : ℕ) : ℤ) % 2 = 1 := by omega
    have hs := hL_spec (a' := ((c : ℕ) : ℤ)) (b := ((b + 1 : ℕ) : ℤ))
      (x := (binaryXgcd c (b + 1)).1)
      (y := (binaryXgcd c (b + 1)).2) hbZ
    linear_combination
      (hL ((c : ℕ) : ℤ) ((b + 1 : ℕ) : ℤ)
        (binaryXgcd c (b + 1)).1 (binaryXgcd c (b + 1)).2).1 * cdiff + hs + ih - gkZ
  | case7 a b ha hb hle ih =>
    simp only [binaryXgcd, ha, hb, show ¬ (a + 1 > b + 1) from by omega, ↓reduceDIte,
      ↓reduceIte, Nat.succ_eq_add_one]
    set c : ℕ := (b + 1 - (a + 1)) / 2 with hc
    have haodd : (a + 1) % 2 = 1 := by omega
    have hbodd : (b + 1) % 2 = 1 := by omega
    have gk : Nat.gcd (a + 1) (b + 1) = Nat.gcd (a + 1) c :=
      (gcd_odd_sub_half_right haodd hbodd (by omega)).symm
    have gkZ : ((Nat.gcd (a + 1) (b + 1) : ℕ) : ℤ)
        = ((Nat.gcd (a + 1) c : ℕ) : ℤ) := by exact_mod_cast gk
    have hle7 : a + 1 ≤ b + 1 := by omega
    have hsub7 : (b + 1) - (a + 1) = 2 * c := by omega
    have cdiff : ((b + 1 : ℕ) : ℤ) - ((a + 1 : ℕ) : ℤ) = 2 * ((c : ℕ) : ℤ) := by
      rw [← Nat.cast_sub hle7, hsub7]; push_cast; ring
    have haZ : ((a + 1 : ℕ) : ℤ) % 2 = 1 := by omega
    have hs := hR_spec (a := ((a + 1 : ℕ) : ℤ)) (b' := ((c : ℕ) : ℤ))
      (x := (binaryXgcd (a + 1) c).1)
      (y := (binaryXgcd (a + 1) c).2) haZ
    linear_combination
      (hR ((a + 1 : ℕ) : ℤ) ((c : ℕ) : ℤ)
        (binaryXgcd (a + 1) c).1 (binaryXgcd (a + 1) c).2).2 * cdiff + hs + ih - gkZ

/-! ## Part V: the integer extended binary GCD -/

/-- **Extended binary GCD on integers.** Sign-adjusts the natural-number
coefficients so that `a * x + b * y = Int.gcd a b`. -/
def binaryXgcdInt (a b : ℤ) : ℤ × ℤ :=
  (a.sign * (binaryXgcd a.natAbs b.natAbs).1,
   b.sign * (binaryXgcd a.natAbs b.natAbs).2)

/-- **Bézout identity for the integer extended binary GCD.** -/
theorem binaryXgcdInt_bezout (a b : ℤ) :
    a * (binaryXgcdInt a b).1 + b * (binaryXgcdInt a b).2 = (Int.gcd a b : ℤ) := by
  unfold binaryXgcdInt
  have hbz := binaryXgcd_bezout a.natAbs b.natAbs
  have ha : a * a.sign = (a.natAbs : ℤ) := by
    rw [mul_comm]; exact Int.sign_mul_self_eq_natAbs a
  have hb : b * b.sign = (b.natAbs : ℤ) := by
    rw [mul_comm]; exact Int.sign_mul_self_eq_natAbs b
  have hg : (Int.gcd a b : ℤ) = (Nat.gcd a.natAbs b.natAbs : ℤ) := by rfl
  rw [hg]
  calc a * (a.sign * (binaryXgcd a.natAbs b.natAbs).1)
        + b * (b.sign * (binaryXgcd a.natAbs b.natAbs).2)
      = (a * a.sign) * (binaryXgcd a.natAbs b.natAbs).1
        + (b * b.sign) * (binaryXgcd a.natAbs b.natAbs).2 := by ring
    _ = (a.natAbs : ℤ) * (binaryXgcd a.natAbs b.natAbs).1
        + (b.natAbs : ℤ) * (binaryXgcd a.natAbs b.natAbs).2 := by rw [ha, hb]
    _ = (Nat.gcd a.natAbs b.natAbs : ℤ) := hbz

/-- **Equivalence to Mathlib's `Int.gcdA` / `Int.gcdB`.** The Bézout relation
produced by the extended *binary* GCD coincides with the one from Mathlib's
extended Euclidean coefficients (both certify the same `Int.gcd`). The
coefficients themselves need not be equal — Bézout coefficients are not
unique — but the certified identities agree. -/
theorem binaryXgcdInt_eq_gcdAB (a b : ℤ) :
    a * (binaryXgcdInt a b).1 + b * (binaryXgcdInt a b).2
      = a * Int.gcdA a b + b * Int.gcdB a b := by
  rw [binaryXgcdInt_bezout, Int.gcd_eq_gcd_ab]

/-! ## Part VI: concrete sanity checks -/

-- 12 = 2²·3, 18 = 2·3²; gcd = 6.  Certifies 12x + 18y = 6.
example : (12 : ℤ) * (binaryXgcdInt 12 18).1 + 18 * (binaryXgcdInt 12 18).2 = 6 := by
  rw [binaryXgcdInt_bezout]; decide

-- coprime case: 17x + 5y = 1
example : (17 : ℤ) * (binaryXgcdInt 17 5).1 + 5 * (binaryXgcdInt 17 5).2 = 1 := by
  rw [binaryXgcdInt_bezout]; decide

-- negative arguments are handled by the sign adjustment
example : (-12 : ℤ) * (binaryXgcdInt (-12) 18).1 + 18 * (binaryXgcdInt (-12) 18).2 = 6 := by
  rw [binaryXgcdInt_bezout]; decide

/-! ## Summary

- `binaryXgcd` (ℕ) and `binaryXgcdInt` (ℤ): extended binary GCD returning
  Bézout coefficients computed through Stein's reductions.
- `binaryXgcd_bezout`, `binaryXgcdInt_bezout`: certified `a x + b y = gcd`.
- `binaryXgcdInt_eq_gcdAB`: the produced identity matches Mathlib's
  `Int.gcdA` / `Int.gcdB`.
- Status: **complete and verified**, 0 axioms, 0 sorries. -/

end BinaryGcdOQ02OQ03
