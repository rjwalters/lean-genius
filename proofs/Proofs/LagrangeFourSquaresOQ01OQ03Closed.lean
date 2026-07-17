import Mathlib
import Proofs.LagrangeFourSquaresOQ01OQ03Even

/-
# Jacobi four-square RHS: the multiplicative even closed form  (OQ-01 → OQ-03, continued)

`LagrangeFourSquaresOQ01OQ03Even.lean` pins the Jacobi right-hand side
`jacobiCount n = 8·Σ_{d|n, 4∤d} d` on every `n` from ordinary divisor sums, but on
the `4 ∣ n` locus it only records the **recursive/subtractive** form
`jacobiCount n = 8·σ(n) − 32·σ(n/4)`.  This file upgrades that to the textbook
**multiplicative closed form**: for every *even* `n = 2^a·m` with `m` odd and `a ≥ 1`,

  `jacobiCount (2^a · m) = 24 · σ(m)`   (with `σ = ∑_{d ∣ ·} d`).

So the Jacobi RHS on the even part is the single universal constant `24` times the
divisor sum of the odd part — independent of the power of two.  Combined with the
odd collapse `jacobiCount n = 8·σ(n)` (`4 ∤ n`) this is the standard closed form of
Jacobi's four-square theorem's right side, e.g. `r₄(n) = 24·σ(odd part of n)` for
`n` even, `= 8·σ(n)` for `n` odd — here proved for the RHS `jacobiCount`, which is
the elementary half that is *not* Mathlib-blocked (the `r₄ = jacobiCount` equality
still needs Hurwitz quaternions / weight-2 modular forms).

The crux is `sum_divisors_two_pow_mul_odd`: `σ(2^a · m) = (2^{a+1} − 1)·σ(m)` for odd
`m`, from `Nat.Coprime.sum_divisors_mul` (divisor-sum is multiplicative on coprime
factors), `Nat.sum_divisors_prime_pow`, and the geometric sum `Σ_{i<a+1} 2^i =
2^{a+1} − 1`.  Feeding it through the odd branch (`a = 1`) and the `4 ∣ n` recurrence
`jacobiCount_four_dvd_add` (`a ≥ 2`) collapses both to `24·σ(m)`.

Axiom-free (`propext`/`Classical.choice`/`Quot.sound` only): no `native_decide`, no
`sorry`, no `axiom`.
-/

namespace LagrangeFourSquaresOQ01OQ03Closed

open Finset LagrangeFourSquaresOQ01OQ03Even

/-- **Divisor sum of `2^a · m` for odd `m`.**  Since `2^a` and an odd `m` are
coprime, the divisor-sum function is multiplicative, and `σ(2^a) = 2^{a+1} − 1` by
the geometric series, giving `σ(2^a · m) = (2^{a+1} − 1)·σ(m)`. -/
theorem sum_divisors_two_pow_mul_odd (a : ℕ) {m : ℕ} (hm : Odd m) :
    ∑ d ∈ (2 ^ a * m).divisors, d = (2 ^ (a + 1) - 1) * ∑ d ∈ m.divisors, d := by
  have hcop : Nat.Coprime (2 ^ a) m := (Nat.coprime_two_left.mpr hm).pow_left a
  rw [hcop.sum_divisors_mul]
  congr 1
  -- σ(2^a) = ∑_{i < a+1} 2^i = 2^{a+1} − 1
  rw [Nat.sum_divisors_prime_pow Nat.prime_two, Nat.geomSum_eq (le_refl 2) (a + 1)]
  simp

/-- **Multiplicative even closed form of the Jacobi RHS.**  For odd `m` and `a ≥ 1`,
`jacobiCount (2^a · m) = 24 · σ(m)` — the power of two drops out entirely, leaving
the universal factor `24` times the divisor sum of the odd part.

`a = 1` (`n ≡ 2 mod 4`): `4 ∤ 2m`, so `jacobiCount = 8·σ(2m) = 8·3·σ(m) = 24σ(m)`.
`a ≥ 2` (`4 ∣ n`): the recurrence `jacobiCount n + 32·σ(n/4) = 8·σ(n)` with
`σ(2^a m) = (2^{a+1}−1)σ(m)` and `σ(2^{a−2} m) = (2^{a−1}−1)σ(m)` telescopes the
powers of two to `24·σ(m)`. -/
theorem jacobiCount_two_pow_mul_odd {a m : ℕ} (ha : 1 ≤ a) (hm : Odd m) :
    jacobiCount (2 ^ a * m) = 24 * ∑ d ∈ m.divisors, d := by
  rcases a with _ | _ | b
  · omega
  · -- a = 1: n = 2·m, and 4 ∤ 2m since m is odd
    have hnot4 : ¬ (4 : ℕ) ∣ 2 ^ 1 * m := by
      intro h
      rw [pow_one, show (4 : ℕ) = 2 * 2 from rfl,
        Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)] at h
      rw [Nat.odd_iff] at hm
      omega
    rw [jacobiCount_of_not_four_dvd hnot4, sum_divisors_two_pow_mul_odd 1 hm]
    ring
  · -- a = b + 2 ≥ 2: 4 ∣ n = 2^(b+2)·m
    have hfact : (2 : ℕ) ^ (b + 2) * m = 4 * (2 ^ b * m) := by ring
    have h4 : (4 : ℕ) ∣ 2 ^ (b + 2) * m := ⟨2 ^ b * m, hfact⟩
    have hquot : (2 ^ (b + 2) * m) / 4 = 2 ^ b * m := by
      rw [hfact, Nat.mul_div_cancel_left _ (by norm_num : 0 < 4)]
    have hadd := jacobiCount_four_dvd_add h4
    rw [hquot, sum_divisors_two_pow_mul_odd b hm,
        sum_divisors_two_pow_mul_odd (b + 2) hm] at hadd
    -- fold the power of two into an atom `x = 2^b` (x ≥ 1)
    have hx : (1 : ℕ) ≤ 2 ^ b := Nat.one_le_two_pow
    set x := 2 ^ b with hxdef
    have e1 : (2 : ℕ) ^ (b + 1) = 2 * x := by rw [hxdef]; ring
    have e3 : (2 : ℕ) ^ (b + 2 + 1) = 8 * x := by rw [hxdef]; ring
    rw [e1, e3] at hadd
    -- hadd : jc + 32·((2x−1)·σ) = 8·((8x−1)·σ),  σ = ∑ d ∈ m.divisors, d
    have hclaim : 8 * ((8 * x - 1) * ∑ d ∈ m.divisors, d)
        = 32 * ((2 * x - 1) * ∑ d ∈ m.divisors, d) + 24 * ∑ d ∈ m.divisors, d := by
      have hlin : 8 * (8 * x - 1) = 32 * (2 * x - 1) + 24 := by omega
      calc 8 * ((8 * x - 1) * ∑ d ∈ m.divisors, d)
            = (8 * (8 * x - 1)) * ∑ d ∈ m.divisors, d := by ring
        _ = (32 * (2 * x - 1) + 24) * ∑ d ∈ m.divisors, d := by rw [hlin]
        _ = 32 * ((2 * x - 1) * ∑ d ∈ m.divisors, d) + 24 * ∑ d ∈ m.divisors, d := by ring
    rw [hclaim] at hadd
    -- hadd : jc + K = K + 24·σ  with K = 32·((2x−1)·σ); cancel K
    rw [add_comm (32 * ((2 * x - 1) * ∑ d ∈ m.divisors, d))
        (24 * ∑ d ∈ m.divisors, d)] at hadd
    exact Nat.add_right_cancel hadd

/-- **Even closed form via the odd part.**  For every even `n ≠ 0`,
`jacobiCount n = 24 · σ(oddPart n)`, where `oddPart n = ordCompl[2] n = n / 2^{v₂(n)}`.
Packages `jacobiCount_two_pow_mul_odd` against the canonical `2`-adic factorization
`n = 2^{v₂(n)} · oddPart n`, so no explicit `(a, m)` decomposition is needed at the
call site. -/
theorem jacobiCount_even_ordCompl {n : ℕ} (hn : n ≠ 0) (h2 : 2 ∣ n) :
    jacobiCount n = 24 * ∑ d ∈ (ordCompl[2] n).divisors, d := by
  have ha : 1 ≤ n.factorization 2 :=
    Nat.Prime.factorization_pos_of_dvd Nat.prime_two hn h2
  have hodd : Odd (ordCompl[2] n) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp (Nat.not_dvd_ordCompl Nat.prime_two hn))
  have key := jacobiCount_two_pow_mul_odd ha hodd
  rwa [Nat.ordProj_mul_ordCompl_eq_self n 2] at key

/-- **Even-side doubling law: doubling an even number leaves the Jacobi count unchanged.**
For every even `n ≠ 0`, `jacobiCount (2·n) = jacobiCount n`.  This is the even-`n`
companion of `jacobiCount_two_mul` (odd `n` ⟹ the count *triples*): once the `2`-adic
valuation is `≥ 1`, the count is `24·σ(oddPart n)`, which is unchanged by another factor of
`2` (`oddPart (2n) = oddPart n`).  So along the chain `m, 2m, 4m, 8m, …` (`m` odd) the count
jumps once — `8σ(m) → 24σ(m)` at the first doubling — and is then constant.  Proof:
`jacobiCount_even_ordCompl` on both sides, with `ordCompl[2] (2n) = ordCompl[2] n` from
`Nat.ordCompl_mul` and `ordCompl[2] 2 = 1`. -/
theorem jacobiCount_two_mul_of_even {n : ℕ} (hn : n ≠ 0) (h2 : 2 ∣ n) :
    jacobiCount (2 * n) = jacobiCount n := by
  have h2n : 2 * n ≠ 0 := Nat.mul_ne_zero (by norm_num) hn
  have h2dvd : 2 ∣ 2 * n := Dvd.intro n rfl
  have h22 : ordCompl[2] 2 = 1 := by
    rw [Nat.Prime.factorization_self Nat.prime_two, pow_one, Nat.div_self (by norm_num)]
  have hoc : ordCompl[2] (2 * n) = ordCompl[2] n := by
    rw [Nat.ordCompl_mul, h22, one_mul]
  rw [jacobiCount_even_ordCompl h2n h2dvd, jacobiCount_even_ordCompl hn h2, hoc]

/-- **The even closed form is independent of the power of two (`a ≥ 1`).** For odd `m` and
any `a, b ≥ 1`, `jacobiCount (2^a · m) = jacobiCount (2^b · m)` — both equal `24·σ(m)`.
This generalizes `jacobiCount_two_pow_const` (the `m = 1` case) from the pure powers of two
to an arbitrary odd part: the Jacobi count sees only whether `v₂ ≥ 1`, not its exact value. -/
theorem jacobiCount_two_pow_mul_odd_const {a b m : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hm : Odd m) : jacobiCount (2 ^ a * m) = jacobiCount (2 ^ b * m) := by
  rw [jacobiCount_two_pow_mul_odd ha hm, jacobiCount_two_pow_mul_odd hb hm]

/-! ## Multiplicativity of the Jacobi RHS as an arithmetic function

Jacobi's four-square count is *not* multiplicative on the nose (there is a fixed
factor of `8`), but the normalized function `r₄/8 = Σ_{d|n, 4∤d} d` **is** a
multiplicative arithmetic function.  This is the structural heart of Jacobi's
formula and the property none of the closed-form lemmas above records: it says the
whole count is determined by its values on prime powers.  The proof is a clean
consequence of the elementary closed forms — the odd collapse `jacobiCount n = 8σ(n)`
(`4 ∤ n`) and the even form `jacobiCount n = 24σ(oddPart n)` — together with
multiplicativity of `σ` (`Nat.Coprime.sum_divisors_mul`).  Coprimality forces at most
one of the two arguments to be even, so a parity split reduces every case to
`σ`-multiplicativity. -/

/-- Odd numbers are their own `2`-odd part: `ordCompl[2] n = n` when `n` is odd (its
`2`-adic valuation vanishes). -/
private theorem ordCompl_two_of_odd {n : ℕ} (hn : Odd n) : ordCompl[2] n = n := by
  have h2 : ¬ (2 : ℕ) ∣ n := fun hdvd =>
    (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr hdvd)
  rw [Nat.factorization_eq_zero_of_not_dvd h2]
  simp

/-- No odd number is divisible by `4`. -/
private theorem not_four_dvd_of_odd {n : ℕ} (hn : Odd n) : ¬ (4 : ℕ) ∣ n := fun hdvd =>
  (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr (dvd_trans ⟨2, rfl⟩ hdvd))

/-- Multiplicativity, the asymmetric `m` even / `n` odd branch.  On this branch the
even closed form `jacobiCount m = 24·σ(oddPart m)` and the odd collapse
`jacobiCount n = 8·σ(n)` combine — using `ordCompl[2] (m·n) = ordCompl[2] m · n`
(as `n` is odd) and multiplicativity of `σ` on the coprime factors — into
`jacobiCount (m·n) = 24·σ(oddPart m)·σ(n)`, whence the `8·` relation. -/
private theorem jacobiCount_mul_coprime_even_left {m n : ℕ}
    (hm0 : m ≠ 0) (hn0 : n ≠ 0) (h : Nat.Coprime m n) (hme : 2 ∣ m) (hno : Odd n) :
    8 * jacobiCount (m * n) = jacobiCount m * jacobiCount n := by
  have hjn : jacobiCount n = 8 * ∑ d ∈ n.divisors, d :=
    jacobiCount_of_not_four_dvd (not_four_dvd_of_odd hno)
  have hjm : jacobiCount m = 24 * ∑ d ∈ (ordCompl[2] m).divisors, d :=
    jacobiCount_even_ordCompl hm0 hme
  have hmn0 : m * n ≠ 0 := Nat.mul_ne_zero hm0 hn0
  have h2mn : 2 ∣ m * n := hme.mul_right n
  have hjmn : jacobiCount (m * n) = 24 * ∑ d ∈ (ordCompl[2] (m * n)).divisors, d :=
    jacobiCount_even_ordCompl hmn0 h2mn
  have hoc : ordCompl[2] (m * n) = ordCompl[2] m * n := by
    rw [Nat.ordCompl_mul, ordCompl_two_of_odd hno]
  have hcop : Nat.Coprime (ordCompl[2] m) n := h.coprime_dvd_left (Nat.ordCompl_dvd m 2)
  rw [hjmn, hoc, hcop.sum_divisors_mul, hjm, hjn]
  ring

/-- **Multiplicativity of the Jacobi four-square RHS.**  For coprime positive `m, n`,
`8 · jacobiCount (m·n) = jacobiCount m · jacobiCount n`.  Equivalently the normalized
count `r₄/8 = Σ_{d|n, 4∤d} d` is a multiplicative arithmetic function — the structural
feature that distinguishes Jacobi's formula and pins the count from its prime-power
values.  Coprimality forces at most one argument even; the three parity branches each
reduce to `σ`-multiplicativity via the odd (`8σ`) and even (`24σ(oddpart)`) closed
forms.  Axiom-free (`propext`/`Classical.choice`/`Quot.sound`). -/
theorem jacobiCount_mul_coprime {m n : ℕ} (hm0 : m ≠ 0) (hn0 : n ≠ 0)
    (h : Nat.Coprime m n) :
    8 * jacobiCount (m * n) = jacobiCount m * jacobiCount n := by
  rcases Nat.even_or_odd m with hme | hmo
  · -- `m` even ⟹ `n` odd, else `2 ∣ gcd m n = 1`
    have hno : Odd n := by
      rcases Nat.even_or_odd n with hne | hno
      · exfalso
        have hgcd : Nat.gcd m n = 1 := h
        have h2 : (2 : ℕ) ∣ 1 :=
          hgcd ▸ Nat.dvd_gcd (even_iff_two_dvd.mp hme) (even_iff_two_dvd.mp hne)
        exact absurd h2 (by decide)
      · exact hno
    exact jacobiCount_mul_coprime_even_left hm0 hn0 h (even_iff_two_dvd.mp hme) hno
  · rcases Nat.even_or_odd n with hne | hno
    · -- `m` odd, `n` even: reduce to the even-left branch by swapping the factors
      have hswap := jacobiCount_mul_coprime_even_left hn0 hm0 h.symm
        (even_iff_two_dvd.mp hne) hmo
      rw [Nat.mul_comm n m] at hswap
      rw [hswap]; exact Nat.mul_comm _ _
    · -- both odd: the `4 ∤ d` filter is vacuous everywhere, so `σ`-multiplicativity closes it
      rw [jacobiCount_of_not_four_dvd (not_four_dvd_of_odd (hmo.mul hno)),
          jacobiCount_of_not_four_dvd (not_four_dvd_of_odd hmo),
          jacobiCount_of_not_four_dvd (not_four_dvd_of_odd hno), h.sum_divisors_mul]
      ring

/-- **The Jacobi normalized count `Σ_{d|n, 4∤d} d` is multiplicative.**  The `8`-free
restatement of `jacobiCount_mul_coprime`: for coprime positive `m, n` the filtered
divisor sum is multiplicative as an arithmetic function.  This is exactly the sense in
which `r₄` "factors" over coprime parts. -/
theorem filter_four_sum_mul_coprime {m n : ℕ} (hm0 : m ≠ 0) (hn0 : n ≠ 0)
    (h : Nat.Coprime m n) :
    ∑ d ∈ (m * n).divisors.filter (fun d => ¬ 4 ∣ d), d
      = (∑ d ∈ m.divisors.filter (fun d => ¬ 4 ∣ d), d)
        * (∑ d ∈ n.divisors.filter (fun d => ¬ 4 ∣ d), d) := by
  have hkey := jacobiCount_mul_coprime hm0 hn0 h
  unfold jacobiCount at hkey
  set A := ∑ d ∈ (m * n).divisors.filter (fun d => ¬ 4 ∣ d), d with hA
  set B := ∑ d ∈ m.divisors.filter (fun d => ¬ 4 ∣ d), d with hB
  set C := ∑ d ∈ n.divisors.filter (fun d => ¬ 4 ∣ d), d with hC
  -- hkey : 8 * (8 * A) = (8 * B) * (8 * C)
  have hrw : (8 * B) * (8 * C) = 8 * (8 * (B * C)) := by ring
  rw [hrw] at hkey
  have h1 : 8 * A = 8 * (B * C) := Nat.eq_of_mul_eq_mul_left (by norm_num) hkey
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h1

/-- Sanity check at `n = 4 = 2² · 1`: `jacobiCount 4 = 24 · σ(1) = 24`. -/
example : jacobiCount (2 ^ 2 * 1) = 24 := by
  rw [jacobiCount_two_pow_mul_odd (by norm_num) (by norm_num)]; decide

/-- Sanity check at `n = 12 = 2² · 3`: `jacobiCount 12 = 24 · σ(3) = 24 · 4 = 96`. -/
example : jacobiCount 12 = 96 := by
  have : (12 : ℕ) = 2 ^ 2 * 3 := by norm_num
  rw [this, jacobiCount_two_pow_mul_odd (by norm_num) (by norm_num)]; decide

/-- Sanity check of multiplicativity, both-odd: `8·jacobiCount 15 = jacobiCount 3 · jacobiCount 5`
(`8·192 = 32·48`). Kernel `decide`, no `ofReduceBool`. -/
example : 8 * jacobiCount 15 = jacobiCount 3 * jacobiCount 5 := by decide

/-- Sanity check of multiplicativity, mixed parity: `8·jacobiCount 6 = jacobiCount 2 · jacobiCount 3`
(`8·96 = 24·32`). Kernel `decide`, no `ofReduceBool`. -/
example : 8 * jacobiCount 6 = jacobiCount 2 * jacobiCount 3 := by decide

end LagrangeFourSquaresOQ01OQ03Closed
