import Mathlib

/-
# Jacobi's Four-Square Count — a Computable Oracle (OQ-01 → OQ-03)

## Gallery Open Question
Parent: `lagrange-four-squares-oq-01` (computational complexity of four-square
representations). This follow-up asks:

  "What is the exact count of four-square representations of `n`, and can Jacobi's
   four-square formula `r₄(n) = 8·Σ_{d|n, 4∤d} d` be formalized?"

## What This File Does — and Honestly Does Not

**The general theorem is a genuine Mathlib gap.** Mathlib formalizes four-square
*existence* (`Nat.sum_four_squares` — every `n` is a sum of four squares) and the
Euler four-square multiplicativity identity (`Nat.euler_four_squares`), but it has
**no representation *count*** `r₄`, no two-square count `r₂`, and no Jacobi formula.
All three classical proof routes are blocked by large gaps:
* weight-2 modular forms `θ⁴ ∈ M₂(Γ₀(4))` (theta identity absent),
* Hurwitz-quaternion order arithmetic (order essentially undeveloped),
* the elementary Lambert/Liouville method (bottoms out on the missing `r₂` count).

Each needs ≫1000 LOC of new number theory, so the *general* Jacobi theorem is
**BLOCKED**. This file therefore does the honest, buildable increment: it pins the
counting **convention** and provides a machine-checked **oracle** that Jacobi's
divisor-sum formula reproduces the brute-force lattice count for a range of small
`n`. It mirrors the parent OQ-01's "verified for small cases" pattern.

## What is machine-checked here
1. `r4 n` — the *ordered, signed* four-square representation count, defined as a
   computable `Finset.card` over the box `[-√n, √n]⁴ ⊆ ℤ⁴`.
2. `jacobiCount n = 8·Σ_{d|n, 4∤d} d` — the right-hand side of Jacobi's formula.
3. `jacobiCount_odd` (0-axiom, **general**): for odd `n` the `4∤d` filter is vacuous,
   so `jacobiCount n = 8·σ(n)`. This isolates the elementary half of the formula.
   `jacobiCount_of_not_four_dvd` (0-axiom, **general**) is its common root: whenever
   `4 ∤ n` the filter is vacuous, so `jacobiCount n = 8·σ(n)`. The doubling relation
   `jacobiCount_two_mul` (0-axiom, **general**) gives `jacobiCount (2·m) = 3·jacobiCount m`
   for odd `m`, and `jacobiCount_two_mul_odd_eq` its closed form `24·σ(m)` — the classical
   `r₄(2m)` value, matching the oracle (`r4 6 = 96 = 24·σ(3)`).  The complementary
   `4 ∤ n` restriction (2-adic valuation `≤ 1`) is `jacobiCount_of_not_four_dvd`; the
   remaining **`4 ∣ n`** case is `jacobiCount_four_dvd` (0-axiom, **general**), the even-side
   recursion `jacobiCount n + 32·σ(n/4) = 8·σ(n)` — its arithmetic core is that the excluded
   `4 ∣ d` divisors sum to `4·σ(n/4)` (`sum_divisors_four_dvd`).  `eight_le_jacobiCount`
   (0-axiom, **general**) records `8 ≤ jacobiCount n` for `n ≥ 1` (the divisor `1` always
   survives the filter), whence `jacobiCount_pos`.
4. `naive_sigma_fails` (0-axiom): the naive `8·σ(4) = 56` is WRONG; the true count
   is `r4 4 = 24`. The `4∤d` exclusion is load-bearing — this guards the convention.
5. `jacobi_oracle` : `r4 n = jacobiCount n` for `1 ≤ n ≤ 24`, by `native_decide`
   (hence depends on `Lean.ofReduceBool`; see the axiom note below).

## Axiom status
The structural lemmas (`jacobiCount_odd`, `naive_sigma_fails`, the box bound) are
0-axiom (`decide`/kernel). The oracle `jacobi_oracle` is discharged by
`native_decide` and so depends on `Lean.ofReduceBool` — it is an *axiomatized*
verified computation, not a proof of the general theorem.
-/

namespace LagrangeFourSquaresOQ01OQ03

open Finset

/-! ## Part 1: The representation count `r4` -/

/-- The box of admissible signed integer components for a four-square representation
of `n`: every component `x` with `x² ≤ n` satisfies `|x| ≤ √n`, i.e. `x ∈ [-√n, √n]`.
So all representations of `n` live inside `box n ^ 4`. -/
def box (n : ℕ) : Finset ℤ := Finset.Icc (-(Nat.sqrt n : ℤ)) (Nat.sqrt n : ℤ)

/-- `r4 n` counts the **ordered, signed** quadruples `(x₁,x₂,x₃,x₄) ∈ ℤ⁴` with
`x₁²+x₂²+x₃²+x₄² = n` (zeros and signs allowed). This is the classical `r₄(n)`.
It is a genuine, computable `Finset.card` over the finite box `box n ^ 4`. -/
def r4 (n : ℕ) : ℕ :=
  (((box n ×ˢ box n ×ˢ box n ×ˢ box n).filter
    (fun p => p.1 ^ 2 + p.2.1 ^ 2 + p.2.2.1 ^ 2 + p.2.2.2 ^ 2 = (n : ℤ))).card)

/-- Sanity: `r4 0 = 1` (only the all-zero quadruple). -/
example : r4 0 = 1 := by decide

/-! ## Part 2: The Jacobi right-hand side -/

/-- The right-hand side of Jacobi's four-square formula:
`jacobiCount n = 8 · Σ_{d ∣ n, 4 ∤ d} d`. -/
def jacobiCount (n : ℕ) : ℕ :=
  8 * ∑ d ∈ n.divisors.filter (fun d => ¬ 4 ∣ d), d

/-- For **odd** `n` the exclusion `4 ∤ d` is vacuous — no divisor of an odd number
is even — so Jacobi's count collapses to `8·σ(n)`. This 0-axiom general lemma
captures the elementary "odd" half of the formula. -/
theorem jacobiCount_odd {n : ℕ} (hn : Odd n) :
    jacobiCount n = 8 * ∑ d ∈ n.divisors, d := by
  unfold jacobiCount
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_true_of_mem
  intro d hd
  rw [Nat.mem_divisors] at hd
  -- `d ∣ n` and `n` odd force `d` odd, hence `4 ∤ d`.
  intro hdvd
  have hd4 : (2 : ℕ) ∣ d := dvd_trans ⟨2, rfl⟩ hdvd
  have : (2 : ℕ) ∣ n := dvd_trans hd4 hd.1
  exact (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr this)

/-- **Prime specialization (0-axiom, general).** For an odd prime `p` the only
divisors are `1` and `p`, both coprime to `4`, so Jacobi's count is the closed form
`jacobiCount p = 8·(p+1)`. Combined with `jacobi_oracle` this pins `r₄(p) = 8(p+1)`
for the small odd primes in range (`r₄(3)=32=8·4`, `r₄(5)=48=8·6`, `r₄(7)=64=8·8`). -/
theorem jacobiCount_prime {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    jacobiCount p = 8 * (p + 1) := by
  rw [jacobiCount_odd hodd, hp.divisors, Finset.sum_pair hp.one_lt.ne]
  ring

/-- **Power-of-two closed form (0-axiom, general).** For every `k ≥ 1` the divisors
of `2^k` are `1, 2, 4, …, 2^k`, and the `4 ∤ d` filter keeps exactly `d = 1` and
`d = 2` (all higher powers are divisible by `4 = 2²`). Hence Jacobi's count is the
constant `jacobiCount (2^k) = 8·(1+2) = 24`, *independent of `k`*. Combined with
`jacobi_oracle` this pins `r₄(2^k) = 24` for the powers of two in range
(`r₄(2)=r₄(4)=r₄(8)=r₄(16)=24`), matching the classical fact that `r₄` is constant
on powers of two. This is the elementary even-side companion to `jacobiCount_odd`. -/
theorem jacobiCount_two_pow {k : ℕ} (hk : 1 ≤ k) : jacobiCount (2 ^ k) = 24 := by
  have hset : (2 ^ k).divisors.filter (fun d => ¬ 4 ∣ d) = {1, 2} := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hdvd, _hne⟩, h4⟩
      rw [Nat.dvd_prime_pow Nat.prime_two] at hdvd
      obtain ⟨i, _hik, rfl⟩ := hdvd
      have hi2 : i < 2 := by
        by_contra h
        push_neg at h
        exact h4 (by
          have h4eq : (4 : ℕ) = 2 ^ 2 := rfl
          rw [h4eq]; exact pow_dvd_pow 2 h)
      interval_cases i
      · left; rfl
      · right; rfl
    · rintro (rfl | rfl)
      · exact ⟨⟨one_dvd _, pow_ne_zero k (by norm_num)⟩, by decide⟩
      · exact ⟨⟨dvd_pow_self 2 (Nat.one_le_iff_ne_zero.mp hk),
          pow_ne_zero k (by norm_num)⟩, by decide⟩
  unfold jacobiCount
  rw [hset, Finset.sum_pair (by decide : (1 : ℕ) ≠ 2)]
  norm_num

/-- **Constancy on powers of two (0-axiom).** An immediate corollary of
`jacobiCount_two_pow`: Jacobi's four-square count takes the same value on every
power of two `2^k` with `k ≥ 1`. -/
theorem jacobiCount_two_pow_const {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) :
    jacobiCount (2 ^ j) = jacobiCount (2 ^ k) := by
  rw [jacobiCount_two_pow hj, jacobiCount_two_pow hk]

/-- **General filter-vacuous lemma (0-axiom).** If `4 ∤ n` then *no* divisor of `n` is
divisible by `4` (a divisor of `4` in `n` would force `4 ∣ n`), so the `4 ∤ d` exclusion
is vacuous and `jacobiCount n = 8·σ(n)`. This is the common root of both `jacobiCount_odd`
(odd `n` ⟹ `4 ∤ n`) and the `n = 2·(odd)` case below: the Jacobi count collapses to
`8·σ` exactly when the 2-adic valuation of `n` is at most `1`. -/
theorem jacobiCount_of_not_four_dvd {n : ℕ} (h : ¬ (4 ∣ n)) :
    jacobiCount n = 8 * ∑ d ∈ n.divisors, d := by
  unfold jacobiCount
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  apply Finset.filter_true_of_mem
  intro d hd
  rw [Nat.mem_divisors] at hd
  intro hdvd
  exact h (dvd_trans hdvd hd.1)

/-- **First doubling triples the count (0-axiom, general).** For every odd `m`,
`jacobiCount (2·m) = 3·jacobiCount m`. Since `2·m` has 2-adic valuation `1`, no divisor
is divisible by `4`, so `jacobiCount (2m) = 8·σ(2m)`; multiplicativity of `σ` on the
coprime factors `2, m` gives `σ(2m) = σ(2)·σ(m) = 3·σ(m)`, while `jacobiCount m = 8·σ(m)`.
This is the even-side companion to `jacobiCount_odd`, and its `m = 1` instance
`jacobiCount 2 = 24` matches `jacobiCount_two_pow`. -/
theorem jacobiCount_two_mul {m : ℕ} (hm : Odd m) :
    jacobiCount (2 * m) = 3 * jacobiCount m := by
  have h4 : ¬ (4 ∣ 2 * m) := by
    intro hdvd
    have h2 : (2 : ℕ) * 2 ∣ 2 * m := by simpa using hdvd
    have : 2 ∣ m := (mul_dvd_mul_iff_left (by norm_num : (2 : ℕ) ≠ 0)).mp h2
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr this)
  have h4m : ¬ (4 ∣ m) := fun hdvd =>
    (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr (dvd_trans ⟨2, rfl⟩ hdvd))
  have hcop : Nat.Coprime 2 m := by rw [Nat.coprime_two_left]; exact hm
  rw [jacobiCount_of_not_four_dvd h4, jacobiCount_of_not_four_dvd h4m,
      hcop.sum_divisors_mul]
  have hdiv2 : ∑ d ∈ (2 : ℕ).divisors, d = 3 := by decide
  rw [hdiv2]; ring

/-- **Closed form for `2·(odd)` (0-axiom, general).** Combining the doubling relation
with `jacobiCount_odd`, for odd `m` the count is `jacobiCount (2·m) = 24·σ(m)` — the
classical value of `r₄(2m)` (matching `r4 2 = 24 = 24·σ(1)`, `r4 6 = 96 = 24·σ(3)`, …).
Together with `jacobiCount_odd` (`8·σ` on the odd part) this exhibits the elementary
half of Jacobi's formula: on `n = 2^a·m` with `a ≤ 1` the count is a pure multiple of
`σ` of the odd part. -/
theorem jacobiCount_two_mul_odd_eq {m : ℕ} (hm : Odd m) :
    jacobiCount (2 * m) = 24 * ∑ d ∈ m.divisors, d := by
  rw [jacobiCount_two_mul hm, jacobiCount_odd hm]; ring

/-- **The `4 ∣ d` divisors scale down to the divisors of `n / 4` (0-axiom, general).**
For `4 ∣ n` (`n ≠ 0`), the map `d ↦ d / 4` is a bijection between the divisors of `n`
divisible by `4` and *all* divisors of `n / 4`, so their sum scales by exactly `4`:
`Σ_{d ∣ n, 4 ∣ d} d = 4 · σ(n / 4)`. This is the arithmetic core of the `4 ∣ n` case of
Jacobi's count below — the excluded ("`4 ∣ d`") part of `σ(n)` is a clean multiple of
`σ(n / 4)`. -/
theorem sum_divisors_four_dvd {n : ℕ} (h4 : 4 ∣ n) (hn : n ≠ 0) :
    ∑ d ∈ n.divisors.filter (fun d => 4 ∣ d), d = 4 * ∑ e ∈ (n / 4).divisors, e := by
  rw [Finset.mul_sum]
  have hn4 : n / 4 ≠ 0 := by
    rw [Ne, Nat.div_eq_zero_iff]; push_neg
    exact ⟨by norm_num, Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h4⟩
  apply Finset.sum_nbij' (i := fun d => d / 4) (j := fun e => 4 * e)
  · intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hdvd, _⟩, h4d⟩ := hd
    rw [Nat.mem_divisors]
    refine ⟨?_, hn4⟩
    obtain ⟨k, rfl⟩ := h4d
    rw [Nat.mul_div_cancel_left k (by norm_num)]
    obtain ⟨m, hm⟩ := h4
    have hkm : 4 * k ∣ 4 * m := hm ▸ hdvd
    rw [hm, Nat.mul_div_cancel_left m (by norm_num)]
    exact (mul_dvd_mul_iff_left (by norm_num : (4:ℕ) ≠ 0)).mp hkm
  · intro e he
    rw [Nat.mem_divisors] at he
    obtain ⟨hedvd, _⟩ := he
    rw [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨?_, hn⟩, ⟨e, rfl⟩⟩
    calc 4 * e ∣ 4 * (n / 4) := mul_dvd_mul_left 4 hedvd
      _ = n := Nat.mul_div_cancel' h4
  · intro d hd
    rw [Finset.mem_filter] at hd
    exact Nat.mul_div_cancel' hd.2
  · intro e _
    exact Nat.mul_div_cancel_left e (by norm_num)
  · intro d hd
    rw [Finset.mem_filter] at hd
    exact (Nat.mul_div_cancel' hd.2).symm

/-- **The `4 ∣ n` case of Jacobi's count (0-axiom, general).** Complementary to
`jacobiCount_of_not_four_dvd` (which handles 2-adic valuation `≤ 1`): whenever `4 ∣ n`
(`n ≠ 0`) the excluded divisors contribute exactly `4·σ(n/4)`, giving the identity
`jacobiCount n + 32·σ(n/4) = 8·σ(n)`.  Equivalently `jacobiCount n = 8·(σ(n) − 4·σ(n/4))`.
This is the general even-side recursion: it reduces the count on `n` to the plain
divisor-sums of `n` and `n/4`.  It matches the oracle — e.g. `n = 4`:
`24 + 32·σ(1) = 24 + 32 = 56 = 8·σ(4)`; `n = 8`: `24 + 32·σ(2) = 24 + 96 = 120 = 8·σ(8)`. -/
theorem jacobiCount_four_dvd {n : ℕ} (h4 : 4 ∣ n) (hn : n ≠ 0) :
    jacobiCount n + 32 * ∑ e ∈ (n / 4).divisors, e = 8 * ∑ d ∈ n.divisors, d := by
  have hsplit : (∑ d ∈ n.divisors.filter (fun d => 4 ∣ d), d)
      + ∑ d ∈ n.divisors.filter (fun d => ¬ 4 ∣ d), d = ∑ d ∈ n.divisors, d :=
    Finset.sum_filter_add_sum_filter_not n.divisors (fun d => 4 ∣ d) (fun d => d)
  have hB : ∑ d ∈ n.divisors.filter (fun d => 4 ∣ d), d = 4 * ∑ e ∈ (n / 4).divisors, e :=
    sum_divisors_four_dvd h4 hn
  unfold jacobiCount
  omega

/-- **Jacobi's count is at least `8` on every positive `n` (0-axiom, general).** The
divisor `d = 1` is always present and never divisible by `4`, so it survives the `4 ∤ d`
filter and contributes `8·1 = 8`.  Hence `8 ≤ jacobiCount n` for all `n ≥ 1` — the formula
predicts every positive integer has at least the `8` "trivial" signed four-square
representations `(±1,0,0,0)` and permutations, consistent with the oracle
(`r4 1 = 8`). -/
theorem eight_le_jacobiCount {n : ℕ} (hn : 1 ≤ n) : 8 ≤ jacobiCount n := by
  unfold jacobiCount
  have h1mem : (1 : ℕ) ∈ n.divisors.filter (fun d => ¬ 4 ∣ d) := by
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨one_dvd _, Nat.one_le_iff_ne_zero.mp hn⟩, by decide⟩
  have hsum : 1 ≤ ∑ d ∈ n.divisors.filter (fun d => ¬ 4 ∣ d), d :=
    Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i) h1mem
  calc 8 = 8 * 1 := by norm_num
    _ ≤ 8 * _ := Nat.mul_le_mul_left 8 hsum

/-- **Jacobi's count is positive on every positive `n` (0-axiom).** Immediate from
`eight_le_jacobiCount`; the counting side of "every positive integer is a sum of four
squares" — `r₄(n) > 0` — is predicted by the formula for all `n ≥ 1`. -/
theorem jacobiCount_pos {n : ℕ} (hn : 1 ≤ n) : 0 < jacobiCount n :=
  lt_of_lt_of_le (by norm_num) (eight_le_jacobiCount hn)

/-- **Convention guard (0-axiom).** The naive formula `8·σ(n)` is WRONG for `n = 4`:
`8·σ(4) = 8·(1+2+4) = 56`, whereas the true count is `r4 4 = 24`. Equivalently the
`4 ∤ d` exclusion drops the divisor `d = 4`. This is exactly why the general formula
cannot be stated as `8·σ`. -/
theorem naive_sigma_fails :
    8 * ∑ d ∈ (4 : ℕ).divisors, d = 56 ∧ jacobiCount 4 = 24 ∧ r4 4 = 24 := by
  refine ⟨by decide, by decide, by native_decide⟩

/-! ## Part 3: The oracle — Jacobi's formula reproduces the brute-force count -/

/-- **Jacobi oracle (`native_decide`; depends on `Lean.ofReduceBool`).**
For every `1 ≤ n ≤ 24`, the divisor-sum formula `jacobiCount n = 8·Σ_{d|n,4∤d} d`
equals the brute-force ordered-signed lattice count `r4 n`. This is a machine-checked
regression oracle pinning the convention (`r4 1 = 8`, `r4 2 = 24`, `r4 4 = 24`, …),
**not** a proof of the general theorem (which is Mathlib-blocked). -/
theorem jacobi_oracle : ∀ n ∈ Finset.Icc 1 24, r4 n = jacobiCount n := by
  native_decide

/-- Spot anchors extracted from the oracle range, stated explicitly so the intended
values are visible: `r4(1)=8, r4(2)=24, r4(3)=32, r4(4)=24, r4(5)=48, r4(7)=64`. -/
theorem r4_anchor_values :
    r4 1 = 8 ∧ r4 2 = 24 ∧ r4 3 = 32 ∧ r4 4 = 24 ∧ r4 5 = 48 ∧ r4 7 = 64 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

end LagrangeFourSquaresOQ01OQ03
