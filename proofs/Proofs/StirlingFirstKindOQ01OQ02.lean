/-
Stirling Numbers of the First Kind: the SIGNED generating identity
    ∑ₖ (−1)ⁿ⁻ᵏ c(n,k) · xᵏ = x · (x−1) · (x−2) · … · (x−n+1)   (the falling factorial)
and the alternating row sum
    ∑ₖ (−1)ⁿ⁻ᵏ c(n,k) = [n ≤ 1].

Source: Open question stirling-first-kind-oq-01-oq-02
Status: VERIFIED (0 axioms, 0 sorries)

`Nat.stirlingFirst n k` is the unsigned Stirling number of the first kind: the
number of permutations of an `n`-element set with exactly `k` disjoint cycles.
The *signed* Stirling numbers of the first kind are `s(n,k) = (−1)ⁿ⁻ᵏ c(n,k)`, and
classically they are the connection coefficients expressing the **falling
factorial** in the monomial basis:

    x⁽ⁿ⁾_↓ = x (x−1) (x−2) ⋯ (x − n + 1) = ∑_{k=0}^{n} (−1)ⁿ⁻ᵏ c(n,k) · xᵏ
            = (descPochhammer R n).eval x.

Mathlib carries the rising-factorial polynomial `ascPochhammer` and the falling
one `descPochhammer`, together with the recurrence/edge data for the *unsigned*
`Nat.stirlingFirst`, but it has **no signed Stirling numbers** and records neither
the monomial expansion of the falling factorial in terms of `Nat.stirlingFirst`
nor the resulting alternating row identity. We fill that gap.

The parent file `StirlingFirstKindOQ01.lean` proves the row sum
`∑ₖ c(n,k) = n!`, and its companion (the *unsigned* generating identity
`∑ₖ c(n,k) xᵏ = x(x+1)…(x+n−1)`) handles the rising factorial. The present file
is the signed/falling-factorial counterpart, and it answers the parent's stated
open question

    "Can the signed row identity ∑ₖ (−1)ⁿ⁻ᵏ c(n,k) = [n = 1] (the alternating
     sum vanishing for n ≥ 2) be formalized from the same recurrence?"

**Method.** The signed identity is obtained from the (unsigned) rising-factorial
generating identity by the substitution `x ↦ −x` together with the parity bridge
`(−1)ⁿ⁻ᵏ = (−1)ⁿ·(−1)ᵏ` (valid for `k ≤ n`): the alternating signs reflect the
`x` to `−x` flip exactly, turning `∏(x+i)` into `∏(x−i)`. The alternating row sum
is then the `x = 1` specialization, where the falling factorial `(1)⁽ⁿ⁾_↓` carries
the factor `(1 − 1) = 0` for every `n ≥ 2`, forcing the sum to vanish.

We prove:
1. `stirlingFirst_generating` — the *unsigned* rising-factorial identity (foundation)
2. `eval_descPochhammer_eq_prod` — `(descPochhammer R n).eval x = ∏ (x − i)`
3. `stirlingFirst_generating_signed` — the signed/falling-factorial identity
4. `stirlingFirst_generating_signed_descPochhammer` — the same, via `descPochhammer`
5. `stirlingFirst_alternating_row_sum` — `∑ₖ (−1)ⁿ⁻ᵏ c(n,k) = [n ≤ 1]`

References:
- Graham, Knuth, Patashnik, *Concrete Mathematics* §6.1 (eqs. 6.10, 6.13)
- StirlingFirstKindOQ01.lean (parent: the `x = 1` row sum and this open question)
-/
import Mathlib

open Nat Finset Polynomial

namespace StirlingFirstKindSigned

/-- The leftmost column vanishes after multiplication by the row index:
`(n : R) · c(n, 0) = 0` for every `n`. For `n = 0` the prefactor `n` kills it; for
`n ≥ 1`, the Stirling number `c(n, 0) = 0` itself. This makes the generating
recursion collapse cleanly to the rising-factorial recursion. -/
theorem natCast_mul_stirlingFirst_zero_left {R : Type*} [Semiring R] (n : ℕ) :
    (n : R) * (Nat.stirlingFirst n 0 : R) = 0 := by
  cases n with
  | zero => simp
  | succ m => simp [Nat.stirlingFirst_succ_zero]

/-- **Unsigned generating identity** (foundation). For every commutative semiring
`R` and `x : R`,

    ∑_{k=0}^{n} c(n, k) · xᵏ = ∏_{i=0}^{n-1} (x + i),

the right-hand side being the rising factorial. The unsigned Stirling numbers of
the first kind are the coefficients expressing the rising factorial in the
monomial basis. Proof by induction on `n` using the recurrence
`c(n+1,k+1) = n·c(n,k+1) + c(n,k)` and an index shift. -/
theorem stirlingFirst_generating {R : Type*} [CommSemiring R] (x : R) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n k : R) * x ^ k
      = ∏ i ∈ Finset.range n, (x + (i : R)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.prod_range_succ]
      rw [Finset.sum_range_succ' (fun k => (Nat.stirlingFirst (n + 1) k : R) * x ^ k) (n + 1),
        Nat.stirlingFirst_succ_zero]
      simp only [Nat.cast_zero, pow_zero, mul_one, add_zero]
      have hrec : ∀ k ∈ Finset.range (n + 1),
          (Nat.stirlingFirst (n + 1) (k + 1) : R) * x ^ (k + 1)
            = (n : R) * ((Nat.stirlingFirst n (k + 1) : R) * x ^ (k + 1))
              + (Nat.stirlingFirst n k : R) * x ^ (k + 1) := by
        intro k _
        rw [Nat.stirlingFirst_succ_succ]
        push_cast
        ring
      rw [Finset.sum_congr rfl hrec, Finset.sum_add_distrib, ← Finset.mul_sum, ← ih]
      have hS2 : (∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n k : R) * x ^ (k + 1))
          = (∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n k : R) * x ^ k) * x := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      have hS1 : (∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n (k + 1) : R) * x ^ (k + 1))
          = ∑ k ∈ Finset.range n, (Nat.stirlingFirst n (k + 1) : R) * x ^ (k + 1) := by
        rw [Finset.sum_range_succ, Nat.stirlingFirst_eq_zero_of_lt (Nat.lt_succ_self n)]
        simp
      have hfull : (∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n k : R) * x ^ k)
          = (∑ k ∈ Finset.range n, (Nat.stirlingFirst n (k + 1) : R) * x ^ (k + 1))
            + (Nat.stirlingFirst n 0 : R) := by
        rw [Finset.sum_range_succ' (fun k => (Nat.stirlingFirst n k : R) * x ^ k) n]
        simp
      have hnS1 : (n : R) * (∑ k ∈ Finset.range (n + 1),
            (Nat.stirlingFirst n (k + 1) : R) * x ^ (k + 1))
          = (n : R) * (∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n k : R) * x ^ k) := by
        rw [hS1, hfull, mul_add, natCast_mul_stirlingFirst_zero_left, add_zero]
      rw [hnS1, hS2]
      ring

/-- The falling-factorial polynomial `descPochhammer R n` evaluates to the explicit
product `∏_{i<n} (x − i)`. (Mathlib records `descPochhammer` but not this evaluated
product form directly.) -/
theorem eval_descPochhammer_eq_prod {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    (descPochhammer R n).eval x = ∏ i ∈ Finset.range n, (x - (i : R)) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [descPochhammer_succ_right, eval_mul, ih, Finset.prod_range_succ, eval_sub, eval_X,
        eval_natCast]

/-- **Signed generating identity for the Stirling numbers of the first kind.**
For every commutative ring `R` and `x : R`,

    ∑_{k=0}^{n} (−1)ⁿ⁻ᵏ c(n, k) · xᵏ = ∏_{i=0}^{n-1} (x − i),

the right-hand side being the falling factorial `x⁽ⁿ⁾_↓ = x(x−1)…(x−n+1)`. The
*signed* Stirling numbers `s(n,k) = (−1)ⁿ⁻ᵏ c(n,k)` are thus the coefficients
expressing the falling factorial in the monomial basis. Obtained from the unsigned
rising-factorial identity `stirlingFirst_generating` by `x ↦ −x` and the parity
bridge `(−1)ⁿ⁻ᵏ = (−1)ⁿ(−1)ᵏ`. -/
theorem stirlingFirst_generating_signed {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : R) ^ (n - k) * (Nat.stirlingFirst n k : R) * x ^ k
      = ∏ i ∈ Finset.range n, (x - (i : R)) := by
  -- Rewrite each signed term as `(−1)ⁿ · (c(n,k) · (−x)ᵏ)`.
  have key : ∑ k ∈ Finset.range (n + 1),
        (-1 : R) ^ (n - k) * (Nat.stirlingFirst n k : R) * x ^ k
      = (-1 : R) ^ n * ∑ k ∈ Finset.range (n + 1), (Nat.stirlingFirst n k : R) * (-x) ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Finset.mem_range] at hk
    have hkn : k ≤ n := by omega
    -- parity bridge: (−1)^(n−k) = (−1)^n · (−1)^k
    have hsq : ((-1 : R) ^ k) * ((-1 : R) ^ k) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    have hcomb : ((-1 : R)) ^ (n - k) * (-1 : R) ^ k = (-1 : R) ^ n := by
      rw [← pow_add, Nat.sub_add_cancel hkn]
    have e1 : ((-1 : R)) ^ (n - k) = (-1 : R) ^ n * (-1 : R) ^ k := by
      calc ((-1 : R)) ^ (n - k)
          = ((-1 : R)) ^ (n - k) * (((-1 : R) ^ k) * ((-1 : R) ^ k)) := by rw [hsq, mul_one]
        _ = (((-1 : R)) ^ (n - k) * (-1 : R) ^ k) * (-1 : R) ^ k := by ring
        _ = (-1 : R) ^ n * (-1 : R) ^ k := by rw [hcomb]
    rw [e1, neg_pow]
    ring
  rw [key, stirlingFirst_generating]
  -- ∏(−x + i) = (−1)ⁿ · ∏(x − i); cancel the leading (−1)ⁿ.
  have hp : ∏ i ∈ Finset.range n, (-x + (i : R)) = (-1 : R) ^ n * ∏ i ∈ Finset.range n, (x - (i : R)) := by
    have hfac : ∀ i ∈ Finset.range n, (-x + (i : R)) = (-1 : R) * (x - (i : R)) :=
      fun i _ => by ring
    rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  rw [hp, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- The signed generating identity phrased with Mathlib's falling-factorial
polynomial: `∑ₖ (−1)ⁿ⁻ᵏ c(n,k) xᵏ = (descPochhammer R n).eval x`. -/
theorem stirlingFirst_generating_signed_descPochhammer {R : Type*} [CommRing R] (x : R) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : R) ^ (n - k) * (Nat.stirlingFirst n k : R) * x ^ k
      = (descPochhammer R n).eval x := by
  rw [stirlingFirst_generating_signed, eval_descPochhammer_eq_prod]

/-- **Alternating row sum of the unsigned Stirling numbers of the first kind:**

    ∑_{k=0}^{n} (−1)ⁿ⁻ᵏ c(n, k) = [n ≤ 1]   (i.e. `1` for `n ∈ {0,1}`, else `0`).

This is the `x = 1` specialization of the signed generating identity: the falling
factorial `(1)⁽ⁿ⁾_↓ = 1·0·(−1)⋯` carries the factor `(1 − 1) = 0` for every
`n ≥ 2`, so the alternating sum vanishes there, exactly answering the parent's
open question. -/
theorem stirlingFirst_alternating_row_sum (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ (n - k) * (Nat.stirlingFirst n k : ℤ)
      = if n ≤ 1 then 1 else 0 := by
  have h := stirlingFirst_generating_signed (1 : ℤ) n
  simp only [one_pow, mul_one] at h
  rw [h]
  match n with
  | 0 => simp
  | 1 => simp
  | (m + 2) =>
      rw [if_neg (by omega)]
      refine Finset.prod_eq_zero (i := 1) (Finset.mem_range.mpr (by omega)) ?_
      norm_num

end StirlingFirstKindSigned
