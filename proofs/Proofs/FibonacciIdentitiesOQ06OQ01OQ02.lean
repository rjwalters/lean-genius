import Mathlib

/-!
# The alternating Fibonacci binomial transform — `∑ (−1)ᵏ C(n,k)·Fₖ = −Fₙ`

The parent entry `FibonacciIdentitiesOQ06OQ01` established the *ordinary* Fibonacci
binomial transform `∑_{k≤n} C(n,k)·Fₘ₊ₖ = F₂ₙ₊ₘ`, whose plus-signed binomial
weights fold the sequence onto itself at a *doubled* index. This open-question
descendant supplies the **alternating (falling) binomial transform**, where the
weights carry the sign `(−1)ᵏ`. Now the fold *collapses* rather than doubles:

* `alt_fib_binom_transform_zero` — `∑_{k≤n} (−1)ᵏ C(n,k)·Fₖ = −Fₙ`.
  The alternating binomial transform of the Fibonacci sequence returns the same
  sequence *negated*, with the index held fixed (contrast the doubling `n ↦ 2n`
  of the plus-signed transform). This is the discrete shadow of `1 − φ = ψ`
  (`ψ = (1−√5)/2` the conjugate root): applying `∑ (−1)ᵏ C(n,k)(·)ᵏ` to `φ`
  sends `φ ↦ (1−φ)ⁿ = ψⁿ`, so via Binet `∑ (−1)ᵏ C(n,k) Fₖ = (ψⁿ − φⁿ)/√5 = −Fₙ`.

* `alt_fib_binom_transform_one` — the offset-`1` companion
  `∑_{k≤n} (−1)ᵏ C(n,k)·Fₖ₊₁ = Fₙ₊₁ − Fₙ` (`= Fₙ₋₁`).

The engine is a **signed Pascal convolution** `signed_pascal_conv` — the `(−1)ᵏ`
analogue of the parent's `pascal_conv` — which splits a length-`(n+2)` signed
binomial sum for `n+1` into the *difference* of the two length-`(n+1)` signed
binomial sums for `n` at consecutive offsets. The sign turns the parent's
`+` into a `−`, and it is precisely this minus that converts the doubling into
a cancellation. Because the two offset-`0` and offset-`1` transforms feed each
other through the recurrence `Fₖ₊₂ = Fₖ + Fₖ₊₁`, they are proved together by a
single joint induction on `n` (the pair
`(∑(−1)ᵏC(n,k)Fₖ, ∑(−1)ᵏC(n,k)Fₖ₊₁) = (−Fₙ, Fₙ₊₁−Fₙ)` is the loop invariant).

No axioms, no `sorry`, no `native_decide`.
-/

namespace FibonacciIdentitiesOQ06OQ01OQ02

open Finset

/-- **Signed Pascal convolution.** For any summand `f : ℕ → ℤ`, the
`(−1)ᵏ`-signed binomial-weighted sum with `C(n+1, ·)` over a length-`(n+2)`
window equals the *difference* of the two `C(n, ·)`-weighted length-`(n+1)`
signed windows at offsets `0` and `1`:
`∑_{k<n+2} (−1)ᵏ C(n+1,k)·f(k) = ∑_{k<n+1} (−1)ᵏ C(n,k)·f(k) − ∑_{k<n+1} (−1)ᵏ C(n,k)·f(k+1)`.

This is Pascal's rule `C(n+1,k+1) = C(n,k) + C(n,k+1)` summed against the
alternating weight `(−1)ᵏ f`; the sign `(−1)^{k+1} = −(−1)^k` on the reindexed
term is what turns the parent `pascal_conv`'s `+` into a `−`. -/
theorem signed_pascal_conv (f : ℕ → ℤ) (n : ℕ) :
    ∑ k ∈ range (n + 2), (-1 : ℤ) ^ k * (n + 1).choose k * f k
      = (∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * n.choose k * f k)
        - ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * n.choose k * f (k + 1) := by
  -- Peel the `k = 0` term off the left sum and reindex the rest by `k ↦ k+1`.
  rw [Finset.sum_range_succ' (fun k => (-1 : ℤ) ^ k * (n + 1).choose k * f k) (n + 1)]
  -- Pascal's rule + `(−1)^{k+1} = −(−1)^k` on the reindexed summand.
  have hpascal : ∀ k, (-1 : ℤ) ^ (k + 1) * ((n + 1).choose (k + 1) : ℤ) * f (k + 1)
      = -((-1 : ℤ) ^ k * (n.choose k : ℤ) * f (k + 1))
        - ((-1 : ℤ) ^ k * (n.choose (k + 1) : ℤ) * f (k + 1)) := by
    intro k
    rw [Nat.choose_succ_succ' n]
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun k _ => hpascal k)]
  -- Split `∑ (−A − B) = −∑A − ∑B`.
  rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  -- Truncate the `C(n,k+1)` sum: its top term `k = n` has `C(n,n+1) = 0`.
  rw [Finset.sum_range_succ (fun k => (-1 : ℤ) ^ k * (n.choose (k + 1) : ℤ) * f (k + 1)) n,
      Nat.choose_succ_self n]
  -- Peel the first term off the RHS `∑ (−1)ᵏ C(n,k) f k`.
  rw [Finset.sum_range_succ' (fun k => (-1 : ℤ) ^ k * (n.choose k : ℤ) * f k) n]
  -- The reindexed RHS sum uses `C(n,k+1)` at offset 1, matching the LHS truncation.
  simp only [Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero, pow_zero,
    pow_succ, one_mul, mul_zero, zero_mul, mul_one, add_zero]
  -- The peeled RHS term carries an inner `·(−1)`; pull it out to match the LHS sum.
  have key : ∑ x ∈ range n, (-1 : ℤ) ^ x * -1 * (n.choose (x + 1) : ℤ) * f (x + 1)
      = -∑ x ∈ range n, (-1 : ℤ) ^ x * (n.choose (x + 1) : ℤ) * f (x + 1) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [key]
  ring

/-- **Joint invariant.** The two alternating transforms at offsets `0` and `1`
evaluate to `(−Fₙ, Fₙ₊₁ − Fₙ)`. Proved together by induction on `n`: the step
feeds each through `signed_pascal_conv`, and the offset-`2` sum that appears is
reduced back to the pair via `Fₖ₊₂ = Fₖ + Fₖ₊₁`. -/
theorem alt_fib_pair (n : ℕ) :
    (∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * n.choose k * Nat.fib k = -Nat.fib n)
      ∧ (∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * n.choose k * Nat.fib (k + 1)
          = Nat.fib (n + 1) - Nat.fib n) := by
  induction n with
  | zero => constructor <;> simp
  | succ p ih =>
    obtain ⟨ihS, ihT⟩ := ih
    -- The offset-1 sum for `p` (call it `T p`) reappears in both steps.
    have hconvS := signed_pascal_conv (fun k => Nat.fib k) p
    have hconvT := signed_pascal_conv (fun k => Nat.fib (k + 1)) p
    -- The offset-2 sum splits into offset-0 + offset-1 via `Fₖ₊₂ = Fₖ + Fₖ₊₁`.
    have hsplit : (∑ k ∈ range (p + 1), (-1 : ℤ) ^ k * p.choose k * Nat.fib (k + 1 + 1))
        = (∑ k ∈ range (p + 1), (-1 : ℤ) ^ k * p.choose k * Nat.fib k)
          + ∑ k ∈ range (p + 1), (-1 : ℤ) ^ k * p.choose k * Nat.fib (k + 1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      have : Nat.fib (k + 1 + 1) = Nat.fib k + Nat.fib (k + 1) := by
        rw [Nat.fib_add_two]
      rw [this]; push_cast; ring
    have hfib : Nat.fib (p + 1 + 1) = Nat.fib p + Nat.fib (p + 1) := by
      rw [Nat.fib_add_two]
    constructor
    · -- offset-0 at `p+1`: `S(p+1) = S(p) − T(p) = −Fₚ − (Fₚ₊₁ − Fₚ) = −Fₚ₊₁`.
      rw [hconvS, ihS, ihT]; ring
    · -- offset-1 at `p+1`: `T(p+1) = T(p) − U(p) = T(p) − (S(p)+T(p)) = −S(p) = Fₚ`.
      rw [hconvT, hsplit, ihS, ihT, hfib]; push_cast; ring

/-- **The alternating binomial transform of the Fibonacci sequence is its own
negation.** The headline offset-`0` case: `∑_{k≤n} (−1)ᵏ C(n,k)·Fₖ = −Fₙ`. -/
theorem alt_fib_binom_transform_zero (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * n.choose k * Nat.fib k = -Nat.fib n :=
  (alt_fib_pair n).1

/-- **The offset-`1` alternating binomial transform.**
`∑_{k≤n} (−1)ᵏ C(n,k)·Fₖ₊₁ = Fₙ₊₁ − Fₙ` (`= Fₙ₋₁`). -/
theorem alt_fib_binom_transform_one (n : ℕ) :
    ∑ k ∈ range (n + 1), (-1 : ℤ) ^ k * n.choose k * Nat.fib (k + 1)
      = Nat.fib (n + 1) - Nat.fib n :=
  (alt_fib_pair n).2

end FibonacciIdentitiesOQ06OQ01OQ02
