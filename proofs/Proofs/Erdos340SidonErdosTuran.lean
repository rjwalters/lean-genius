/-
# Erdős Problem #340 (oq-02): The Erdős–Turán / Lindström upper bound, verified

The sibling file `Erdos340GreedySidonOQ02.lean` carries out the hard part of the
Erdős–Turán argument for the maximal size of a Sidon set.  It proves, **fully (0
sorries, 0 axioms)**, the sliding-window / Cauchy–Schwarz master inequality

  `sidon_window_key : ∀ ℓ ≥ 1,  ℓ · |A|² ≤ (N + ℓ) · (ℓ − 1 + |A|)`            (★)

for every Sidon set `A ⊆ {0,…,N}`.  What the parent file `Erdos340GreedySidon.lean`
left as its **only axiom** is the *closed-form consequence* of (★) obtained by
optimising the window length `ℓ`:

  `axiom sidon_upper_bound : |A| ≤ √N + ⁴√N + 1`    (the Lindström constant).

This file performs that optimisation **rigorously and axiom-free**.  Plugging the
near-optimal integer window length

  `ℓ = ⌊√N⌋ · ⌊⁴√N⌋ + 1   (≈ N^{3/4})`

into (★) yields, by elementary integer arithmetic on `Nat.sqrt`, the bound

  `sidon_card_le_sqrt : |A| ≤ ⌊√N⌋ + ⌊⁴√N⌋ + 2`.                              (†)

## What this does and does not settle

* (†) captures the **optimal leading term `√N`** — a genuine improvement over the
  elementary difference-counting bound `sidon_upper_bound_weak : |A| ≤ √(2N) + 1`
  proved in the parent (constant `√2 ≈ 1.414` vs. the optimal `1`).  It also gets
  the correct second-order `⌊⁴√N⌋ ≈ N^{1/4}` term.
* The master inequality (★) is very slightly lossy in its Cauchy–Schwarz step, so it
  cannot reach the *exact* Lindström additive constant `+1`: a short search shows
  `|A| = ⌊√N⌋ + ⌊⁴√N⌋ + 2` is genuinely **not** refutable from (★) alone (e.g.
  `N = 15`, where (★) permits one more element than the true maximum).  Hence (†)
  proves `+2`, not `+1`, and the parent's `sidon_upper_bound` axiom — which asserts
  the `+1` form — is **not** discharged here.  (†) is the sharpest closed-form bound
  that (★) supports, and is fully verified.

The open growth *lower* bound `|A ∩ [1,N]| ≫ N^{1/2−ε}` (Erdős #340 proper) is a
different, unsolved direction and is untouched.
-/
import Proofs.Erdos340GreedySidonOQ02

namespace Erdos340

open Finset

/-- **Arithmetic core of the window optimisation.**

With `ℓ = s·t + 1` and `k = s + t + 3 + d` (the first cardinality strictly above the
target `s + t + 2`, where `s = ⌊√N⌋`, `t = ⌊√s⌋`), the master inequality (★) at its
worst case `N = s² + 2s` is violated.  This is a pure polynomial inequality over `ℤ`,
where the two `Nat.sqrt` bracketings enter as `t² ≤ s ≤ t² + 2t`.

The proof writes the gap as `Q = (s·t+1)·d² + C₁·d + C₀` (a quadratic in `d` with
nonnegative coefficients) and shows the constant term factors as
`C₀ = (s+t+2)·R` with `R = −s² + s·t² + 3st − 2s + t + 3 ≥ 1`.  The bound `R ≥ 1`
is the concavity estimate `2t·R = (t²+2t−s)·e₀ + (s−t²)·e₁ + 2t(s−t²)(t²+2t−s)`,
where the endpoint values `e₀ = 3t³−2t²+t+3` and `e₁ = (t−1)²(t+2)+1` are positive. -/
private lemma window_opt_arith (s t d : ℤ) (hs : 0 ≤ s) (ht : 0 ≤ t) (hd : 0 ≤ d)
    (h1 : t ^ 2 ≤ s) (h2 : s ≤ t ^ 2 + 2 * t) :
    (s ^ 2 + 2 * s + (s * t + 1)) * (s * t + (s + t + 3 + d))
      < (s * t + 1) * (s + t + 3 + d) ^ 2 := by
  have hg : 0 ≤ s - t ^ 2 := by linarith
  have hh : 0 ≤ t ^ 2 + 2 * t - s := by linarith
  -- endpoint values of the parabola `R` in `s` are ≥ 1.
  have he0 : 1 ≤ 3 * t ^ 3 - 2 * t ^ 2 + t + 3 := by
    nlinarith [mul_nonneg (mul_nonneg ht ht) ht, sq_nonneg t, ht]
  have he1 : 1 ≤ t ^ 3 - 3 * t + 3 := by
    nlinarith [mul_nonneg (sq_nonneg (t - 1)) (by linarith : (0 : ℤ) ≤ t + 2)]
  -- `R ≥ 1` (the `d⁰` factor) via the concavity certificate.
  have hR : 1 ≤ -s ^ 2 + s * t ^ 2 + 3 * s * t - 2 * s + t + 3 := by
    rcases eq_or_lt_of_le ht with ht0 | htpos
    · -- t = 0 forces s = 0
      have hs0 : s = 0 := by nlinarith [h2, hs, ht0.symm]
      rw [← ht0, hs0]; norm_num
    · -- t > 0 : `2t·(R−1) = (t²+2t−s)(e₀−1) + (s−t²)(e₁−1) + 2t(s−t²)(t²+2t−s) ≥ 0`
      have hcert : 2 * t * 1 ≤ 2 * t * (-s ^ 2 + s * t ^ 2 + 3 * s * t - 2 * s + t + 3) := by
        nlinarith [mul_nonneg hh (by linarith : (0 : ℤ) ≤ 3 * t ^ 3 - 2 * t ^ 2 + t + 3 - 1),
                   mul_nonneg hg (by linarith : (0 : ℤ) ≤ t ^ 3 - 3 * t + 3 - 1),
                   mul_nonneg (mul_nonneg (by linarith : (0 : ℤ) ≤ 2 * t) hg) hh]
      exact le_of_mul_le_mul_left hcert (by linarith)
  -- the `d¹` coefficient is nonnegative.
  have hC1 : 0 ≤ 2 * s ^ 2 * t - s ^ 2 + 2 * s * t ^ 2 + 5 * s * t + 2 * t + 5 := by
    nlinarith [mul_nonneg hs hh, mul_nonneg (mul_nonneg hs hs) ht,
               mul_nonneg hs (mul_nonneg ht ht), mul_nonneg hs ht, ht]
  -- assemble: gap `= (s·t+1)·d² + C₁·d + (s+t+2)·R`, all pieces ≥ 0 and the last > 0.
  have hC0 : 0 < (s + t + 2) * (-s ^ 2 + s * t ^ 2 + 3 * s * t - 2 * s + t + 3) :=
    mul_pos (by linarith) (by linarith)
  nlinarith [mul_nonneg (by positivity : (0 : ℤ) ≤ s * t + 1) (sq_nonneg d),
             mul_nonneg hC1 hd, hC0, mul_nonneg hs ht]

/-- **Erdős–Turán / Lindström upper bound for Sidon sets (verified, axiom-free).**

A Sidon set `A ⊆ {0, …, N}` has at most `⌊√N⌋ + ⌊√⌊√N⌋⌋ + 2` elements.

This is the optimised closed form of the master window inequality `sidon_window_key`
(★), obtained at window length `ℓ = ⌊√N⌋·⌊√⌊√N⌋⌋ + 1 ≈ N^{3/4}`.  It improves the
elementary `√(2N)` difference bound to the optimal leading constant `√N`. -/
theorem sidon_card_le_sqrt (A : Finset ℕ) (hA : IsSidon A) (N : ℕ)
    (hAN : ∀ a ∈ A, a ≤ N) :
    A.card ≤ Nat.sqrt N + Nat.sqrt (Nat.sqrt N) + 2 := by
  by_contra hcon
  push_neg at hcon
  set s := Nat.sqrt N with hs
  set t := Nat.sqrt s with ht
  -- the two square-root bracketings, in additive form.
  have hsN : N < (s + 1) ^ 2 := Nat.lt_succ_sqrt' N
  have hts1 : t ^ 2 ≤ s := Nat.sqrt_le' s
  have hts2 : s < (t + 1) ^ 2 := Nat.lt_succ_sqrt' s
  have hNb : N ≤ s ^ 2 + 2 * s := by nlinarith [hsN]
  have h2nat : s ≤ t ^ 2 + 2 * t := by nlinarith [hts2]
  -- master inequality at ℓ = s·t + 1.
  have hℓ : 1 ≤ s * t + 1 := Nat.le_add_left 1 (s * t)
  have key := Erdos340.OQ02.sidon_window_key A hA N (s * t + 1) hℓ hAN
  rw [Nat.add_sub_cancel] at key
  -- replace `N` by its worst case `s² + 2s`.
  have key2 : (s * t + 1) * A.card ^ 2
      ≤ (s ^ 2 + 2 * s + (s * t + 1)) * (s * t + A.card) :=
    le_trans key (Nat.mul_le_mul_right _ (by omega))
  -- write `A.card = s + t + 3 + d`.
  obtain ⟨d, hd⟩ : ∃ d, A.card = s + t + 3 + d := ⟨A.card - (s + t + 3), by omega⟩
  rw [hd] at key2
  -- cast to ℤ and contradict the arithmetic core.
  have hcontra := window_opt_arith (s : ℤ) (t : ℤ) (d : ℤ)
    (Int.natCast_nonneg s) (Int.natCast_nonneg t) (Int.natCast_nonneg d)
    (by exact_mod_cast hts1) (by exact_mod_cast h2nat)
  have key2Z : ((s * t + 1 : ℕ) : ℤ) * ((s + t + 3 + d : ℕ) : ℤ) ^ 2
      ≤ ((s ^ 2 + 2 * s + (s * t + 1) : ℕ) : ℤ) * ((s * t + (s + t + 3 + d) : ℕ) : ℤ) := by
    exact_mod_cast key2
  push_cast at key2Z
  linarith [hcontra, key2Z]

end Erdos340
