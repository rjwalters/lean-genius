import Mathlib

/-
# Waring's problem for fourth powers via a Lagrange-type argument: `g(4) ≤ 53`

This file gives a **sorry-free, axiom-free** proof that every natural number is a
sum of at most `53` fourth powers, i.e. an explicit finite upper bound for the
Waring constant `g(4)`.  The whole argument is "Lagrange-type": it rests entirely
on Lagrange's four-square theorem (`Nat.sum_four_squares`) together with the
classical **Liouville identity**

  `6 (a² + b² + c² + d²)² = Σ_{i<j} ((xᵢ + xⱼ)⁴ + (xᵢ − xⱼ)⁴)`        (★)

over the four variables `a, b, c, d`.  The right-hand side is a sum of `12`
fourth powers, so (★) says that `6 m²` is a sum of `12` fourth powers whenever
`m` is itself a sum of four squares — which, by Lagrange, is *every* `m`.

## Context in the gallery

The existing `lagrange-four-squares-waring-g2-*` entries establish the **lower**
bound `g(4) ≥ 19` (via a counting / `omega` infeasibility argument).  This file
supplies the complementary **upper** bound `g(4) ≤ 53` and, in particular, the
*finiteness* of `g(4)` — the qualitative heart of Waring's problem for fourth
powers — by the elementary Liouville route rather than by the analytic
circle-method machinery.  The constant `53` is the classical Liouville bound; it
is not optimal (the true value is `g(4) = 19`), but it is obtained here by a
completely self-contained finite argument.

## Proof outline

1. `liouville_identity` — the polynomial identity (★) over `ℤ`, closed by `ring`.
2. `IsSumOfFourthPowers` — `n` is a sum of `k` fourth powers (zero summands are
   allowed, so this really means "at most `k`").  It is closed under
   concatenation (`append`) and padding by zeros (`zeros`, `succ`).
3. `sixMulSq_isSum` — `6 m²` is a sum of `12` fourth powers, by feeding the four
   squares from Lagrange into (★).  The `12` summands are `a ± b`, `a ± c`, …,
   realised as natural numbers via `Int.natAbs`.
4. `sixMul_isSum` — `6 Q` is a sum of `48` fourth powers, writing
   `Q = m₁² + m₂² + m₃² + m₄²` (Lagrange again) and applying step 3 four times.
5. `waring_four` — `N = 6 (N / 6) + N % 6` with `N % 6 ≤ 5`; the quotient block
   is `48` fourth powers and the residue is at most `5` copies of `1⁴`, giving
   `53` in total.
-/

namespace LagrangeFourSquaresOQ03

/-- **Liouville's identity** over `ℤ`: six times the square of a sum of four
squares equals a sum of twelve fourth powers, namely `(xᵢ ± xⱼ)⁴` over the six
unordered pairs `{i, j} ⊆ {a, b, c, d}`. -/
theorem liouville_identity (a b c d : ℤ) :
    6 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2 =
      (a + b) ^ 4 + (a - b) ^ 4 + (a + c) ^ 4 + (a - c) ^ 4 + (a + d) ^ 4 + (a - d) ^ 4
        + (b + c) ^ 4 + (b - c) ^ 4 + (b + d) ^ 4 + (b - d) ^ 4 + (c + d) ^ 4 + (c - d) ^ 4 := by
  ring

/-- For an integer `z`, the fourth power of its natural absolute value (viewed
back in `ℤ`) is `z ⁴`.  This lets us realise the difference summands `(xᵢ − xⱼ)⁴`
of Liouville's identity as fourth powers of *natural* numbers. -/
theorem cast_natAbs_pow4 (z : ℤ) : ((z.natAbs : ℤ)) ^ 4 = z ^ 4 := by
  rw [← Int.abs_eq_natAbs, ← abs_pow]
  exact abs_of_nonneg (by positivity)

/-- `n` is a sum of `k` fourth powers.  Because `0 ⁴ = 0`, allowing zero
summands means this is really "`n` is a sum of *at most* `k` fourth powers". -/
def IsSumOfFourthPowers (k n : ℕ) : Prop :=
  ∃ l : List ℕ, l.length = k ∧ (l.map (· ^ 4)).sum = n

namespace IsSumOfFourthPowers

/-- The empty sum: `0` is a sum of `0` fourth powers. -/
theorem zero : IsSumOfFourthPowers 0 0 := ⟨[], rfl, rfl⟩

/-- A single fourth power. -/
theorem single (a : ℕ) : IsSumOfFourthPowers 1 (a ^ 4) := ⟨[a], rfl, by simp⟩

/-- Concatenating representations: a sum of `k₁` fourth powers plus a sum of
`k₂` fourth powers is a sum of `k₁ + k₂` fourth powers. -/
theorem append {k₁ k₂ x y : ℕ} (hx : IsSumOfFourthPowers k₁ x)
    (hy : IsSumOfFourthPowers k₂ y) : IsSumOfFourthPowers (k₁ + k₂) (x + y) := by
  obtain ⟨l, hl, hls⟩ := hx
  obtain ⟨m, hm, hms⟩ := hy
  exact ⟨l ++ m, by rw [List.length_append, hl, hm],
    by rw [List.map_append, List.sum_append, hls, hms]⟩

/-- `0` is a sum of any number `k` of fourth powers (all summands zero). -/
theorem zeros (k : ℕ) : IsSumOfFourthPowers k 0 := by
  refine ⟨List.replicate k 0, by simp, ?_⟩
  rw [List.map_replicate]
  simp

/-- Padding by one zero summand: monotonicity in the number of summands. -/
theorem succ {k n : ℕ} (h : IsSumOfFourthPowers k n) : IsSumOfFourthPowers (k + 1) n := by
  have := (zeros 1).append h
  simpa [Nat.add_comm] using this

end IsSumOfFourthPowers

open IsSumOfFourthPowers

/-- **Liouville step.** For any naturals `a, b, c, d`, the number
`6 (a² + b² + c² + d²)²` is a sum of `12` fourth powers.  The twelve summands
are `a + b`, `|a − b|`, …, `c + d`, `|c − d|`, and the identity is verified by
casting to `ℤ` and applying `liouville_identity`. -/
theorem sixMulSq_isSum (a b c d : ℕ) :
    IsSumOfFourthPowers 12 (6 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ^ 2) := by
  refine ⟨[a + b, ((a : ℤ) - b).natAbs, a + c, ((a : ℤ) - c).natAbs,
           a + d, ((a : ℤ) - d).natAbs, b + c, ((b : ℤ) - c).natAbs,
           b + d, ((b : ℤ) - d).natAbs, c + d, ((c : ℤ) - d).natAbs], rfl, ?_⟩
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [← @Nat.cast_inj ℤ]
  simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat, cast_natAbs_pow4]
  linear_combination liouville_identity (a : ℤ) (b : ℤ) (c : ℤ) (d : ℤ)

/-- `6 m²` is a sum of `12` fourth powers, for every natural `m`: apply
Lagrange's four-square theorem to `m` and feed the result into the Liouville
step. -/
theorem sixMulSq (m : ℕ) : IsSumOfFourthPowers 12 (6 * m ^ 2) := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares m
  have := sixMulSq_isSum a b c d
  rwa [h] at this

/-- `6 Q` is a sum of `48` fourth powers, for every natural `Q`: write
`Q = m₁² + m₂² + m₃² + m₄²` (Lagrange), so `6 Q = 6 m₁² + 6 m₂² + 6 m₃² + 6 m₄²`,
and apply the previous step to each block. -/
theorem sixMul (Q : ℕ) : IsSumOfFourthPowers 48 (6 * Q) := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares Q
  have e : 6 * Q = 6 * a ^ 2 + 6 * b ^ 2 + (6 * c ^ 2 + 6 * d ^ 2) := by rw [← h]; ring
  rw [e]
  have h1 := ((sixMulSq a).append (sixMulSq b)).append ((sixMulSq c).append (sixMulSq d))
  -- `h1 : IsSumOfFourthPowers ((12+12)+(12+12)) ((6a²+6b²)+(6c²+6d²))`
  rw [show (6 * a ^ 2 + 6 * b ^ 2 + (6 * c ^ 2 + 6 * d ^ 2))
        = (6 * a ^ 2 + 6 * b ^ 2) + (6 * c ^ 2 + 6 * d ^ 2) by ring]
  exact h1

/-- **Waring's problem for fourth powers, upper bound.**  Every natural number
`N` is a sum of at most `53` fourth powers.  Hence the Waring constant `g(4)` is
finite, with `g(4) ≤ 53`.  The proof is purely a Lagrange-type argument: it uses
only Lagrange's four-square theorem and Liouville's identity. -/
theorem waring_four (N : ℕ) : IsSumOfFourthPowers 53 N := by
  -- residue part: `N % 6 ≤ 5` copies of `1⁴ = 1`, padded to `5` summands
  have hr : N % 6 ≤ 5 := by omega
  have hres : IsSumOfFourthPowers 5 (N % 6) := by
    -- `N % 6` copies of `1` realise `N % 6`; pad with `5 - N % 6` zeros
    have hones : IsSumOfFourthPowers (N % 6) (N % 6) := by
      refine ⟨List.replicate (N % 6) 1, by simp, ?_⟩
      rw [List.map_replicate]
      simp
    have := hones.append (zeros (5 - N % 6))
    rwa [Nat.add_sub_cancel' hr, add_zero] at this
  -- quotient part: `48` fourth powers for `6 * (N / 6)`
  have hquot : IsSumOfFourthPowers 48 (6 * (N / 6)) := sixMul (N / 6)
  -- combine: `48 + 5 = 53` summands for `6 * (N / 6) + N % 6 = N`
  have := hquot.append hres
  rwa [Nat.div_add_mod N 6] at this

end LagrangeFourSquaresOQ03
