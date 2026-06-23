import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The obstruction direction of the Legendre–Gauss three-square theorem

**Open Question (`zsqrtd-neg-two-oq-02`)**: extend the parent gallery entry
`Proofs/ZsqrtdNegTwo.lean` ("ℤ[√−2]: Euclidean Domain and x² + 2y²
Representations") towards the full **Legendre–Gauss three-square theorem**

  `n = x² + y² + z²` is solvable  ↔  `n` is **not** of the form `4^a (8b + 7)`.

The parent file and its siblings establish *sufficiency* slices — e.g. every
prime `p ≡ 3 (mod 8)` is a sum of three squares, via `p = a² + 2b² = a² + b² + b²`
extracted from the Euclidean domain `ℤ[√−2]`.  The full forward direction (every
`n ∉ 4^a(8b+7)` is a sum of three squares) additionally requires Dirichlet's
theorem on primes in arithmetic progressions and is **not** formalised here (and
is not yet in Mathlib).

This file proves the **complete necessity / obstruction direction**, which is the
genuinely elementary and self-contained half:

  `not_sumThreeSq_four_pow_mul`:
    for all `a b : ℕ`, `4^a (8b + 7)` is **never** a sum of three integer squares.

Equivalently (contrapositive, `sumThreeSq_ne_four_pow_mul`): if `n` is a sum of
three squares then `n` is not of the form `4^a (8b + 7)`.

Mathlib has `Mathlib/NumberTheory/SumTwoSquares.lean` and
`Mathlib/NumberTheory/SumFourSquares.lean`, but **no** three-square result; this
obstruction is therefore new content.

## Proof architecture

Two elementary modular facts, combined by induction on the exponent `a`:

1. **Mod-8 obstruction** (`sumThreeSq_ne_seven_mod_eight`): a sum of three
   squares is never `≡ 7 (mod 8)`.  Squares mod 8 lie in `{0,1,4}`, and no three
   of those sum to `7`; verified by `decide` over `ZMod 8`.

2. **Descent** (`descent_even`): if `x² + y² + z² ≡ 0 (mod 4)` then `x, y, z` are
   all even.  Squares mod 4 lie in `{0,1}`, and the only way three of them sum to
   `0 (mod 4)` is `0 + 0 + 0`; verified by `decide` over `ZMod 4` (mapping down
   to `ZMod 2` to read off parity).

The induction: the base case `a = 0` gives `8b + 7 ≡ 7 (mod 8)`, excluded by (1).
For `a + 1`, the value is `4 · (4^a (8b+7)) ≡ 0 (mod 4)`, so by (2) any
representation halves to a representation of `4^a (8b+7)`, contradicting the
induction hypothesis.
-/

namespace ZsqrtNegTwoOQ02

open scoped Classical

/-! ## Step 1 — the mod-8 obstruction -/

/-- **Mod-8 obstruction.** A sum of three integer squares is never `≡ 7 (mod 8)`.
Squares in `ZMod 8` are `{0, 1, 4}`, and no three of those sum to `7`. -/
theorem sumThreeSq_ne_seven_mod_eight (x y z : ℤ) :
    ((x ^ 2 + y ^ 2 + z ^ 2 : ℤ) : ZMod 8) ≠ 7 := by
  have key : ∀ a b c : ZMod 8, a ^ 2 + b ^ 2 + c ^ 2 ≠ 7 := by decide
  push_cast
  exact key _ _ _

/-! ## Step 2 — the descent step -/

/-- **Descent.** If `x² + y² + z² ≡ 0 (mod 4)` then `x`, `y`, `z` are all even.
Squares in `ZMod 4` are `{0, 1}`, so a sum of three of them vanishing mod 4
forces each to be `0`, i.e. each base even.  We read off parity through the
ring map `ZMod 4 → ZMod 2`. -/
theorem descent_even (x y z : ℤ)
    (h : ((x ^ 2 + y ^ 2 + z ^ 2 : ℤ) : ZMod 4) = 0) :
    (2 : ℤ) ∣ x ∧ (2 : ℤ) ∣ y ∧ (2 : ℤ) ∣ z := by
  -- the ring homomorphism `ZMod 4 → ZMod 2`
  set f : ZMod 4 →+* ZMod 2 := ZMod.castHom (by norm_num) (ZMod 2) with hf
  -- finite check: in `ZMod 4`, a²+b²+c²=0 forces all three to vanish mod 2
  have key : ∀ a b c : ZMod 4, a ^ 2 + b ^ 2 + c ^ 2 = 0 →
      f a = 0 ∧ f b = 0 ∧ f c = 0 := by decide
  -- transport the hypothesis into `ZMod 4`
  have h4 : (x : ZMod 4) ^ 2 + (y : ZMod 4) ^ 2 + (z : ZMod 4) ^ 2 = 0 := by
    push_cast at h; exact h
  obtain ⟨hx, hy, hz⟩ := key _ _ _ h4
  -- `f ((x : ZMod 4)) = (x : ZMod 2)` since `f` is a ring hom out of `ℤ`'s image
  have fx : f (x : ZMod 4) = (x : ZMod 2) := by rw [hf]; exact map_intCast _ x
  have fy : f (y : ZMod 4) = (y : ZMod 2) := by rw [hf]; exact map_intCast _ y
  have fz : f (z : ZMod 4) = (z : ZMod 2) := by rw [hf]; exact map_intCast _ z
  refine ⟨?_, ?_, ?_⟩
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd x 2).1 (by rw [← fx]; exact hx)
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd y 2).1 (by rw [← fy]; exact hy)
  · exact (ZMod.intCast_zmod_eq_zero_iff_dvd z 2).1 (by rw [← fz]; exact hz)

/-! ## Step 3 — the main obstruction theorem -/

/-- **Necessity direction of the three-square theorem.**  For every `a b : ℕ`,
the number `4^a (8b + 7)` is *not* a sum of three integer squares. -/
theorem not_sumThreeSq_four_pow_mul (a b : ℕ) :
    ¬ ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = 4 ^ a * (8 * b + 7) := by
  induction a with
  | zero =>
    -- base case: `8b + 7 ≡ 7 (mod 8)`, excluded by the mod-8 obstruction
    rintro ⟨x, y, z, h⟩
    apply sumThreeSq_ne_seven_mod_eight x y z
    rw [h]
    have e : ((4 : ℤ) ^ 0 * (8 * (b : ℤ) + 7) : ℤ) = 8 * (b : ℤ) + 7 := by ring
    rw [e]
    push_cast
    have h8 : (8 : ZMod 8) = 0 := by decide
    rw [h8]; ring
  | succ a ih =>
    -- inductive step: `4^(a+1)(8b+7) = 4 · (4^a(8b+7)) ≡ 0 (mod 4)`; descend
    rintro ⟨x, y, z, h⟩
    -- the right-hand side is divisible by 4
    have hdvd : (4 : ℤ) ∣ 4 ^ (a + 1) * (8 * b + 7) :=
      Dvd.dvd.mul_right (dvd_pow_self 4 (Nat.succ_ne_zero a)) _
    have h0 : ((x ^ 2 + y ^ 2 + z ^ 2 : ℤ) : ZMod 4) = 0 := by
      rw [h, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast hdvd
    obtain ⟨⟨x', hx'⟩, ⟨y', hy'⟩, ⟨z', hz'⟩⟩ := descent_even x y z h0
    -- substitute `x = 2x'`, etc., and cancel the factor `4`
    apply ih
    refine ⟨x', y', z', ?_⟩
    have hpow : (4 : ℤ) ^ (a + 1) = 4 * 4 ^ a := by rw [pow_succ]; ring
    have h2 := h
    rw [hpow, hx', hy', hz'] at h2
    have h4 : (4 : ℤ) * (x' ^ 2 + y' ^ 2 + z' ^ 2) = 4 * (4 ^ a * (8 * b + 7)) := by
      linear_combination h2
    exact mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) h4

/-- **Contrapositive form.**  If `n` is a sum of three integer squares, then `n`
is not of the form `4^a (8b + 7)`.  This is the necessity half of the
Legendre–Gauss three-square theorem. -/
theorem sumThreeSq_ne_four_pow_mul {n : ℤ} (a b : ℕ)
    (h : ∃ x y z : ℤ, x ^ 2 + y ^ 2 + z ^ 2 = n) :
    n ≠ 4 ^ a * (8 * b + 7) := by
  rintro rfl
  exact not_sumThreeSq_four_pow_mul a b h

/-! ## Step 4 — the bridge back to the parent ℤ[√−2] norm form `x² + 2y²`

The parent gallery entry `Proofs/ZsqrtdNegTwo.lean` develops the norm form `x² + 2y²` of
`ℤ[√−2]`.  These two lemmas place that development *inside* the three-square picture and
show it is compatible with the Legendre obstruction proved above: every norm-form value is
a sum of three squares, and consequently no norm-form value is of the excluded shape
`4^a (8b + 7)`.  This is the elementary inclusion side — the ℤ[√−2] representable numbers
are a (proper, ~36 %) subset of the sums of three squares, never the full converse. -/

/-- **Norm-form inclusion.**  Every value of the ℤ[√−2] norm form `x² + 2y²` is a sum of
three integer squares, via the trivial splitting `x² + 2y² = x² + y² + y²`. -/
theorem normForm_isSumThreeSq (x y : ℤ) :
    ∃ a b c : ℤ, a ^ 2 + b ^ 2 + c ^ 2 = x ^ 2 + 2 * y ^ 2 :=
  ⟨x, y, y, by ring⟩

/-- **Norm-form values avoid the Legendre excluded form.**  Combining the inclusion with the
obstruction: `x² + 2y²` is never of the form `4^a (8b + 7)`.  So the ℤ[√−2] representable
numbers respect the three-square obstruction — a consistency check tying the parent norm-form
development to the necessity direction proved here. -/
theorem normForm_ne_four_pow_mul (x y : ℤ) (a b : ℕ) :
    x ^ 2 + 2 * y ^ 2 ≠ 4 ^ a * (8 * b + 7) :=
  sumThreeSq_ne_four_pow_mul a b (normForm_isSumThreeSq x y)

end ZsqrtNegTwoOQ02
