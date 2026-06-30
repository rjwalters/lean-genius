import Mathlib

/-
# Catalan Numbers: the Central-Binomial Reflection Form

Mathlib (`Mathlib/Combinatorics/Enumerative/Catalan.lean`) provides the Catalan
numbers `catalan` together with the closed form
`catalan_eq_centralBinom_div` (`catalan n = centralBinom n / (n + 1)`) and the
multiplicative bridge `succ_mul_catalan_eq_centralBinom`
(`(n + 1) * catalan n = centralBinom n`).  It does **not** record the classical
*reflection* (ballot-problem) identity

  `catalan n = C(2n, n) - C(2n, n + 1)`,

which expresses the `n`-th Catalan number as the gap between the central binomial
coefficient `C(2n, n)` and its immediate right neighbour `C(2n, n + 1)`.

Combinatorially this is André's reflection principle: of the `C(2n, n)` lattice
paths from `(0,0)` to `(n,n)`, the "bad" ones that cross the diagonal are in
reflection-bijection with the `C(2n, n + 1)` paths to the reflected endpoint, so
the Dyck (non-crossing) paths number exactly `C(2n,n) - C(2n,n+1) = catalan n`.

We give a purely arithmetic, 0-axiom derivation over `ℕ`.  Writing `B = C(2n,n)`,
`R = C(2n, n+1)` and `C = catalan n`, the two facts

* `(n + 1) * C = B`            (`succ_mul_catalan_eq_centralBinom`, with `B = centralBinom n` by `rfl`), and
* `(n + 1) * R = n * B`        (from `Nat.choose_succ_right_eq` since `2n - n = n`),

combine after multiplying the target `B = C + R` by `n + 1`:
`(n+1)*B = (n+1)*C + (n+1)*R = B + n*B = (n+1)*B`.  Cancelling the positive factor
`n + 1` gives the additive partition, and `ℕ` subtraction (`omega`) yields the
reflection form.  Everything is over `ℕ`, fully machine-checked, 0-axiom.
-/

/-- **Near-central partition (additive form).**  The central binomial coefficient
splits as the Catalan number plus its right neighbour:

  `C(2n, n) = catalan n + C(2n, n + 1)`.

This is the additive heart of the reflection identity, stated without `ℕ`
truncated subtraction so that every later corollary follows by `omega`. -/
theorem centralBinom_eq_catalan_add_choose (n : ℕ) :
    (2 * n).choose n = catalan n + (2 * n).choose (n + 1) := by
  -- `centralBinom n` is *definitionally* `(2 * n).choose n`.
  have hcb : Nat.centralBinom n = (2 * n).choose n := rfl
  -- Bridge: `(n + 1) * catalan n = C(2n, n)`.
  have hcat : (n + 1) * catalan n = (2 * n).choose n := by
    rw [← hcb]; exact succ_mul_catalan_eq_centralBinom n
  -- Neighbour relation: `(n + 1) * C(2n, n+1) = n * C(2n, n)`.
  have hchoose : (n + 1) * ((2 * n).choose (n + 1)) = n * ((2 * n).choose n) := by
    have h := Nat.choose_succ_right_eq (2 * n) n
    -- h : (2*n).choose (n+1) * (n+1) = (2*n).choose n * (2*n - n)
    have e : 2 * n - n = n := by omega
    rw [e] at h
    calc (n + 1) * ((2 * n).choose (n + 1))
          = (2 * n).choose (n + 1) * (n + 1) := by ring
      _ = (2 * n).choose n * n := h
      _ = n * ((2 * n).choose n) := by ring
  -- Multiply the target by the positive factor `n + 1`, then cancel it.
  refine Nat.eq_of_mul_eq_mul_left (show 0 < n + 1 by omega) ?_
  rw [Nat.mul_add, hcat, hchoose]
  ring

/-- **Catalan reflection / ballot form.**

  `catalan n = C(2n, n) - C(2n, n + 1)`.

The `n`-th Catalan number is the difference between the central binomial
coefficient and its right neighbour — the lattice-path count after André's
reflection removes the diagonal-crossing paths. -/
theorem catalan_eq_centralBinom_sub_choose (n : ℕ) :
    catalan n = (2 * n).choose n - (2 * n).choose (n + 1) := by
  have h := centralBinom_eq_catalan_add_choose n
  omega

/-- The same identity phrased with Mathlib's `Nat.centralBinom`:

  `catalan n = centralBinom n - C(2n, n + 1)`. -/
theorem catalan_eq_centralBinom_sub (n : ℕ) :
    catalan n = Nat.centralBinom n - (2 * n).choose (n + 1) := by
  rw [show Nat.centralBinom n = (2 * n).choose n from rfl]
  exact catalan_eq_centralBinom_sub_choose n

/-- The subtraction in the reflection form is a *genuine* difference: the right
neighbour `C(2n, n + 1)` never exceeds the central coefficient `C(2n, n)`, so the
`ℕ` subtraction is not silently truncated to `0`. -/
theorem choose_succ_le_centralBinom (n : ℕ) :
    (2 * n).choose (n + 1) ≤ (2 * n).choose n := by
  have h := centralBinom_eq_catalan_add_choose n
  omega

/-- Sanity check (`n = 3`): the reflection form computes `catalan 3` as
`C(6,3) - C(6,4)`. -/
example : catalan 3 = (2 * 3).choose 3 - (2 * 3).choose (3 + 1) :=
  catalan_eq_centralBinom_sub_choose 3

/-- `C(6,3) - C(6,4) = 20 - 15 = 5 = catalan 3`. -/
example : Nat.choose 6 3 - Nat.choose 6 4 = 5 := by decide

/-- `C(8,4) - C(8,5) = 70 - 56 = 14 = catalan 4`. -/
example : Nat.choose 8 4 - Nat.choose 8 5 = 14 := by decide
