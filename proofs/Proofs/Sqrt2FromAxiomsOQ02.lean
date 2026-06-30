import Mathlib

/-
# √2 is Irrational by Infinite Descent (the Continued-Fraction Tail Map)

## What This Proves
A self-contained proof that `√2` is irrational, taking a route that is genuinely
different from the two siblings in this lineage:

* the parent `Sqrt2IrrationalFromAxioms` (`Sqrt2FromAxioms`) uses **parity**: it
  assumes the fraction is in lowest terms and derives that numerator *and*
  denominator are both even, contradicting coprimality;
* the first follow-up `Sqrt2FromAxiomsOQ01` (`SqrtPrimeFromAxioms`) lifts that
  parity argument to all primes via Euclid's criterion.

Here we instead use **Fermat's method of infinite descent**, driven by the map

```
  (a, b)  ↦  (2·b − a,  a − b).
```

The single algebraic fact `descent_step` shows this map sends *any* positive
solution of `a² = 2·b²` to a *strictly smaller* positive solution.  Iterating
would produce an infinite strictly-decreasing sequence of naturals, which is
impossible — so no positive solution exists.

## Why the descent map is the continued fraction of √2
`√2 = [1; 2, 2, 2, …]` has the purely periodic continued fraction with all
partial quotients equal to `2` (after the leading `1`).  One step of the
Euclidean / continued-fraction algorithm applied to the vector `(a, b)`
approximating `√2 ≈ a/b` subtracts off the integer part `2` of `a/b + 1` and
inverts, which is exactly `(a, b) ↦ (2b − a, a − b)` up to relabelling.  A
*quadratic irrational* has an *eventually periodic* continued fraction; for `√2`
the period never terminates, and the non-termination of this descent **is** that
statement.  Equivalently, `(2b − a, a − b)` is the image of `(a, b)` under the
inverse of the matrix `[[1,1],[1,2]]` whose powers generate the convergents
`1/1, 3/2, 7/5, 17/12, …` of `√2`.

The crucial structural difference from the parity proof: descent needs **no
coprimality / lowest-terms hypothesis**.  It contradicts the well-ordering of ℕ
directly, on an *arbitrary* positive solution.

## Approach
We build the descent from the minimal arithmetic toolbox (`ring`, `omega`,
`nlinarith`, `linarith`, `linear_combination`, `zify`).  The bridges to ℤ and ℚ
reuse only the standard cast lemmas.

## Status
- [x] Complete proof, no sorries
- [x] 0 axioms beyond Mathlib's foundational `propext`/`Classical.choice`/`Quot.sound`
- [x] Core: infinite descent via the continued-fraction tail map (no coprimality)
- [x] ℤ and ℚ corollaries: no nontrivial integer solution; `√2 ∉ ℚ`
-/

namespace Sqrt2FromAxiomsOQ02

-- ============================================================
-- PART 1: The descent step (the continued-fraction tail map)
-- ============================================================

/-- **The descent step.**  If `(a, b)` is a *positive* solution of `a² = 2 b²`,
then `(2b − a, a − b)` is again a solution and its second coordinate `a − b`
is strictly between `0` and `b`.

This is one step of the continued-fraction algorithm for `√2 = [1; 2,2,2,…]`:
the map `(a, b) ↦ (2b − a, a − b)` strictly shrinks the denominator while
preserving the equation `x² = 2 y²`.  No coprimality assumption is used. -/
theorem descent_step (a b : Nat) (hpos : 0 < b) (h : a * a = 2 * (b * b)) :
    (2 * b - a) * (2 * b - a) = 2 * ((a - b) * (a - b)) ∧ 0 < a - b ∧ a - b < b := by
  have hbb : 0 < b * b := Nat.mul_pos hpos hpos
  -- Lower bound: a > b  (else a² ≤ b² < 2b² = a²)
  have hba : b < a := by
    rcases Nat.lt_or_ge b a with h1 | h1
    · exact h1
    · exfalso
      have hle : a * a ≤ b * b := Nat.mul_le_mul h1 h1
      linarith [h, hle, hbb]
  -- Upper bound: a < 2b  (else (2b)² ≤ a² = 2b², impossible)
  have hab : a < 2 * b := by
    rcases Nat.lt_or_ge a (2 * b) with h1 | h1
    · exact h1
    · exfalso
      have hle : (2 * b) * (2 * b) ≤ a * a := Nat.mul_le_mul h1 h1
      nlinarith [h, hle, hbb]
  refine ⟨?_, by omega, by omega⟩
  -- The algebraic identity, computed over ℤ where subtraction is honest.
  have hz : (a : ℤ) * a = 2 * ((b : ℤ) * b) := by exact_mod_cast h
  zify [Nat.le_of_lt hba, Nat.le_of_lt hab]
  linear_combination (-1 : ℤ) * hz

-- ============================================================
-- PART 2: Infinite descent ⇒ no positive ℕ solution
-- ============================================================

/-- Bounded form of the descent, proved by induction on the fuel `n ≥ b`.
The recursive call feeds the strictly-smaller denominator `a − b ≤ n` back in. -/
theorem no_sol_aux : ∀ (n a b : Nat), b ≤ n → a * a = 2 * (b * b) → b = 0 := by
  intro n
  induction n with
  | zero => intro a b hb _; omega
  | succ n ih =>
    intro a b hb h
    rcases Nat.eq_zero_or_pos b with h0 | hpos
    · exact h0
    · exfalso
      obtain ⟨hident, hdpos, hdlt⟩ := descent_step a b hpos h
      have hbound : a - b ≤ n := by omega
      have hzero : a - b = 0 := ih (2 * b - a) (a - b) hbound hident
      omega

/-- **No nontrivial natural solution.**  `a² = 2 b²` forces `b = 0` (hence `a = 0`).
There is no way to write `√2 = a/b` with `b > 0`. -/
theorem no_nat_solution (a b : Nat) (h : a * a = 2 * (b * b)) : b = 0 :=
  no_sol_aux b a b (Nat.le_refl b) h

-- ============================================================
-- PART 3: Integer and rational corollaries
-- ============================================================

/-- No nontrivial integer solution: `x² = 2 y²` forces `y = 0`.
Obtained from the ℕ statement by passing to absolute values. -/
theorem no_int_solution (x y : ℤ) (h : x * x = 2 * (y * y)) : y = 0 := by
  have key : x.natAbs * x.natAbs = 2 * (y.natAbs * y.natAbs) := by
    have hx : ((x.natAbs * x.natAbs : ℕ) : ℤ) = x * x := Int.natAbs_mul_self
    have hy : ((y.natAbs * y.natAbs : ℕ) : ℤ) = y * y := Int.natAbs_mul_self
    have hZ : ((x.natAbs * x.natAbs : ℕ) : ℤ)
        = ((2 * (y.natAbs * y.natAbs) : ℕ) : ℤ) := by
      have e : ((2 * (y.natAbs * y.natAbs) : ℕ) : ℤ) = 2 * (y * y) := by
        rw [Nat.cast_mul, hy]; norm_num
      rw [hx, e]; exact h
    exact_mod_cast hZ
  have hy0 : y.natAbs = 0 := no_nat_solution x.natAbs y.natAbs key
  omega

/-- **√2 is irrational.**  No rational `q` satisfies `q² = 2`.
If `q = num/den` with `den > 0`, then `num² = 2·den²` over ℤ, so `den = 0`
by `no_int_solution` — contradicting `den ≠ 0`. -/
theorem sqrt2_not_rational : ¬ ∃ q : ℚ, q * q = 2 := by
  rintro ⟨q, hq⟩
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast Rat.den_ne_zero q
  have key : q.num * q.num = 2 * ((q.den : ℤ) * (q.den : ℤ)) := by
    have hnum : (q.num : ℚ) = q * (q.den : ℚ) := (div_eq_iff hd).mp (Rat.num_div_den q)
    have h0 : (q.num : ℚ) * q.num = 2 * ((q.den : ℚ) * q.den) := by
      calc (q.num : ℚ) * q.num
          = (q * q.den) * (q * q.den) := by rw [hnum]
        _ = (q * q) * ((q.den : ℚ) * q.den) := by ring
        _ = 2 * ((q.den : ℚ) * q.den) := by rw [hq]
    exact_mod_cast h0
  have hzero : (q.den : ℤ) = 0 := no_int_solution q.num (q.den : ℤ) key
  exact Rat.den_ne_zero q (by exact_mod_cast hzero)

-- ============================================================
-- PART 4: The descent map, made explicit
-- ============================================================

/-- The continued-fraction tail map `T(a,b) = (2b − a, a − b)` for `√2`,
packaged as a function on pairs. -/
def cfStep (p : Nat × Nat) : Nat × Nat := (2 * p.2 - p.1, p.1 - p.2)

/-- On a positive solution, `cfStep` lands on a solution with a strictly
smaller denominator: the engine of the descent, restated for `cfStep`. -/
theorem cfStep_descends (a b : Nat) (hpos : 0 < b) (h : a * a = 2 * (b * b)) :
    (cfStep (a, b)).1 * (cfStep (a, b)).1 = 2 * ((cfStep (a, b)).2 * (cfStep (a, b)).2)
      ∧ (cfStep (a, b)).2 < b := by
  obtain ⟨hident, _, hdlt⟩ := descent_step a b hpos h
  exact ⟨hident, hdlt⟩

end Sqrt2FromAxiomsOQ02
