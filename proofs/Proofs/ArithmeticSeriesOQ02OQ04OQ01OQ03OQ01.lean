/-
  Vandermonde Convolution for Rising / Falling Factorials over a Commutative Ring

  Open Question (arithmetic-series-oq-02-oq-04-oq-01-oq-03-oq-01):
  Lift the numerical falling-factorial Vandermonde identity of the parent entry
  (over ℕ) to genuine polynomial identities valid for any elements x, y of an
  arbitrary commutative ring R.

  The **rising factorial** of x ∈ R at k is
    x^{(k)} = x · (x+1) ··· (x+k-1),   x^{(0)} = 1.

  Main theorem (rising-factorial / umbral binomial convolution):
    (x+y)^{(r)} = ∑_{j=0}^{r} C(r,j) · x^{(j)} · y^{(r-j)}     for all x, y ∈ R.

  This is the binomial theorem for the finite-difference operator Δf(x)=f(x+1)-f(x),
  for which the rising/falling factorials play the role of monomials.  Mathlib has
  `ascPochhammer`/`descPochhammer` but no `ascPochhammer_add` (binomial convolution),
  so the content is genuinely absent and is proved here directly by induction on r,
  mirroring the proof architecture of `Commute.add_pow`.

  Companion:
  * `fallingFactorial_add` — the falling-factorial mirror
      (x+y)^{underline r} = ∑ C(r,j) x^{underline j} y^{underline (r-j)},
    obtained from the rising form via the reflection x^{underline k} = (-1)^k (-x)^{(k)}.

  All results are over an arbitrary `CommRing`, 0 axioms, 0 sorries.
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open Finset BigOperators

namespace RisingFactorialVandermonde

/-- Rising factorial of a ring element: `x^{(k)} = x·(x+1)···(x+k-1)`. -/
def risingFactorial {R : Type*} [CommRing R] (x : R) : ℕ → R
  | 0     => 1
  | k + 1 => risingFactorial x k * (x + k)

@[simp] lemma risingFactorial_zero {R : Type*} [CommRing R] (x : R) :
    risingFactorial x 0 = 1 := rfl

lemma risingFactorial_succ {R : Type*} [CommRing R] (x : R) (k : ℕ) :
    risingFactorial x (k + 1) = risingFactorial x k * (x + k) := rfl

/-- **Rising-factorial Vandermonde convolution over an arbitrary commutative ring.**
    `(x+y)^{(r)} = ∑_{j=0}^{r} C(r,j) · x^{(j)} · y^{(r-j)}`.

    Proved by induction on `r`, mirroring `Commute.add_pow`: the successor step splits
    the shift factor `(x+y+r) = (x+j) + (y+(r-j))` (valid since `j ≤ r`), turning the
    inductive hypothesis into two sums that recombine by Pascal's rule. -/
theorem risingFactorial_add {R : Type*} [CommRing R] (x y : R) (r : ℕ) :
    risingFactorial (x + y) r
      = ∑ j ∈ range (r + 1),
          (r.choose j : R) * risingFactorial x j * risingFactorial y (r - j) := by
  induction r with
  | zero => simp
  | succ r ih =>
    -- Unfold the outer rising factorial and apply the inductive hypothesis.
    rw [risingFactorial_succ, ih, sum_mul]
    -- Rewrite each term of the (IH · shift) sum as a sum of two pieces.
    have key : ∀ j ∈ range (r + 1),
        ((r.choose j : R) * risingFactorial x j * risingFactorial y (r - j)) *
            ((x + y) + (r : R))
          = (r.choose j : R) * risingFactorial x (j + 1) * risingFactorial y (r - j)
            + (r.choose j : R) * risingFactorial x j * risingFactorial y (r - j + 1) := by
      intro j hj
      rw [mem_range, Nat.lt_succ_iff] at hj
      have hcast : ((j : ℕ) : R) + ((r - j : ℕ) : R) = (r : R) := by
        rw [← Nat.cast_add, Nat.add_sub_cancel' hj]
      have hsplit : (x + y) + (r : R) = (x + (j : R)) + (y + ((r - j : ℕ) : R)) := by
        rw [← hcast]; ring
      rw [hsplit, risingFactorial_succ x j, risingFactorial_succ y (r - j)]
      ring
    rw [sum_congr rfl key, sum_add_distrib]
    -- Name the two accumulated sums.
    set A := ∑ j ∈ range (r + 1),
      (r.choose j : R) * risingFactorial x (j + 1) * risingFactorial y (r - j) with hA
    set B := ∑ j ∈ range (r + 1),
      (r.choose j : R) * risingFactorial x j * risingFactorial y (r - j + 1) with hB
    -- Target sum, expanded by peeling the j = 0 term and Pascal's rule.
    rw [sum_range_succ' (fun j =>
        ((r + 1).choose j : R) * risingFactorial x j * risingFactorial y (r + 1 - j)) (r + 1)]
    -- The j = 0 term is  1 · 1 · y^{(r+1)} = risingFactorial y (r+1).
    simp only [Nat.choose_zero_right, Nat.cast_one, risingFactorial_zero, Nat.sub_zero,
      one_mul, mul_one]
    -- Split C(r+1, j+1) = C(r, j) + C(r, j+1) inside the shifted sum.
    have hpascal : ∀ j ∈ range (r + 1),
        ((r + 1).choose (j + 1) : R) * risingFactorial x (j + 1) *
            risingFactorial y (r + 1 - (j + 1))
          = (r.choose j : R) * risingFactorial x (j + 1) * risingFactorial y (r - j)
            + (r.choose (j + 1) : R) * risingFactorial x (j + 1) * risingFactorial y (r - j) := by
      intro j _
      rw [Nat.choose_succ_succ, Nat.cast_add]
      have : r + 1 - (j + 1) = r - j := by omega
      rw [this]
      ring
    rw [sum_congr rfl hpascal, sum_add_distrib]
    -- The first split sum is exactly A.
    rw [← hA]
    -- Remaining goal:  A + B = A + (C + y^{(r+1)})  where
    --   C = ∑ j ∈ range (r+1), C(r,j+1) x^{(j+1)} y^{(r-j)}.
    -- Show B = C + y^{(r+1)} by peeling the j = 0 term of B and reindexing.
    have hB' : B = (∑ j ∈ range (r + 1),
        (r.choose (j + 1) : R) * risingFactorial x (j + 1) * risingFactorial y (r - j))
        + risingFactorial y (r + 1) := by
      rw [hB, sum_range_succ' (fun j =>
        (r.choose j : R) * risingFactorial x j * risingFactorial y (r - j + 1)) r]
      -- j = 0 term:  C(r,0) · 1 · y^{(r-0+1)} = y^{(r+1)}.
      simp only [Nat.choose_zero_right, Nat.cast_one, risingFactorial_zero, Nat.sub_zero,
        one_mul, mul_one]
      -- Reindex the shifted body:  r - (j+1) + 1 = r - j  for j < r, and pad range r → r+1.
      rw [sum_range_succ (fun j =>
        (r.choose (j + 1) : R) * risingFactorial x (j + 1) * risingFactorial y (r - j))]
      -- The added top term (j = r) carries C(r, r+1) = 0.
      rw [Nat.choose_succ_self, Nat.cast_zero]
      have hbody : ∀ j ∈ range r,
          (r.choose (j + 1) : R) * risingFactorial x (j + 1) *
              risingFactorial y (r - (j + 1) + 1)
            = (r.choose (j + 1) : R) * risingFactorial x (j + 1) * risingFactorial y (r - j) := by
        intro j hj
        rw [mem_range] at hj
        have : r - (j + 1) + 1 = r - j := by omega
        rw [this]
      rw [sum_congr rfl hbody]
      ring
    rw [hB']
    ring

/-! ### Falling-factorial companion via the reflection `x^{underline k} = (-1)^k (-x)^{(k)}`. -/

/-- Falling factorial of a ring element: `x^{underline k} = x·(x-1)···(x-k+1)`. -/
def fallingFactorial {R : Type*} [CommRing R] (x : R) : ℕ → R
  | 0     => 1
  | k + 1 => fallingFactorial x k * (x - k)

@[simp] lemma fallingFactorial_zero {R : Type*} [CommRing R] (x : R) :
    fallingFactorial x 0 = 1 := rfl

lemma fallingFactorial_succ {R : Type*} [CommRing R] (x : R) (k : ℕ) :
    fallingFactorial x (k + 1) = fallingFactorial x k * (x - k) := rfl

/-- Reflection identity: `x^{underline k} = (-1)^k · (-x)^{(k)}`. -/
lemma fallingFactorial_eq_neg_one_pow_mul_risingFactorial {R : Type*} [CommRing R]
    (x : R) (k : ℕ) :
    fallingFactorial x k = (-1) ^ k * risingFactorial (-x) k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [fallingFactorial_succ, ih, risingFactorial_succ, pow_succ]
    ring

/-- **Falling-factorial Vandermonde convolution over an arbitrary commutative ring.**
    `(x+y)^{underline r} = ∑_{j=0}^{r} C(r,j) · x^{underline j} · y^{underline (r-j)}`. -/
theorem fallingFactorial_add {R : Type*} [CommRing R] (x y : R) (r : ℕ) :
    fallingFactorial (x + y) r
      = ∑ j ∈ range (r + 1),
          (r.choose j : R) * fallingFactorial x j * fallingFactorial y (r - j) := by
  rw [fallingFactorial_eq_neg_one_pow_mul_risingFactorial, neg_add,
    risingFactorial_add, mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [mem_range, Nat.lt_succ_iff] at hj
  rw [fallingFactorial_eq_neg_one_pow_mul_risingFactorial x j,
    fallingFactorial_eq_neg_one_pow_mul_risingFactorial y (r - j)]
  -- Reassemble the sign: (-1)^r = (-1)^j · (-1)^(r-j) since j + (r-j) = r.
  have hpow : ((-1 : R)) ^ r = (-1) ^ j * (-1) ^ (r - j) := by
    rw [← pow_add, Nat.add_sub_cancel' hj]
  rw [hpow]
  ring

/-! ### Numerical corollary bridge: recover the parent's ℕ-valued identity. -/

/-- `risingFactorial (m : R) k` is the cast of the natural rising factorial `Nat.ascFactorial`.
    (`Nat.ascFactorial m k = m·(m+1)···(m+k-1)`.) -/
lemma risingFactorial_natCast {R : Type*} [CommRing R] (m k : ℕ) :
    risingFactorial (m : R) k = (m.ascFactorial k : R) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [risingFactorial_succ, ih, Nat.ascFactorial_succ]
    push_cast
    ring

end RisingFactorialVandermonde
