/-
  Vandermonde Convolution for Rising Factorials (Binomial-Type Property)

  Open Question (arithmetic-series-oq-02-oq-04-oq-01-oq-01):
    #2 "Prove the multiset Vandermonde / Chu-Vandermonde identity in
        rising-factorial form."
    #3 "Relate the rising factorial to Mathlib's general ascending Pochhammer
        (ascPochhammer) over a commutative ring and recover this ℕ identity as
        a specialization."

  This file answers BOTH at once.

  Main result (over any commutative semiring S, x y : S):

    (x + y)^{(k)} = ∑_{m=0}^{k} C(k,m) · x^{(m)} · y^{(k-m)}

  where z^{(j)} = z(z+1)···(z+j-1) is the rising factorial, realized as
  `(ascPochhammer S j).eval z`.  Equivalently: the sequence of rising-factorial
  polynomials `{x^{(k)}}` is a SEQUENCE OF BINOMIAL TYPE (an Appell/umbral
  binomial theorem).  Mathlib has the *compositional* product law
  `ascPochhammer_mul` but not this additive (Vandermonde) convolution.

  Specializing S = ℕ, x = a, y = b recovers the multiset / Chu-Vandermonde
  identity for `Nat.ascFactorial`:

    (a+b).ascFactorial k = ∑_{m=0}^{k} a.ascFactorial m · b.ascFactorial (k-m) · C(k,m).

  Proof: induction on k mirroring Mathlib's `Commute.add_pow` (the binomial
  theorem).  The recurrence `ascPochhammer_succ_eval`
    `(ascPochhammer S (n+1)).eval z = (ascPochhammer S n).eval z * (z + n)`
  plays the role of `pow_succ`; the index-dependent shift `(z + n)` is absorbed
  by a Pascal-rule step `Nat.choose_succ_succ` with a single case split.

  Status: 0 axioms, 0 sorries, no native_decide.

  Parent:      ArithmeticSeriesOQ02OQ04OQ01OQ01.lean (multiset coefficient · k! = rising factorial)
  Grandparent: ArithmeticSeriesOQ02OQ04OQ01.lean (descending factorial)
-/

import Mathlib

namespace ArithmeticSeriesOQ02OQ04OQ01OQ01OQ02

open Finset Polynomial

-- ============================================================
-- Part I: The Rising-Factorial Vandermonde Convolution (CommSemiring)
-- ============================================================

/-- **Vandermonde convolution for rising factorials.**

Over any commutative semiring `S`, the rising-factorial polynomial sequence
`x^{(k)} = (ascPochhammer S k).eval x` is of *binomial type*:

  `(x + y)^{(k)} = ∑_{m=0}^{k} C(k,m) · x^{(m)} · y^{(k-m)}`.

This is the additive (Chu-Vandermonde) analogue of the multiplicative
composition law `ascPochhammer_mul`, and is not in Mathlib.  The proof mirrors
the binomial theorem `Commute.add_pow`, using `ascPochhammer_succ_eval` as the
analogue of `pow_succ`. -/
theorem ascPochhammer_eval_add {S : Type*} [CommSemiring S] (x y : S) (k : ℕ) :
    (ascPochhammer S k).eval (x + y) =
      ∑ m ∈ range (k + 1),
        (ascPochhammer S m).eval x * (ascPochhammer S (k - m)).eval y * (k.choose m : S) := by
  -- summand
  let t : ℕ → ℕ → S := fun n m =>
    (ascPochhammer S m).eval x * (ascPochhammer S (n - m)).eval y * (n.choose m : S)
  change (ascPochhammer S k).eval (x + y) = ∑ m ∈ range (k + 1), t k m
  -- recurrences (analogue of `pow_succ`)
  have hAx : ∀ m : ℕ, (ascPochhammer S (m + 1)).eval x
      = (ascPochhammer S m).eval x * (x + (m : S)) := fun m => ascPochhammer_succ_eval m x
  have hBy : ∀ m : ℕ, (ascPochhammer S (m + 1)).eval y
      = (ascPochhammer S m).eval y * (y + (m : S)) := fun m => ascPochhammer_succ_eval m y
  have hCxy : ∀ m : ℕ, (ascPochhammer S (m + 1)).eval (x + y)
      = (ascPochhammer S m).eval (x + y) * ((x + y) + (m : S)) :=
    fun m => ascPochhammer_succ_eval m (x + y)
  -- boundary values of the summand
  have h_first : ∀ n : ℕ, t n 0 = (ascPochhammer S n).eval y := by
    intro n
    simp only [t, ascPochhammer_zero, eval_one, Nat.sub_zero, Nat.choose_zero_right,
      Nat.cast_one, one_mul, mul_one]
  have h_last : ∀ n : ℕ, t n (n + 1) = 0 := by
    intro n
    simp only [t, Nat.choose_succ_self, Nat.cast_zero, mul_zero]
  -- Pascal step: relate level n+1 to level n
  have h_middle : ∀ n i : ℕ, i ≤ n →
      t (n + 1) (i + 1)
        = (x + (i : S)) * t n i + (y + ((n - (i + 1) : ℕ) : S)) * t n (i + 1) := by
    intro n i hi
    have hsub : n + 1 - (i + 1) = n - i := by omega
    dsimp only [t]
    rw [hsub, Nat.choose_succ_succ', Nat.cast_add, mul_add]
    congr 1
    · rw [hAx i]; ring
    · by_cases h_eq : i = n
      · subst h_eq
        simp [Nat.choose_succ_self]
      · have hni : n - i = (n - (i + 1)) + 1 := by omega
        rw [hni, hBy (n - (i + 1))]; ring
  -- main induction
  induction k with
  | zero =>
    rw [Finset.sum_range_one]
    simp [t, ascPochhammer_zero]
  | succ n ih =>
    -- LHS: expand the recurrence and the inductive hypothesis
    rw [hCxy n, ih, Finset.sum_mul]
    -- per-term split of the (constant) factor (x+y)+n on the LHS
    have hsplit : ∀ m : ℕ, m ∈ range (n + 1) →
        t n m * ((x + y) + (n : S))
          = (x + (m : S)) * t n m + (y + ((n - m : ℕ) : S)) * t n m := by
      intro m hm
      have hmn : m ≤ n := Finset.mem_range_succ_iff.mp hm
      have hcast : (n : S) = (m : S) + ((n - m : ℕ) : S) := by
        have hmm : m + (n - m) = n := by omega
        rw [← Nat.cast_add, hmm]
      rw [hcast]; ring
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    -- RHS: expand the top sum via the Pascal step
    rw [Finset.sum_range_succ' (fun m => t (n + 1) m) (n + 1)]
    rw [h_first (n + 1),
        Finset.sum_congr rfl
          (fun i hi => h_middle n i (Finset.mem_range_succ_iff.mp hi)),
        Finset.sum_add_distrib]
    -- the "x" sums coincide; the remaining "y" identity:
    have hQ :
        (∑ m ∈ range (n + 1), (y + ((n - m : ℕ) : S)) * t n m)
          = (∑ i ∈ range (n + 1), (y + ((n - (i + 1) : ℕ) : S)) * t n (i + 1))
            + (ascPochhammer S (n + 1)).eval y := by
      rw [Finset.sum_range_succ' (fun m => (y + ((n - m : ℕ) : S)) * t n m) n,
          Finset.sum_range_succ (fun i => (y + ((n - (i + 1) : ℕ) : S)) * t n (i + 1)) n]
      rw [h_last n, h_first n, hBy n, Nat.sub_zero]
      ring
    rw [hQ]; ring

-- ============================================================
-- Part II: ℕ Specialization — Chu-Vandermonde for `Nat.ascFactorial`
-- ============================================================

/-- **Multiset / Chu-Vandermonde identity for rising factorials over ℕ.**

  `(a+b)^{(k)} = ∑_{m=0}^{k} C(k,m) · a^{(m)} · b^{(k-m)}`

stated with Mathlib's `Nat.ascFactorial`.  This is the recorded open question's
multiset Vandermonde identity in rising-factorial form, obtained as the `S = ℕ`,
`x = a`, `y = b` specialization of `ascPochhammer_eval_add`. -/
theorem ascFactorial_add_vandermonde (a b k : ℕ) :
    (a + b).ascFactorial k
      = ∑ m ∈ range (k + 1), a.ascFactorial m * b.ascFactorial (k - m) * k.choose m := by
  have h := ascPochhammer_eval_add (a : ℕ) (b : ℕ) k
  simpa only [ascPochhammer_nat_eq_ascFactorial, Nat.cast_id] using h

/-- The same identity written with explicit rising products
    `n^{(j)} = ∏ i in range j, (n + i)`. -/
theorem ascFactorial_add_vandermonde_prod (a b k : ℕ) :
    (a + b).ascFactorial k
      = ∑ m ∈ range (k + 1),
          (∏ i ∈ range m, (a + i)) * (∏ i ∈ range (k - m), (b + i)) * k.choose m := by
  rw [ascFactorial_add_vandermonde]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Nat.ascFactorial_eq_prod_range a m, Nat.ascFactorial_eq_prod_range b (k - m)]

-- ============================================================
-- Part III: Structural Corollaries
-- ============================================================

/-- **Absorption at `b = 0`.** Since `0^{(j)} = 0` for `j ≥ 1` and `0^{(0)} = 1`,
    the convolution collapses to its `m = k` term, recovering `a^{(k)} = a^{(k)}`.
    A consistency check that the boundary is handled uniformly. -/
theorem ascFactorial_add_vandermonde_zero_right (a k : ℕ) :
    (a + 0).ascFactorial k
      = ∑ m ∈ range (k + 1), a.ascFactorial m * (0 : ℕ).ascFactorial (k - m) * k.choose m :=
  ascFactorial_add_vandermonde a 0 k

/-- **Symmetry (commutativity of `+`).** Swapping `a` and `b` reindexes the sum
    `m ↦ k - m`; the convolution is symmetric, as `(a+b) = (b+a)`. -/
theorem ascFactorial_add_vandermonde_symm (a b k : ℕ) :
    (∑ m ∈ range (k + 1), a.ascFactorial m * b.ascFactorial (k - m) * k.choose m)
      = ∑ m ∈ range (k + 1), b.ascFactorial m * a.ascFactorial (k - m) * k.choose m := by
  rw [← ascFactorial_add_vandermonde a b k, ← ascFactorial_add_vandermonde b a k, Nat.add_comm]

-- ============================================================
-- Part IV: Concrete Verification (decide — no native_decide)
-- ============================================================

/-- `a=b=1, k=2`: `(2)^{(2)} = 2·3 = 6`, and the RHS is `2+2+2 = 6`. -/
theorem check_a1_b1_k2 :
    (1 + 1 : ℕ).ascFactorial 2
      = ∑ m ∈ range 3, (1 : ℕ).ascFactorial m * (1 : ℕ).ascFactorial (2 - m) * (2).choose m := by
  decide

/-- `a=2, b=1, k=2`: `(3)^{(2)} = 3·4 = 12`. -/
theorem check_a2_b1_k2 :
    (2 + 1 : ℕ).ascFactorial 2
      = ∑ m ∈ range 3, (2 : ℕ).ascFactorial m * (1 : ℕ).ascFactorial (2 - m) * (2).choose m := by
  decide

/-- `a=1, b=2, k=3`: `(3)^{(3)} = 3·4·5 = 60`. -/
theorem check_a1_b2_k3 :
    (1 + 2 : ℕ).ascFactorial 3
      = ∑ m ∈ range 4, (1 : ℕ).ascFactorial m * (2 : ℕ).ascFactorial (3 - m) * (3).choose m := by
  decide

/-
  Summary

  Rising factorials form a sequence of binomial type:

    Part I   - ascPochhammer_eval_add:            (x+y)^{(k)} = ∑ C(k,m) x^{(m)} y^{(k-m)}   [CommSemiring]
    Part II  - ascFactorial_add_vandermonde:      ℕ specialization with Nat.ascFactorial
               ascFactorial_add_vandermonde_prod: explicit rising-product form
    Part III - ..._zero_right / ..._symm:         boundary collapse and a↔b symmetry
    Part IV  - decide checks

  The headline is the additive (Chu-Vandermonde) companion to Mathlib's
  multiplicative `ascPochhammer_mul`; it answers open questions #2 and #3 of the
  parent multiset-coefficient entry. 0 axioms / 0 sorries / no native_decide.
-/

end ArithmeticSeriesOQ02OQ04OQ01OQ01OQ02
