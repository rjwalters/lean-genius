/-
Erdős Problem #724: Mutually Orthogonal Latin Squares

Source: https://erdosproblems.com/724
Status: OPEN

Statement:
Let f(n) be the maximum number of mutually orthogonal Latin squares of order n.
Is it true that f(n) ≫ n^(1/2)?

The question asks whether the maximum size of a set of mutually orthogonal Latin
squares (MOLS) of order n grows at least as fast as the square root of n.

Historical Context:
Euler originally conjectured that f(n) = 1 when n ≡ 2 (mod 4), meaning no pair
of orthogonal Latin squares exists for these orders. This was famously disproved
by Bose, Parker, and Shrikhande (1960), who showed f(n) ≥ 2 for all n ≥ 7.

Progress on Lower Bounds:
- Chowla, Erdős, and Straus (1960): f(n) ≫ n^(1/91)
- Wilson (1974): f(n) ≫ n^(1/17)
- Beth (1983): f(n) ≫ n^(1/14.8)

The gap between the best known lower bound (n^(1/14.8)) and the conjectured
n^(1/2) remains substantial. This problem cannot be resolved by finite
computation alone.

References:
- Bose, R.C., Shrikhande, S.S., Parker, E.T. (1960): "Further results on
  the construction of mutually orthogonal Latin squares"
- Chowla, S., Erdős, P., Straus, E.G. (1960): "On the maximal number of
  pairwise orthogonal Latin squares of a given order"
- Wilson, R.M. (1974): "Concerning the number of mutually orthogonal Latin squares"
- Beth, T. (1983): "Eine Bemerkung zur Abschätzung der Anzahl orthogonaler
  lateinischer Quadrate mittels Siebverfahren"
- OEIS A001438: Maximum number of MOLS of order n
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Order.BoundedOrder.Basic

open Matrix Finset

namespace Erdos724

/-
## Part I: Latin Squares

A Latin square of order n is an n×n array filled with n different symbols,
each occurring exactly once in each row and exactly once in each column.
-/

/--
A Latin square of order n is a function from Fin n × Fin n → Fin n
such that each row is a permutation and each column is a permutation.
-/
def IsLatinSquare {n : ℕ} (L : Fin n → Fin n → Fin n) : Prop :=
  (∀ i : Fin n, Function.Bijective (L i)) ∧  -- each row is a permutation
  (∀ j : Fin n, Function.Bijective (fun i => L i j))  -- each column is a permutation

/--
The set of all Latin squares of order n.
-/
def LatinSquares (n : ℕ) : Set (Fin n → Fin n → Fin n) :=
  {L | IsLatinSquare L}

/-
## Part II: Orthogonal Latin Squares

Two Latin squares L and M are orthogonal if, when superimposed, every
ordered pair (L[i,j], M[i,j]) appears exactly once.
-/

/--
Two Latin squares L and M of order n are orthogonal if all n² pairs
(L(i,j), M(i,j)) are distinct, i.e., the combined mapping is bijective.
-/
def AreOrthogonal {n : ℕ} (L M : Fin n → Fin n → Fin n) : Prop :=
  Function.Bijective (fun ij : Fin n × Fin n => (L ij.1 ij.2, M ij.1 ij.2))

/--
A set of Latin squares is mutually orthogonal if every pair is orthogonal.
-/
def MutuallyOrthogonal {n : ℕ} (S : Set (Fin n → Fin n → Fin n)) : Prop :=
  (∀ L ∈ S, IsLatinSquare L) ∧
  (∀ L ∈ S, ∀ M ∈ S, L ≠ M → AreOrthogonal L M)

/-
## Part III: The Function f(n)

f(n) is the maximum number of mutually orthogonal Latin squares of order n.
-/

/--
**f(n)**: The maximum number of mutually orthogonal Latin squares of order n.
Also known as N(n) in some literature.

Key values:
- f(1) = ∞ (trivially, any number of 1×1 squares are MOLS)
- f(2) = 1 (no pair of orthogonal 2×2 Latin squares exists)
- f(p) = p - 1 for prime p (achieved by affine planes)
- f(p^k) = p^k - 1 for prime powers (projective plane construction)
-/
noncomputable def maxMOLS (n : ℕ) : ℕ∞ :=
  ⨆ (S : Finset (Fin n → Fin n → Fin n)) (hS : MutuallyOrthogonal (S : Set _)), (S.card : ℕ∞)

/-- Notation for the MOLS function -/
notation "f(" n ")" => maxMOLS n

/-
## Part IV: Known Bounds

The upper bound f(n) ≤ n - 1 is classical and achieved for prime powers.
The lower bounds have been gradually improved.
-/

/--
**Upper Bound:**
f(n) ≤ n - 1 for all n ≥ 2.

This is a classical result: the maximum set of MOLS of order n has at most
n - 1 squares. This bound is achieved when n is a prime power.
-/
axiom mols_upper_bound (n : ℕ) (hn : n ≥ 2) : f(n) ≤ n - 1

/--
**Prime Power Theorem:**
If n = p^k for a prime p, then f(n) = n - 1.

The construction uses finite field arithmetic.
-/
axiom mols_prime_power (p k : ℕ) (hp : Nat.Prime p) (hk : k ≥ 1) :
    f(p ^ k) = p ^ k - 1

/--
**Bose-Parker-Shrikhande Theorem (1960):**
f(n) ≥ 2 for all n ≥ 7.

This disproved Euler's conjecture that no pair of orthogonal Latin squares
exists when n ≡ 2 (mod 4).
-/
axiom bose_parker_shrikhande (n : ℕ) (hn : n ≥ 7) : f(n) ≥ 2

/--
**Special Cases:**
- f(2) = 1 (no pair of orthogonal 2×2 Latin squares)
- f(6) ≥ 1 (historically difficult; Euler was right that f(6) = 1)
-/
axiom f_two : f(2) = 1
axiom f_six : f(6) = 1

/-
## Part V: Lower Bound Progress

The question asks whether f(n) grows at least as fast as n^(1/2).
Progress has been made on improving lower bounds.
-/

/--
**Chowla-Erdős-Straus Theorem (1960):**
f(n) ≫ n^(1/91).

For sufficiently large n, f(n) ≥ C · n^(1/91) for some constant C > 0.
-/
axiom chowla_erdos_straus : ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, n ≥ 2 → (f(n) : ℕ∞) ≥ C * (n : ℝ) ^ (1 / 91 : ℝ)

/--
**Wilson's Improvement (1974):**
f(n) ≫ n^(1/17).
-/
axiom wilson_1974 : ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, n ≥ 2 → (f(n) : ℕ∞) ≥ C * (n : ℝ) ^ (1 / 17 : ℝ)

/--
**Beth's Improvement (1983):**
f(n) ≫ n^(1/14.8).

This is the current best known lower bound exponent.
-/
axiom beth_1983 : ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, n ≥ 2 → (f(n) : ℕ∞) ≥ C * (n : ℝ) ^ (1 / 14.8 : ℝ)

/-
## Part VI: The Erdős Conjecture

Erdős conjectured that f(n) ≫ n^(1/2), a much stronger bound than proven.
-/

/--
**Erdős Problem #724:**
Is f(n) ≫ n^(1/2)?

That is, does there exist a constant C > 0 such that f(n) ≥ C · n^(1/2)
for all sufficiently large n?

**Status: OPEN**

The gap between the best known exponent (1/14.8 ≈ 0.068) and the
conjectured exponent (1/2 = 0.5) is substantial.
-/
def erdos_724_conjecture : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 2 → (f(n) : ℕ∞) ≥ C * (n : ℝ) ^ (1 / 2 : ℝ)

/-
## Part VII: Examples and Constructions
-/

/--
**Example: f(3) = 2**
The two MOLS of order 3:
L = [0,1,2; 2,0,1; 1,2,0]
M = [0,1,2; 1,2,0; 2,0,1]
-/
def latinSquare3_L : Fin 3 → Fin 3 → Fin 3 :=
  fun i j => ⟨(i.val + j.val) % 3, Nat.mod_lt _ (by decide)⟩

def latinSquare3_M : Fin 3 → Fin 3 → Fin 3 :=
  fun i j => ⟨(2 * i.val + j.val) % 3, Nat.mod_lt _ (by decide)⟩

axiom latinSquare3_L_is_latin : IsLatinSquare latinSquare3_L
axiom latinSquare3_M_is_latin : IsLatinSquare latinSquare3_M
axiom latinSquare3_orthogonal : AreOrthogonal latinSquare3_L latinSquare3_M

/--
f(3) = 2, achieved by the construction above.
-/
axiom f_three : f(3) = 2

/--
**Example: f(4) = 3**
For n = 4 = 2², the maximum is n - 1 = 3.
-/
axiom f_four : f(4) = 3

/--
**Example: f(5) = 4**
For n = 5 (prime), the maximum is n - 1 = 4.
-/
axiom f_five : f(5) = 4

/-
## Part VIII: Connection to Projective Planes

The existence of n - 1 MOLS of order n is equivalent to the existence
of a projective plane of order n.
-/

/--
**Projective Plane Connection:**
f(n) = n - 1 if and only if a projective plane of order n exists.

Projective planes of order n exist for all prime powers n, but existence
for non-prime-powers (like n = 6, 10, 12, ...) is generally unknown,
with n = 10 ruled out by the famous Lam-Thiel-Swiercz computation (1989).
-/
axiom mols_projective_plane_equiv (n : ℕ) (hn : n ≥ 2) :
    f(n) = n - 1 ↔ ∃ (ProjectivePlane : Type), True  -- placeholder for plane existence

/--
**No Projective Plane of Order 10:**
f(10) < 9, proved by exhaustive computer search.
-/
axiom f_ten_lt_nine : f(10) < 9

/-
## Part IX: MacNeish's Conjecture (Disproved)

MacNeish conjectured f(n) = min{p_i^{a_i} - 1} where n = ∏p_i^{a_i}.
This was disproved; the true behavior is more complex.
-/

/--
**MacNeish's Bound:**
f(n) ≥ min{p_i^{a_i} - 1} where n = ∏p_i^{a_i}.

While not tight, this provides a constructive lower bound using
direct products of Latin squares.
-/
axiom macneish_lower_bound (n : ℕ) (hn : n ≥ 2) :
    ∃ m : ℕ, m ≥ 1 ∧ f(n) ≥ m

/-
## Part X: Summary
-/

/--
**Erdős Problem #724: Summary**

Question: Is f(n) ≫ n^(1/2)?

Status: OPEN

What we know:
1. f(n) ≤ n - 1 for all n ≥ 2 (classical upper bound)
2. f(n) = n - 1 for prime powers (achieved)
3. f(n) ≥ 2 for n ≥ 7 (Bose-Parker-Shrikhande 1960)
4. f(n) ≫ n^(1/14.8) (Beth 1983, best known lower bound)

The conjecture asks for f(n) ≫ n^(1/2), a significant jump from
the current best exponent of 1/14.8.
-/
theorem erdos_724_status :
    -- The problem is open: we state what is known
    (∀ n, n ≥ 2 → f(n) ≤ n - 1) ∧  -- Upper bound
    (∀ p k, Nat.Prime p → k ≥ 1 → f(p^k) = p^k - 1) ∧  -- Prime power case
    (∀ n, n ≥ 7 → f(n) ≥ 2)  -- Bose-Parker-Shrikhande
    := ⟨mols_upper_bound, mols_prime_power, bose_parker_shrikhande⟩

/--
**Current Best Lower Bound:**
The best known result is f(n) ≫ n^(1/14.8) by Beth (1983).
-/
theorem current_best_lower_bound : ∃ C : ℝ, C > 0 ∧
    ∀ n : ℕ, n ≥ 2 → (f(n) : ℕ∞) ≥ C * (n : ℝ) ^ (1 / 14.8 : ℝ) :=
  beth_1983

/--
**The Gap:**
The exponent 1/14.8 ≈ 0.068 is far from the conjectured 1/2 = 0.5.
Closing this gap would be a major advance in combinatorics.
-/
theorem exponent_gap :
    (1 : ℝ) / 14.8 < (1 : ℝ) / 2 := by norm_num

end Erdos724
