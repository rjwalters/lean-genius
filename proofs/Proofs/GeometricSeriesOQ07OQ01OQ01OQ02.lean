/-
# Geometric series, open question oq-07-oq-01-oq-01-oq-02:
# The Eulerian polynomial is palindromic — the Eulerian numbers are symmetric

The parent entry `geometric-series-oq-07-oq-01-oq-01` builds the **Eulerian
polynomial** `eulerPoly m` by its classical first-order differential recurrence

  E₀ = 1,   E_{m+1} = X·(1-X)·E'ₘ + (m+1)·X·Eₘ,

and identifies it (Frobenius' identity) with the Stirling closed form.  Its
integer coefficients are the Eulerian numbers: in this "geometric" normalisation
`E_m(X) = ∑_{k=1}^{m} ⟨m,k-1⟩·Xᵏ` for `m ≥ 1`, with

  E₁ = X,   E₂ = X + X²,   E₃ = X + 4X² + X³.

This entry answers the parent's recorded open question
`geometric-series-oq-07-oq-01-oq-01-oq-02`: prove the **palindromic symmetry**
`⟨m,k⟩ = ⟨m,m-1-k⟩` of the Eulerian numbers, equivalently
`Eₘ(X) = X^{m+1}·Eₘ(1/X)` for `m ≥ 1`.

We work entirely at the level of coefficients over an arbitrary commutative ring.
The engine is a **coefficient recurrence** extracted from the differential
recurrence by coefficient extraction:

  coeff(E_{m+1}, j+2) = (j+2)·coeff(Eₘ, j+2) − (j+1)·coeff(Eₘ, j+1)
                          + (m+1)·coeff(Eₘ, j+1),

together with the boundary values `coeff(E_{m+1}, 0) = 0` and
`coeff(E_{m+1}, 1) = coeff(Eₘ, 1) + (m+1)·coeff(Eₘ, 0)`.  From these we prove, by
induction on `m`, the symmetric statement

  `eulerPoly_palindrome` :  a + b = m + 1  →  coeff(Eₘ, a) = coeff(Eₘ, b)   (m ≥ 1),

which is exactly palindromicity (`eulerPoly_coeff_symm`:
`coeff(Eₘ, a) = coeff(Eₘ, m+1-a)`).  As corollaries we read off the extreme
Eulerian numbers `⟨m,0⟩ = ⟨m,m-1⟩ = 1` (`eulerPoly_coeff_one`,
`eulerPoly_coeff_self`), the degree `deg Eₘ = m` and monicity
(`eulerPoly_natDegree`, `eulerPoly_monic`), all for `m ≥ 1`.

Mathlib has no Eulerian numbers or polynomials, so the symmetry — a textbook
structural fact (Concrete Mathematics) — is new here.  Everything is `0`-axiom
(`propext` / `Classical.choice` / `Quot.sound` only) and `sorry`-free.
-/
import Mathlib
import Proofs.GeometricSeriesOQ07OQ01OQ01

namespace GeometricSeriesOQ07OQ01OQ01OQ02

open Polynomial Finset

open GeometricSeriesOQ07OQ01OQ01 (eulerPoly eulerPoly_zero eulerPoly_succ eulerPoly_one)

variable {R : Type*} [CommRing R]

/-! ## Part 1: the coefficient recurrence for `eulerPoly`

Coefficient extraction turns the differential recurrence
`E_{m+1} = X·(1-X)·E'ₘ + (m+1)·X·Eₘ` into a recurrence on coefficients.  Because
`X` and `X²` shift indices, the three index regions `j = 0`, `j = 1`,
`j ≥ 2` are handled separately. -/

/-- Rewriting `(↑m + 1 : R[X])` as the constant polynomial `C (↑m + 1)`. -/
private theorem natCast_add_one_eq_C (m : ℕ) : ((m : R[X]) + 1) = C ((m : R) + 1) := by
  rw [map_add, map_natCast, map_one]

/-- Boundary value: the constant coefficient of `E_{m+1}` vanishes (every term of
the recurrence carries a factor `X`). -/
theorem coeff_eulerPoly_succ_zero (m : ℕ) :
    (eulerPoly (m + 1) : R[X]).coeff 0 = 0 := by
  rw [coeff_zero_eq_eval_zero, eulerPoly_succ]
  simp

/-- The constant coefficient of `Eₘ` vanishes for `m ≥ 1`. -/
theorem coeff_eulerPoly_zero_eq_zero {m : ℕ} (hm : 1 ≤ m) :
    (eulerPoly m : R[X]).coeff 0 = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  exact coeff_eulerPoly_succ_zero n

/-- Boundary value at index `1`. -/
theorem coeff_eulerPoly_succ_one (m : ℕ) :
    (eulerPoly (m + 1) : R[X]).coeff 1
      = (eulerPoly m).coeff 1 + ((m : R) + 1) * (eulerPoly m).coeff 0 := by
  have hcomm : ((m : R[X]) + 1) * X * eulerPoly m
      = X * (((m : R[X]) + 1) * eulerPoly m) := by ring
  have hassoc : (X * (1 - X) * derivative (eulerPoly m) : R[X])
      = X * ((1 - X) * derivative (eulerPoly m)) := by ring
  rw [eulerPoly_succ, hassoc, hcomm, coeff_add]
  rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_X_mul, coeff_X_mul]
  rw [mul_coeff_zero, natCast_add_one_eq_C, coeff_C_mul, coeff_derivative]
  simp [coeff_one, coeff_X]

/-- The core coefficient recurrence at index `j + 2`. -/
theorem coeff_eulerPoly_succ_add_two (m j : ℕ) :
    (eulerPoly (m + 1) : R[X]).coeff (j + 2)
      = (eulerPoly m).coeff (j + 2) * ((j : R) + 2)
        - (eulerPoly m).coeff (j + 1) * ((j : R) + 1)
        + ((m : R) + 1) * (eulerPoly m).coeff (j + 1) := by
  have hsplit : (X * (1 - X) * derivative (eulerPoly m) : R[X])
      = X * derivative (eulerPoly m) - X ^ 2 * derivative (eulerPoly m) := by ring
  have hcomm : ((m : R[X]) + 1) * X * eulerPoly m
      = X * (((m : R[X]) + 1) * eulerPoly m) := by ring
  have e1 : (X * derivative (eulerPoly m) : R[X]).coeff (j + 2)
      = (eulerPoly m).coeff (j + 2) * ((j : R) + 2) := by
    rw [show j + 2 = (j + 1) + 1 from rfl, coeff_X_mul, coeff_derivative]
    push_cast; ring
  have e2 : (X ^ 2 * derivative (eulerPoly m) : R[X]).coeff (j + 2)
      = (eulerPoly m).coeff (j + 1) * ((j : R) + 1) := by
    rw [coeff_X_pow_mul, coeff_derivative]
  have e3 : (X * (((m : R[X]) + 1) * eulerPoly m) : R[X]).coeff (j + 2)
      = ((m : R) + 1) * (eulerPoly m).coeff (j + 1) := by
    rw [show j + 2 = (j + 1) + 1 from rfl, coeff_X_mul, natCast_add_one_eq_C, coeff_C_mul]
  rw [eulerPoly_succ, hsplit, hcomm, coeff_add, coeff_sub, e1, e2, e3]

/-! ## Part 2: degree bound -/

/-- The Eulerian polynomial `Eₘ` has degree at most `m`: its coefficients vanish
above index `m`. -/
theorem coeff_eulerPoly_eq_zero {m j : ℕ} (h : m < j) :
    (eulerPoly m : R[X]).coeff j = 0 := by
  induction m generalizing j with
  | zero =>
    rw [eulerPoly_zero, coeff_one, if_neg (by omega)]
  | succ n ih =>
    obtain ⟨j', rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    rw [coeff_eulerPoly_succ_add_two]
    rw [ih (by omega), ih (by omega)]
    ring

/-! ## Part 3: palindromicity -/

/-- **Palindromicity of the Eulerian polynomial** (symmetric form).  For `m ≥ 1`,
the coefficients of `eulerPoly m` are symmetric about `(m+1)/2`:
`a + b = m + 1` implies `coeff(Eₘ, a) = coeff(Eₘ, b)`.  Equivalently the Eulerian
numbers satisfy `⟨m,k⟩ = ⟨m,m-1-k⟩`. -/
theorem eulerPoly_palindrome {m : ℕ} (hm : 1 ≤ m) :
    ∀ a b : ℕ, a + b = m + 1 → (eulerPoly m : R[X]).coeff a = (eulerPoly m).coeff b := by
  induction m, hm using Nat.le_induction with
  | base =>
    intro a b hab
    rw [eulerPoly_one, coeff_X, coeff_X]
    split_ifs <;> first | rfl | (exfalso; omega)
  | succ n hn ih =>
    -- ordered helper: prove the statement assuming `a ≤ b`, then close by symmetry.
    have key : ∀ a b : ℕ, a + b = n + 2 → a ≤ b →
        (eulerPoly (n + 1) : R[X]).coeff a = (eulerPoly (n + 1)).coeff b := by
      intro a b hab hle
      match a, b with
      | 0, b =>
        -- b = n + 2 : both sides vanish (constant term, and above the degree)
        rw [coeff_eulerPoly_succ_zero, coeff_eulerPoly_eq_zero (by omega)]
      | 1, b =>
        -- b = n + 1 : the two boundary values, equated through the IH `coeff 1 = coeff n`
        obtain rfl : b = n + 1 := by omega
        obtain ⟨n', rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        rw [coeff_eulerPoly_succ_one, coeff_eulerPoly_zero_eq_zero (by omega : 1 ≤ n' + 1),
          mul_zero, add_zero]
        -- normalise the index `n'+1+1` to the `_ + 2` form expected by the recurrence
        show (eulerPoly (n' + 1) : R[X]).coeff 1
          = (eulerPoly (n' + 1 + 1)).coeff (n' + 2)
        rw [coeff_eulerPoly_succ_add_two,
          coeff_eulerPoly_eq_zero (show n' + 1 < n' + 2 by omega)]
        -- now relate coeff(Eₙ, 1) and coeff(Eₙ, n) by the inner palindrome
        rw [ih 1 (n' + 1) (by omega)]
        push_cast; ring
      | (a + 2), (b + 2) =>
        -- interior: both via the core recurrence, then the IH pairs the coefficients
        rw [coeff_eulerPoly_succ_add_two, coeff_eulerPoly_succ_add_two]
        have hrel : a + b + 2 = n := by omega
        rw [ih (a + 2) (b + 1) (by omega), ih (a + 1) (b + 2) (by omega)]
        have hc : ((a : R) + (b : R) + 2) = (n : R) := by exact_mod_cast congrArg (Nat.cast) hrel
        linear_combination
          ((eulerPoly n : R[X]).coeff (b + 1) - (eulerPoly n).coeff (b + 2)) * hc
    intro a b hab
    rcases le_total a b with h | h
    · exact key a b hab h
    · exact (key b a (by omega) h).symm

/-- **Palindromicity** (reflection form).  For `m ≥ 1`,
`coeff(Eₘ, a) = coeff(Eₘ, m + 1 - a)` for every `a`. -/
theorem eulerPoly_coeff_symm {m : ℕ} (hm : 1 ≤ m) (a : ℕ) :
    (eulerPoly m : R[X]).coeff a = (eulerPoly m).coeff (m + 1 - a) := by
  rcases le_or_gt a (m + 1) with h | h
  · exact eulerPoly_palindrome hm a (m + 1 - a) (by omega)
  · -- a > m + 1 : LHS = 0 (above degree), RHS = coeff 0 = 0 (m ≥ 1)
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    rw [coeff_eulerPoly_eq_zero (by omega), show n + 1 + 1 - a = 0 from by omega,
      coeff_eulerPoly_succ_zero]

/-! ## Part 4: structural corollaries (`m ≥ 1`) -/

/-- The first Eulerian number is `⟨m,0⟩ = 1`: `coeff(Eₘ, 1) = 1`. -/
theorem eulerPoly_coeff_one {m : ℕ} (hm : 1 ≤ m) :
    (eulerPoly m : R[X]).coeff 1 = 1 := by
  induction m, hm using Nat.le_induction with
  | base => rw [eulerPoly_one, coeff_X]; simp
  | succ n hn ih =>
    rw [coeff_eulerPoly_succ_one, coeff_eulerPoly_zero_eq_zero hn, mul_zero, add_zero, ih]

/-- The leading Eulerian number is `⟨m,m-1⟩ = 1`: `coeff(Eₘ, m) = 1`.  Read off
from palindromicity and `coeff(Eₘ, 1) = 1`. -/
theorem eulerPoly_coeff_self {m : ℕ} (hm : 1 ≤ m) :
    (eulerPoly m : R[X]).coeff m = 1 := by
  rw [eulerPoly_coeff_symm hm m, show m + 1 - m = 1 from by omega, eulerPoly_coeff_one hm]

/-- For `m ≥ 1` over a nontrivial ring, `eulerPoly m` has degree exactly `m`. -/
theorem eulerPoly_natDegree [Nontrivial R] {m : ℕ} (hm : 1 ≤ m) :
    (eulerPoly m : R[X]).natDegree = m := by
  refine le_antisymm (natDegree_le_iff_coeff_eq_zero.mpr ?_)
    (le_natDegree_of_ne_zero ?_)
  · intro j hj
    exact coeff_eulerPoly_eq_zero hj
  · rw [eulerPoly_coeff_self hm]
    exact one_ne_zero

/-- For `m ≥ 1` over a nontrivial ring, `eulerPoly m` is monic. -/
theorem eulerPoly_monic [Nontrivial R] {m : ℕ} (hm : 1 ≤ m) :
    (eulerPoly m : R[X]).Monic := by
  rw [Monic, leadingCoeff, eulerPoly_natDegree hm, eulerPoly_coeff_self hm]

/-! ## Part 5: low-order sanity checks (the symmetric rows `1`, `1 4 1`) -/

example : (eulerPoly 2 : ℤ[X]).coeff 1 = (eulerPoly 2 : ℤ[X]).coeff 2 :=
  eulerPoly_palindrome (by norm_num) 1 2 rfl

example : (eulerPoly 3 : ℤ[X]).coeff 1 = (eulerPoly 3 : ℤ[X]).coeff 3 :=
  eulerPoly_palindrome (by norm_num) 1 3 rfl

end GeometricSeriesOQ07OQ01OQ01OQ02
