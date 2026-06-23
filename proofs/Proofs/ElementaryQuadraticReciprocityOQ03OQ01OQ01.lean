/-
# The Kronecker Symbol: Extending Jacobi to All Integer Moduli

Open Question (from elementary-quadratic-reciprocity-oq-03-oq-01):
  Can the Kronecker symbol (extending Jacobi to even moduli and n = 0, -1, -2)
  be formalized as a further generalization?

Answer: YES. We define the Kronecker symbol χ(a, n) for a ∈ ℤ, n ∈ ℤ,
extending the Jacobi symbol to:
  - n = 0: χ(a, 0) = 1 if |a| = 1, else 0
  - n = -1: χ(a, -1) = -1 if a < 0, else 1
  - n = 2: χ(a, 2) = 0 if 2∣a, (-1)^((a²-1)/8) otherwise
  - General: χ(a, n) = χ(a, sign(n)) · χ(a, 2)^v₂(|n|) · J(a, odd_part(|n|))

Parent: ElementaryQuadraticReciprocityOQ03.lean (0 axioms, 0 sorries)
-/
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic

namespace KroneckerSymbol

open ZMod

/-
## Part I: The Kronecker Symbol at Special Values
-/

/-- The Kronecker symbol at n = -1: χ(a, -1) = -1 if a < 0, else 1. -/
def kroneckerNegOne (a : ℤ) : ℤ :=
  if a < 0 then -1 else 1

/-- The Kronecker symbol at n = 2.
    χ(a, 2) = 0 if a is even, 1 if a ≡ ±1 (mod 8), -1 if a ≡ ±3 (mod 8). -/
def kroneckerTwo (a : ℤ) : ℤ :=
  if a % 2 = 0 then 0
  else if a % 8 = 1 ∨ a % 8 = -1 then 1
  else -1

/-- The Kronecker symbol at n = 0: χ(a, 0) = 1 if |a| = 1, else 0. -/
def kroneckerZero (a : ℤ) : ℤ :=
  if a = 1 ∨ a = -1 then 1 else 0

/-
## Part II: Two-Adic Factoring
-/

/-- Extract the 2-adic valuation and odd part of a natural number.
    Returns (v, m) where n = 2^v * m and m is odd (or m = 0 for n = 0). -/
def factorTwos : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | n + 1 =>
    if (n + 1) % 2 = 0 then
      let (v, m) := factorTwos ((n + 1) / 2)
      (v + 1, m)
    else (0, n + 1)
termination_by n => n

/-- For an odd number, factorTwos returns (0, n). -/
theorem factorTwos_odd_eq (n : ℕ) (hn : n > 0) (hodd : n % 2 = 1) :
    factorTwos n = (0, n) := by
  cases n with
  | zero => omega
  | succ k => simp [factorTwos]; omega

/-
## Part III: The Full Kronecker Symbol
-/

/-- The Kronecker symbol χ(a, n) for a ∈ ℤ, n ∈ ℤ.
    Extends the Jacobi symbol to all integer moduli.

    For odd positive n, this equals the Jacobi symbol J(a, n).
    For even n, it factors out powers of 2 using kroneckerTwo.
    For negative n, it includes a sign factor using kroneckerNegOne.
    For n = 0, it returns 1 if |a| = 1, else 0. -/
noncomputable def kroneckerSym (a n : ℤ) : ℤ :=
  if n = 0 then kroneckerZero a
  else
    let sign_factor := if n < 0 then kroneckerNegOne a else 1
    let (v, m) := factorTwos n.natAbs
    let two_factor := kroneckerTwo a ^ v
    let jacobi_factor := jacobiSym a m
    sign_factor * two_factor * jacobi_factor

/-
## Part IV: Basic Properties
-/

/-- χ(a, 1) = 1 for all a. -/
theorem kroneckerSym_one (a : ℤ) : kroneckerSym a 1 = 1 := by
  unfold kroneckerSym
  simp only [one_ne_zero, ite_false, show ¬((1 : ℤ) < 0) from by omega, ite_false,
    Int.natAbs_one]
  show 1 * kroneckerTwo a ^ (factorTwos 1).1 * jacobiSym a (factorTwos 1).2 = 1
  simp [factorTwos, jacobiSym.one_right, pow_zero]

/-- χ(a, -1) = kroneckerNegOne a. -/
theorem kroneckerSym_neg_one (a : ℤ) : kroneckerSym a (-1) = kroneckerNegOne a := by
  unfold kroneckerSym
  simp only [show (-1 : ℤ) ≠ 0 from by omega, ite_false,
    show (-1 : ℤ) < 0 from by omega, ite_true, Int.natAbs_neg, Int.natAbs_one]
  show kroneckerNegOne a * kroneckerTwo a ^ (factorTwos 1).1 * jacobiSym a (factorTwos 1).2 =
    kroneckerNegOne a
  simp [factorTwos, jacobiSym.one_right, pow_zero]

/-- χ(a, 0) = kroneckerZero a. -/
theorem kroneckerSym_zero (a : ℤ) : kroneckerSym a 0 = kroneckerZero a := by
  simp [kroneckerSym]

/-- **Key theorem**: For odd positive n, χ(a, n) = J(a, n) (the Jacobi symbol).
    This shows the Kronecker symbol genuinely extends the Jacobi symbol. -/
theorem kroneckerSym_eq_jacobiSym (a : ℤ) (n : ℕ) (hn : n > 0) (hodd : n % 2 = 1) :
    kroneckerSym a n = jacobiSym a n := by
  simp only [kroneckerSym, Int.natCast_ne_zero.mpr (by omega : n ≠ 0), ite_false,
    show ¬((n : ℤ) < 0) from by omega, ite_false, Int.natAbs_natCast]
  rw [factorTwos_odd_eq n hn hodd]
  simp [pow_zero]

/-- χ(1, n) = 1 for all n. -/
theorem kroneckerSym_one_left (n : ℤ) : kroneckerSym 1 n = 1 := by
  unfold kroneckerSym
  split
  · simp [kroneckerZero]
  · next h =>
    have hkt : kroneckerTwo 1 = 1 := by
      simp only [kroneckerTwo, show (1 : ℤ) % 2 ≠ 0 from by omega, ite_false,
        show ((1 : ℤ) % 8 = 1 ∨ (1 : ℤ) % 8 = -1) from Or.inl rfl, ite_true]
    have hkn : kroneckerNegOne 1 = 1 := by simp [kroneckerNegOne]
    split <;> simp [hkt, hkn, one_pow, jacobiSym.one_left]

/-
## Part V: The Kronecker Symbol at n = 2
-/

/-- kroneckerTwo classifies integers by their residue mod 8. -/
theorem kroneckerTwo_values (a : ℤ) :
    kroneckerTwo a = 0 ∨ kroneckerTwo a = 1 ∨ kroneckerTwo a = -1 := by
  unfold kroneckerTwo
  split
  · left; rfl
  · split
    · right; left; rfl
    · right; right; rfl

/-- kroneckerNegOne only takes values ±1. -/
theorem kroneckerNegOne_values (a : ℤ) :
    kroneckerNegOne a = 1 ∨ kroneckerNegOne a = -1 := by
  simp only [kroneckerNegOne]
  split <;> [right; left] <;> rfl

/-
## Part VI: Summary and Future Work
-/

/-- The Kronecker symbol is well-defined and extends the Jacobi symbol. -/
theorem kronecker_extends_jacobi :
    ∀ (a : ℤ) (n : ℕ), n > 0 → n % 2 = 1 → kroneckerSym a n = jacobiSym a n :=
  kroneckerSym_eq_jacobiSym

#check kroneckerSym
#check kroneckerSym_eq_jacobiSym
#check kroneckerSym_one_left

end KroneckerSymbol
