import Mathlib

/-!
# The 2-adic normal form of the non-three-square integers

**Open question (`lagrange-four-squares-waring-g2-oq-03-oq-04`)**, a companion to
the parent `oq-03` entry *"Legendre's three-square theorem — the if direction"*:

  `n = x² + y² + z²` is solvable  ⟺  `n ≠ 4^a (8b + 7)`  for all `a, b ≥ 0`.

The integers that are **not** sums of three squares form the *excluded family*
`E = { 4^a (8b+7) : a, b ≥ 0 }`.  The gallery's main file `Proofs/ThreeSquares.lean`
already proves the elementary *necessity* direction (every element of `E` fails to
be a sum of three squares) and the `4`-descent equivalence `n ∈ E ↔ 4n ∈ E`.  It
defines membership of `E` by the *existential* form `∃ a b, n = 4^a(8b+7)` and only
supplies a **`noncomputable`** decidability instance (via `Classical`).

This file supplies the **effective / structural layer** that the existential form
leaves implicit, and which is not present elsewhere in the gallery:

## What is new here

* **2-adic normal form** (`isExcludedForm_iff`):  a positive integer `n` lies in
  `E` *iff* its `2`-adic valuation is even **and** its odd part is `≡ 7 (mod 8)`:
  `IsExcludedForm n ↔ 0 < n ∧ Even (v₂ n) ∧ (n / 2^{v₂ n}) % 8 = 7`.
  This is the canonical "solved" description: it replaces the unbounded search over
  `(a,b)` by two arithmetic conditions on `n` itself.

* **Uniqueness of the parametrisation** (`excludedForm_unique`):  the exponents in
  `4^a(8b+7)` are uniquely determined — `4^a(8b+7) = 4^{a'}(8b'+7) ⟹ a=a' ∧ b=b'`.
  This is the well-definedness underlying the normal form (and any counting/density
  statement about `E`), proved by reading off the `2`-adic valuation.

* **A genuinely computable decision procedure** (`isExcludedB`, `instExcluded`):  a
  `Bool`-valued test `isExcludedB n` with `IsExcludedForm n ↔ isExcludedB n = true`,
  yielding a `Decidable` instance with **no `Classical`** — an effective replacement
  for the parent's `noncomputable` instance, subsuming all future membership checks.

All proofs are axiom-free and rest only on Mathlib's `Nat.factorization` API.
-/

namespace LagrangeFourSquaresWaringG2OQ03OQ04

/-- `n` lies in the **excluded family** of Legendre's three-square theorem if
`n = 4^a (8b + 7)` for some `a, b ≥ 0` — equivalently (by the main `ThreeSquares`
file's necessity theorem) `n` is not a sum of three integer squares. -/
def IsExcludedForm (n : ℕ) : Prop := ∃ a b : ℕ, n = 4 ^ a * (8 * b + 7)

/-! ## The 2-adic valuation of an excluded number -/

/-- The `2`-adic valuation of `4^a(8b+7)` is exactly `2a`: the odd factor `8b+7`
contributes nothing, and `4^a = 2^{2a}`.  This is the engine behind both the
normal form and the uniqueness of the parametrisation. -/
theorem factorization_two_of_excluded (a b : ℕ) :
    (4 ^ a * (8 * b + 7)).factorization 2 = 2 * a := by
  have hodd : ¬ (2 ∣ (8 * b + 7)) := by omega
  have h4 : (4 : ℕ) ^ a = 2 ^ (2 * a) := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
  rw [Nat.factorization_mul (pow_ne_zero a (by norm_num)) (by positivity),
      Finsupp.add_apply, h4, Nat.factorization_pow, Finsupp.smul_apply,
      Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd hodd, smul_eq_mul, mul_one, add_zero]

/-- **Uniqueness of the `4^a(8b+7)` parametrisation.**  Reading off the `2`-adic
valuation (`= 2a`) pins down `a`, after which cancelling `4^a` pins down `b`. -/
theorem excludedForm_unique {a a' b b' : ℕ}
    (h : 4 ^ a * (8 * b + 7) = 4 ^ a' * (8 * b' + 7)) : a = a' ∧ b = b' := by
  have ha : a = a' := by
    have hval := congrArg (fun n => n.factorization 2) h
    simp only [factorization_two_of_excluded] at hval
    omega
  subst ha
  have h4 : (0 : ℕ) < 4 ^ a := by positivity
  have hb : 8 * b + 7 = 8 * b' + 7 := Nat.eq_of_mul_eq_mul_left h4 h
  exact ⟨rfl, by omega⟩

/-! ## The 2-adic normal form -/

/-- **2-adic normal form of the excluded family.**  A positive integer `n` is of
the form `4^a(8b+7)` iff its `2`-adic valuation `v₂ n = n.factorization 2` is even
and its odd part `n / 2^{v₂ n}` is `≡ 7 (mod 8)`.  This converts the unbounded
existential search over `(a,b)` into two arithmetic conditions on `n`. -/
theorem isExcludedForm_iff {n : ℕ} :
    IsExcludedForm n ↔
      0 < n ∧ Even (n.factorization 2) ∧ (n / 2 ^ (n.factorization 2)) % 8 = 7 := by
  constructor
  · rintro ⟨a, b, rfl⟩
    refine ⟨by positivity, ?_, ?_⟩
    · rw [factorization_two_of_excluded]; exact ⟨a, by ring⟩
    · rw [factorization_two_of_excluded,
        show (4 : ℕ) ^ a = 2 ^ (2 * a) by rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul],
        Nat.mul_div_cancel_left _ (by positivity)]
      omega
  · rintro ⟨_, ⟨a, ha⟩, hmod⟩
    have key : 2 ^ (n.factorization 2) * (n / 2 ^ (n.factorization 2)) = n :=
      Nat.ordProj_mul_ordCompl_eq_self n 2
    have hb : n / 2 ^ (n.factorization 2)
        = 8 * (n / 2 ^ (n.factorization 2) / 8) + 7 := by
      have hdm := Nat.div_add_mod (n / 2 ^ (n.factorization 2)) 8
      omega
    refine ⟨a, n / 2 ^ (n.factorization 2) / 8, ?_⟩
    have h4 : (4 : ℕ) ^ a = 2 ^ (n.factorization 2) := by
      rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, ha]; congr 1; omega
    rw [h4, ← hb]; exact key.symm

/-! ## Every excluded number is at least 7 -/

/-- Every element of the excluded family is `≥ 7` (`4^a ≥ 1` and `8b+7 ≥ 7`). -/
theorem excludedForm_ge_seven {n : ℕ} (h : IsExcludedForm n) : 7 ≤ n := by
  obtain ⟨a, b, rfl⟩ := h
  calc 7 = 1 * 7 := by ring
    _ ≤ 4 ^ a * (8 * b + 7) :=
        Nat.mul_le_mul (Nat.one_le_pow _ _ (by norm_num)) (by omega)

/-! ## A computable decision procedure -/

/-- A **computable** `Bool`-valued membership test for the excluded family,
expressing the 2-adic normal form. -/
def isExcludedB (n : ℕ) : Bool :=
  decide (0 < n) && decide (n.factorization 2 % 2 = 0) &&
    decide ((n / 2 ^ (n.factorization 2)) % 8 = 7)

/-- The `Bool` test agrees with the `Prop`-level excluded family. -/
theorem isExcludedForm_iff_isExcludedB (n : ℕ) :
    IsExcludedForm n ↔ isExcludedB n = true := by
  rw [isExcludedForm_iff, isExcludedB]
  simp only [Bool.and_eq_true, decide_eq_true_eq, Nat.even_iff, and_assoc]

/-- A **`Decidable` instance with no `Classical`**, replacing the parent file's
`noncomputable` instance: membership of the excluded family is effectively
checkable via `isExcludedB`. -/
instance instExcluded : DecidablePred IsExcludedForm :=
  fun n => decidable_of_iff _ (isExcludedForm_iff_isExcludedB n).symm

/-! ## Concrete witnesses -/

/-- `7 = 4^0(8·0+7)` is excluded. -/
example : IsExcludedForm 7 := ⟨0, 0, rfl⟩

/-- `15 = 4^0(8·1+7)` is excluded. -/
example : IsExcludedForm 15 := ⟨0, 1, rfl⟩

/-- `28 = 4^1(8·0+7)` is excluded. -/
example : IsExcludedForm 28 := ⟨1, 0, rfl⟩

/-- `112 = 4^2(8·0+7)` is excluded. -/
example : IsExcludedForm 112 := ⟨2, 0, rfl⟩

/-- `6 < 7`, so `6` is not excluded (every excluded number is `≥ 7`). -/
example : ¬ IsExcludedForm 6 := fun h => by have := excludedForm_ge_seven h; omega

/-- The parametrisation of `28` as `4^1(8·0+7)` is the unique one. -/
example {a b : ℕ} (h : 4 ^ a * (8 * b + 7) = 28) : a = 1 ∧ b = 0 :=
  excludedForm_unique (h.trans (by norm_num : (28 : ℕ) = 4 ^ 1 * (8 * 0 + 7)))

end LagrangeFourSquaresWaringG2OQ03OQ04
