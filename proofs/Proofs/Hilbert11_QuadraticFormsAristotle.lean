/-
  Aristotle targets for Hilbert's 11th Problem: Quadratic Forms over Number Fields.
  Routine supporting lemmas for automated proof search.
  See Hilbert11_QuadraticForms.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main deep results (Hasse-Minkowski, Sylvester's law, Witt cancellation,
    Selmer counterexample, Hilbert reciprocity, Meyer's theorem)
  - Routine arithmetic on Mathlib's `QuadraticForm` API
  - Lagrange four-square corollaries on small inputs (via `Nat.sum_four_squares`)
  - Definitional unfolding of `IsIsotropic` / `IsAnisotropic` style predicates
  - Concrete `IsSquare` / parity / signature witnesses
  - No axioms, no definition sorries, no open conjectures
  - Block comments only (no `/-!` module docstrings -- Aristotle parser limitation)
-/
import Mathlib

namespace Hilbert11QuadraticFormsAristotle

open scoped BigOperators

/-
## Section 1: Isotropy predicates (definitional helpers)

The main file introduces `RepresentsZeroNontrivially Q := ∃ x, x ≠ 0 ∧ Q x = 0`.
We mirror that predicate here over Mathlib's `QuadraticForm` to expose the
definitional iff and basic monotonicity / negation lemmas that Aristotle can
attack without entering the axiom-laden main namespace.
-/

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- A quadratic form represents zero nontrivially: a nonzero vector mapped to 0. -/
def RepresentsZeroNontriv (Q : QuadraticForm R M) : Prop :=
  ∃ x : M, x ≠ 0 ∧ Q x = 0

/-- A quadratic form is isotropic iff it represents zero nontrivially. -/
def IsIsotropic (Q : QuadraticForm R M) : Prop := RepresentsZeroNontriv Q

/-- A quadratic form is anisotropic iff it does not represent zero nontrivially. -/
def IsAnisotropic (Q : QuadraticForm R M) : Prop := ¬ RepresentsZeroNontriv Q

theorem isIsotropic_iff (Q : QuadraticForm R M) :
    IsIsotropic Q ↔ ∃ x : M, x ≠ 0 ∧ Q x = 0 :=
  Iff.rfl

theorem isAnisotropic_iff (Q : QuadraticForm R M) :
    IsAnisotropic Q ↔ ∀ x : M, x ≠ 0 → Q x ≠ 0 := by
  unfold IsAnisotropic RepresentsZeroNontriv
  push_neg
  rfl

theorem isIsotropic_of_witness (Q : QuadraticForm R M) (x : M)
    (hx : x ≠ 0) (h0 : Q x = 0) : IsIsotropic Q :=
  ⟨x, hx, h0⟩

theorem not_anisotropic_of_isotropic (Q : QuadraticForm R M)
    (h : IsIsotropic Q) : ¬ IsAnisotropic Q := by
  intro hAni; exact hAni h

theorem isotropic_or_anisotropic (Q : QuadraticForm R M) :
    IsIsotropic Q ∨ IsAnisotropic Q := by
  classical
  by_cases h : RepresentsZeroNontriv Q
  · exact Or.inl h
  · exact Or.inr h

/-
## Section 2: Lagrange four-square witnesses (small inputs)

`Nat.sum_four_squares` from Mathlib guarantees every `n : ℕ` is a sum of four
integer squares. The main file already wraps this as `four_squares_connection`.
We expose explicit small-N witnesses Aristotle can verify with `decide` / `norm_num`.
-/

theorem four_squares_zero : ∃ a b c d : ℤ, (0 : ℕ) = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  refine ⟨0, 0, 0, 0, ?_⟩
  norm_num

theorem four_squares_one : ∃ a b c d : ℤ, (1 : ℕ) = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  refine ⟨1, 0, 0, 0, ?_⟩
  norm_num

theorem four_squares_two : ∃ a b c d : ℤ, (2 : ℕ) = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  refine ⟨1, 1, 0, 0, ?_⟩
  norm_num

theorem four_squares_three : ∃ a b c d : ℤ, (3 : ℕ) = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  refine ⟨1, 1, 1, 0, ?_⟩
  norm_num

theorem four_squares_four : ∃ a b c d : ℤ, (4 : ℕ) = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  refine ⟨2, 0, 0, 0, ?_⟩
  norm_num

theorem four_squares_seven : ∃ a b c d : ℤ, (7 : ℕ) = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  refine ⟨2, 1, 1, 1, ?_⟩
  norm_num

theorem four_squares_eight : ∃ a b c d : ℤ, (8 : ℕ) = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  refine ⟨2, 2, 0, 0, ?_⟩
  norm_num

/-- Generic existence: every `n : ℕ` is a sum of four integer squares.
This is the direct corollary of Mathlib's `Nat.sum_four_squares`. -/
theorem four_squares_generic (n : ℕ) :
    ∃ a b c d : ℤ, (n : ℤ) = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  obtain ⟨a, b, c, d, h⟩ := Nat.sum_four_squares n
  exact ⟨a, b, c, d, by exact_mod_cast h.symm⟩

/-- Extension to non-negative integers: any non-negative `m : ℤ` is a sum of four
integer squares. -/
theorem four_squares_nonneg_int (m : ℤ) (hm : 0 ≤ m) :
    ∃ a b c d : ℤ, m = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  sorry

/-- The sum of four integer squares is always non-negative. -/
theorem sum_four_squares_nonneg (a b c d : ℤ) :
    0 ≤ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  sorry

/-- A negative integer is not a sum of four integer squares. -/
theorem not_four_squares_of_neg (m : ℤ) (hm : m < 0) :
    ¬ ∃ a b c d : ℤ, m = a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 := by
  sorry

/-
## Section 3: Hyperbolicity parity facts

The main file defines `IsHyperbolic` requiring `Even n` and the existence of an
isomorphism with `m` hyperbolic planes. We expose the parity side conditions
on small dimensions -- routine `Nat.Even` facts.
-/

theorem even_zero : Even (0 : ℕ) := ⟨0, rfl⟩
theorem even_two : Even (2 : ℕ) := ⟨1, rfl⟩
theorem even_four : Even (4 : ℕ) := ⟨2, rfl⟩
theorem even_six : Even (6 : ℕ) := ⟨3, rfl⟩
theorem even_eight : Even (8 : ℕ) := ⟨4, rfl⟩

theorem not_even_one : ¬ Even (1 : ℕ) := by decide
theorem not_even_three : ¬ Even (3 : ℕ) := by decide
theorem not_even_five : ¬ Even (5 : ℕ) := by decide
theorem not_even_seven : ¬ Even (7 : ℕ) := by decide

/-- Hyperbolic-plane dimension witness: `2 * m = 2m`. -/
theorem two_mul_witness (m : ℕ) : ∃ n : ℕ, 2 * m = n :=
  ⟨2 * m, rfl⟩

/-- Even iff doubling: `n` is even iff `n = 2 * m` for some `m`. -/
theorem even_iff_exists_two_mul (n : ℕ) : Even n ↔ ∃ m : ℕ, n = 2 * m := by
  refine ⟨fun h => ?_, fun ⟨m, hm⟩ => ?_⟩
  · obtain ⟨k, hk⟩ := h
    exact ⟨k, by omega⟩
  · exact ⟨m, by omega⟩

/-
## Section 4: Real signature arithmetic

`RealSignature` in the main file has fields `positive` and `negative : ℕ`.
Sylvester's law of inertia (axiomatized in main) gives `positive + negative ≤ n`.
We expose closed-form arithmetic Aristotle can verify.
-/

structure Signature where
  positive : ℕ
  negative : ℕ
  deriving DecidableEq

def Signature.total (s : Signature) : ℕ := s.positive + s.negative

theorem Signature.total_def (s : Signature) :
    s.total = s.positive + s.negative := rfl

theorem Signature.total_le_iff (s : Signature) (n : ℕ) :
    s.total ≤ n ↔ s.positive + s.negative ≤ n := Iff.rfl

/-- Definite positive: signature `(n, 0)`. -/
def Signature.posDef (n : ℕ) : Signature := ⟨n, 0⟩

/-- Definite negative: signature `(0, n)`. -/
def Signature.negDef (n : ℕ) : Signature := ⟨0, n⟩

/-- Hyperbolic plane: signature `(1, 1)`. -/
def Signature.hyperbolic : Signature := ⟨1, 1⟩

theorem Signature.posDef_total (n : ℕ) : (Signature.posDef n).total = n := by
  simp [Signature.total, Signature.posDef]

theorem Signature.negDef_total (n : ℕ) : (Signature.negDef n).total = n := by
  simp [Signature.total, Signature.negDef]

theorem Signature.hyperbolic_total : Signature.hyperbolic.total = 2 := by
  simp [Signature.total, Signature.hyperbolic]

theorem Signature.posDef_indefinite_iff (n : ℕ) :
    (Signature.posDef n).negative = 0 := rfl

theorem Signature.negDef_indefinite_iff (n : ℕ) :
    (Signature.negDef n).positive = 0 := rfl

/-- Indefinite signature has both positive and negative parts. -/
def Signature.IsIndefinite (s : Signature) : Prop :=
  0 < s.positive ∧ 0 < s.negative

theorem Signature.hyperbolic_isIndefinite : Signature.hyperbolic.IsIndefinite := by
  refine ⟨?_, ?_⟩ <;> decide

theorem Signature.posDef_not_isIndefinite (n : ℕ) :
    ¬ (Signature.posDef n).IsIndefinite := by
  rintro ⟨_, h⟩; exact absurd h (by decide)

theorem Signature.negDef_not_isIndefinite (n : ℕ) :
    ¬ (Signature.negDef n).IsIndefinite := by
  rintro ⟨h, _⟩; exact absurd h (by decide)

/-
## Section 5: Hilbert symbol arithmetic on the placeholder definition

The main file defines `HilbertSymbol a b p := 1` as a placeholder. Until the
genuine Hilbert symbol is formalized, the placeholder is constant, which makes
the product formula (Hilbert reciprocity) vacuously trivial. We expose the
arithmetic in a small namespace Aristotle can verify.

For the actual Hilbert symbol facts (when Mathlib formalizes it), Aristotle
will not be able to discharge them -- those belong to the main statement.
-/

/-- Placeholder Hilbert symbol, matching the main file's definition. -/
def hilbertPlaceholder (_a _b : ℚ) (_p : ℕ) : ℤ := 1

theorem hilbertPlaceholder_const (a b : ℚ) (p : ℕ) :
    hilbertPlaceholder a b p = 1 := rfl

theorem hilbertPlaceholder_symm (a b : ℚ) (p : ℕ) :
    hilbertPlaceholder a b p = hilbertPlaceholder b a p := rfl

theorem hilbertPlaceholder_mul (a b : ℚ) (p : ℕ) :
    hilbertPlaceholder a b p * hilbertPlaceholder b a p = 1 := by
  simp [hilbertPlaceholder]

theorem hilbertPlaceholder_pos (a b : ℚ) (p : ℕ) :
    0 < hilbertPlaceholder a b p := by
  simp [hilbertPlaceholder]

/-
## Section 6: Conditional consequences of Hasse-Minkowski

Given the iff direction of Hasse-Minkowski as a hypothesis, we can derive
specific consequences. These are conditional theorems -- Aristotle does NOT
attempt to prove the main iff, only the routine derivations.
-/

variable {n : ℕ}

/-- Conditional: if a quadratic form is isotropic, then a witness exists
(this is just definitional unfolding). -/
theorem isotropic_witness_exists {Q : QuadraticForm ℚ (Fin n → ℚ)}
    (h : IsIsotropic Q) : ∃ x : Fin n → ℚ, x ≠ 0 ∧ Q x = 0 := h

/-- Conditional: if no nonzero vector is killed by `Q`, then `Q` is anisotropic. -/
theorem anisotropic_of_no_zero {Q : QuadraticForm ℚ (Fin n → ℚ)}
    (h : ∀ x : Fin n → ℚ, x ≠ 0 → Q x ≠ 0) : IsAnisotropic Q := by
  intro ⟨x, hx, h0⟩
  exact h x hx h0

/-- Conditional: anisotropic forms have no nontrivial zero. -/
theorem anisotropic_no_zero {Q : QuadraticForm ℚ (Fin n → ℚ)}
    (h : IsAnisotropic Q) : ∀ x : Fin n → ℚ, x ≠ 0 → Q x ≠ 0 := by
  intro x hx h0
  exact h ⟨x, hx, h0⟩

/-
## Section 7: Sanity numerics for low-dimension cases
-/

theorem dim_two_witness_pos : (2 : ℕ) > 0 := by decide
theorem dim_three_witness_pos : (3 : ℕ) > 0 := by decide
theorem dim_four_witness_pos : (4 : ℕ) > 0 := by decide
theorem dim_five_witness_pos : (5 : ℕ) > 0 := by decide

theorem dim_five_ge_two : (5 : ℕ) ≥ 2 := by decide
theorem dim_five_ge_three : (5 : ℕ) ≥ 3 := by decide
theorem dim_five_ge_four : (5 : ℕ) ≥ 4 := by decide

end Hilbert11QuadraticFormsAristotle
