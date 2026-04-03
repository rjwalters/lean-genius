import Mathlib
import Proofs.DeMoivreOQ02

/-
Chebyshev Composition Monoid Structure (de-moivre-oq-02-oq-01)

Open question from DeMoivreOQ02: Prove that the Chebyshev polynomial map
n ↦ T_n formalizes as a monoid homomorphism under composition.

**Main Result**: `T_mul` (Mathlib): T R (m * n) = (T R m).comp (T R n)

This gives the Chebyshev polynomials a monoid structure under composition:
  - Identity: T_1 = X (the identity polynomial for composition)
  - Operation: T_m ∘ T_n = T_{mn}  (multiplication of indices)
  - Commutativity: T_m ∘ T_n = T_n ∘ T_m
  - Associativity: (T_l ∘ T_m) ∘ T_n = T_l ∘ (T_m ∘ T_n)

The proof uses Mathlib's `Polynomial.Chebyshev.T_mul` and `T_mul_T`, which
establish these identities algebraically (induction via the Chebyshev recurrence),
without requiring trigonometric parametrization.

**Status**: 0 sorries, 0 axioms. All results derived from Mathlib.
-/

open Polynomial Polynomial.Chebyshev Real BigOperators

namespace DeMoivreOQ02OQ01

variable (R : Type*) [CommRing R]

/-!
## Section I: Polynomial Composition Identity (from Mathlib)
-/

/-- **Chebyshev Composition**: T_m ∘ T_n = T_{mn} as polynomials over any commutative ring.

    This is `Polynomial.Chebyshev.T_mul` from Mathlib, proved algebraically by induction
    on the Chebyshev recurrence T_{n+2} = 2X·T_{n+1} - T_n, using the product identity
    `T_mul_T`: 2·T_m·T_n = T_{m+n} + T_{m-n}. No trigonometry needed. -/
theorem chebyshev_comp_eq (m n : ℤ) :
    (T R m).comp (T R n) = T R (m * n) :=
  (T_mul R m n).symm

/-- **Product-to-Sum Identity**: 2·T_m·T_n = T_{m+n} + T_{m-n} as polynomial identity.

    This is `Polynomial.Chebyshev.T_mul_T` from Mathlib. Proved algebraically
    by induction; coincides with the trigonometric identity
    2·cos(mθ)·cos(nθ) = cos((m+n)θ) + cos((m-n)θ) when evaluated at cos θ. -/
theorem chebyshev_product_to_sum_poly (m k : ℤ) :
    2 * T R m * T R k = T R (m + k) + T R (m - k) :=
  T_mul_T R m k

/-!
## Section II: Monoid Axioms
-/

/-- T_1 = X is the identity for polynomial composition (left). -/
theorem chebyshev_one_comp (n : ℤ) : (T R 1).comp (T R n) = T R n := by
  rw [T_one, Polynomial.X_comp]

/-- T_1 = X is the identity for polynomial composition (right). -/
theorem chebyshev_comp_one (n : ℤ) : (T R n).comp (T R 1) = T R n := by
  rw [T_one, Polynomial.comp_X]

/-- Chebyshev composition is commutative: T_m ∘ T_n = T_n ∘ T_m. -/
theorem chebyshev_comp_comm (m n : ℤ) :
    (T R m).comp (T R n) = (T R n).comp (T R m) := by
  rw [chebyshev_comp_eq, chebyshev_comp_eq, mul_comm]

/-- Chebyshev composition is associative. -/
theorem chebyshev_comp_assoc (l m n : ℤ) :
    ((T R l).comp (T R m)).comp (T R n) = (T R l).comp ((T R m).comp (T R n)) := by
  rw [chebyshev_comp_eq, chebyshev_comp_eq, chebyshev_comp_eq, chebyshev_comp_eq, mul_assoc]

/-!
## Section III: Evaluation Consequences
-/

/-- Composition at cos inputs: T_m(T_n(cos θ)) = T_{mn}(cos θ). -/
theorem chebyshev_comp_cos (m n : ℤ) (θ : ℝ) :
    (T ℝ m).eval ((T ℝ n).eval (Real.cos θ)) = (T ℝ (m * n)).eval (Real.cos θ) := by
  rw [← Polynomial.eval_comp, chebyshev_comp_eq]

/-- Double angle: T_2(T_n(cos θ)) = T_{2n}(cos θ). -/
theorem chebyshev_double_angle (n : ℤ) (θ : ℝ) :
    (T ℝ 2).eval ((T ℝ n).eval (Real.cos θ)) = (T ℝ (2 * n)).eval (Real.cos θ) :=
  chebyshev_comp_cos 2 n θ

/-- Squaring index: T_n(T_n(cos θ)) = T_{n²}(cos θ). -/
theorem chebyshev_square_index (n : ℤ) (θ : ℝ) :
    (T ℝ n).eval ((T ℝ n).eval (Real.cos θ)) = (T ℝ (n * n)).eval (Real.cos θ) :=
  chebyshev_comp_cos n n θ

/-!
## Section IV: Concrete Polynomial Verifications
-/

/-- T_2 ∘ T_3 = T_6 as polynomials. -/
example : (T ℝ 2).comp (T ℝ 3) = T ℝ 6 := chebyshev_comp_eq ℝ 2 3

/-- T_2 ∘ T_5 = T_5 ∘ T_2 (commutativity). -/
example : (T ℝ 2).comp (T ℝ 5) = (T ℝ 5).comp (T ℝ 2) :=
  chebyshev_comp_comm ℝ 2 5

/-- T_{-3} ∘ T_4 = T_{-12} = T_{12} (since T_{-n} = T_n). -/
example : (T ℝ (-3)).comp (T ℝ 4) = T ℝ 12 := by
  rw [chebyshev_comp_eq, show (-3 : ℤ) * 4 = -12 from by norm_num, T_neg]

/-!
## Section V: Monoid Homomorphism Statement
-/

/-- **Monoid Homomorphism**: The map n ↦ T n is a multiplicative monoid homomorphism
    from (ℤ, *, 1) to polynomial endomorphisms under composition.

    Formally: the composition map (m, n) ↦ (T R m).comp (T R n) equals
    (m, n) ↦ T R (m * n), so T_ respects the monoid structure of ℤ. -/
theorem chebyshev_monoid_hom (m n : ℤ) :
    (T R m).comp (T R n) = T R (m * n) ∧
    (T R 1).comp (T R n) = T R n ∧
    (T R n).comp (T R 1) = T R n :=
  ⟨chebyshev_comp_eq R m n,
   chebyshev_one_comp R n,
   chebyshev_comp_one R n⟩

/-- **Summary**: Chebyshev polynomials of the first kind form a commutative monoid
    under polynomial composition, with T_1 = X as the identity. The map n ↦ T_n
    is a monoid homomorphism from (ℤ, ·, 1) to (R[X], ∘, X):
      - T_m ∘ T_n = T_{mn}    (homomorphism property)
      - T_1 ∘ T_n = T_n ∘ T_1 = T_n   (identity)
      - T_m ∘ T_n = T_n ∘ T_m  (commutativity)
    The product identity 2·T_m·T_n = T_{m+n} + T_{m-n} is the key algebraic engine. -/
theorem demoivre_oq02_oq01_summary (l m n : ℤ) (θ : ℝ) :
    -- Composition identity (polynomial)
    ((T R m).comp (T R n) = T R (m * n)) ∧
    -- Commutativity
    ((T R m).comp (T R n) = (T R n).comp (T R m)) ∧
    -- Associativity
    (((T R l).comp (T R m)).comp (T R n) = (T R l).comp ((T R m).comp (T R n))) ∧
    -- Evaluation at cos θ
    ((T ℝ m).eval ((T ℝ n).eval (Real.cos θ)) = (T ℝ (m * n)).eval (Real.cos θ)) :=
  ⟨chebyshev_comp_eq R m n,
   chebyshev_comp_comm R m n,
   chebyshev_comp_assoc R l m n,
   chebyshev_comp_cos m n θ⟩

end DeMoivreOQ02OQ01
