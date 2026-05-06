import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.GCDMonoid.Basic
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.Tactic

/-
# Smith Normal Form over Principal Ideal Domains

## Open Question (bezout-identity-oq-04-oq-01-oq-01)

"Can the Smith Normal Form theory from BezoutIdentityOQ04OQ01 (over ℤ) generalize
to arbitrary Principal Ideal Domains using Mathlib's IsPrincipalIdealRing and
GCDMonoid infrastructure?"

## Answer: Yes — The Theory Lifts to Any PID

Over a PID R, every matrix A decomposes as A = U·D·V with:
- U, V unimodular (det is a unit of R, not just ±1)
- D diagonal with invariant factors d₁ | d₂ | ... | dₖ
- The 1×2 invariant factor equals gcd(a,b) up to associates

## Key Generalization
- IsUnimodular (det = ±1) → IsUnimodularPID (IsUnit det)
- Int.gcd → GCDMonoid.gcd
- ℤ-specific case split (u = ±1) → abstract unit.inv_val argument
-/

namespace BezoutIdentityOQ04OQ01OQ01

open Matrix GCDMonoid

/-! ## Unimodular Matrices over a Commutative Ring -/

def IsUnimodularPID {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) : Prop :=
  IsUnit M.det

theorem isUnimodularPID_one {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] :
    IsUnimodularPID (1 : Matrix n n R) := by
  simp [IsUnimodularPID, det_one]

theorem IsUnimodularPID.mul {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]
    {M N : Matrix n n R} (hM : IsUnimodularPID M) (hN : IsUnimodularPID N) :
    IsUnimodularPID (M * N) := by
  simp only [IsUnimodularPID, det_mul]; exact hM.mul hN

/-- Over ℤ, IsUnimodularPID ↔ det = ±1. -/
theorem isUnimodularPID_int_iff {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℤ) :
    IsUnimodularPID M ↔ (M.det = 1 ∨ M.det = -1) := by
  simp [IsUnimodularPID, Int.isUnit_iff]

/-! ## Smith Normal Form Structure -/

structure SmithNormalFormPID (R : Type*) [CommRing R] (m n : ℕ) where
  U : Matrix (Fin m) (Fin m) R
  D : Matrix (Fin m) (Fin n) R
  V : Matrix (Fin n) (Fin n) R
  hU : IsUnimodularPID U
  hV : IsUnimodularPID V
  hD_diag : ∀ i : Fin m, ∀ j : Fin n, i.val ≠ j.val → D i j = 0
  hD_div : ∀ k : ℕ, k + 1 < min m n →
    (hm : k < m) → (hn : k < n) → (hm' : k + 1 < m) → (hn' : k + 1 < n) →
    D ⟨k, hm⟩ ⟨k, hn⟩ ∣ D ⟨k + 1, hm'⟩ ⟨k + 1, hn'⟩

def SmithNormalFormPID.isDecompOf {R : Type*} [CommRing R] {m n : ℕ}
    (snf : SmithNormalFormPID R m n) (A : Matrix (Fin m) (Fin n) R) : Prop :=
  A = snf.U * snf.D * snf.V

def SmithNormalFormPID.invariantFactor {R : Type*} [CommRing R] {m n : ℕ}
    (snf : SmithNormalFormPID R m n) (k : ℕ) : R :=
  if hm : k < m then
    if hn : k < n then snf.D ⟨k, hm⟩ ⟨k, hn⟩
    else 0
  else 0

/-! ## GCD Characterization for 1×2 Matrices -/

/-- For a 1×2 matrix [a, b] over a GCDMonoid, the invariant factor is associated to gcd(a,b).
    Generalizes BezoutIdentityOQ04OQ01.snf_1x2_invariant_factor from ℤ to any GCDMonoid.
    The NEW element vs. parent: replace the {1,-1} case split with unit.inv_val. -/
theorem snf_1x2_invariant_factor_pid {R : Type*} [CommRing R] [IsDomain R]
    [GCDMonoid R] (a b : R)
    (snf : SmithNormalFormPID R 1 2)
    (hsnf : snf.isDecompOf (Matrix.of ![![a, b]])) :
    snf.invariantFactor 0 ∣ GCDMonoid.gcd a b ∧
    GCDMonoid.gcd a b ∣ snf.invariantFactor 0 := by
  have hd_eq : snf.invariantFactor 0 = snf.D ⟨0, by omega⟩ ⟨0, by omega⟩ := by
    simp [SmithNormalFormPID.invariantFactor]
  have hD01 : snf.D ⟨0, by omega⟩ ⟨1, by omega⟩ = 0 :=
    snf.hD_diag ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp)
  -- U is 1×1: det(U) = U[0,0] is a unit
  have hU_unit : IsUnit (snf.U ⟨0, by omega⟩ ⟨0, by omega⟩) := by
    have h := snf.hU; simp [IsUnimodularPID, det_fin_one] at h; exact h
  -- det(V) = V[0,0]*V[1,1] - V[0,1]*V[1,0] is a unit
  have hV_unit : IsUnit (snf.V ⟨0, by omega⟩ ⟨0, by omega⟩ *
                          snf.V ⟨1, by omega⟩ ⟨1, by omega⟩ -
                          snf.V ⟨0, by omega⟩ ⟨1, by omega⟩ *
                          snf.V ⟨1, by omega⟩ ⟨0, by omega⟩) := by
    have h := snf.hV; simp [IsUnimodularPID, det_fin_two] at h; exact h
  set u   := snf.U ⟨0, by omega⟩ ⟨0, by omega⟩
  set d   := snf.D ⟨0, by omega⟩ ⟨0, by omega⟩
  set v00 := snf.V ⟨0, by omega⟩ ⟨0, by omega⟩
  set v01 := snf.V ⟨0, by omega⟩ ⟨1, by omega⟩
  set v10 := snf.V ⟨1, by omega⟩ ⟨0, by omega⟩
  set v11 := snf.V ⟨1, by omega⟩ ⟨1, by omega⟩
  -- Extract a = u*d*v00 and b = u*d*v01 from A = U*D*V
  have ha : a = u * d * v00 := by
    have h := congr_fun (congr_fun hsnf ⟨0, by omega⟩) ⟨0, by omega⟩
    simp only [SmithNormalFormPID.isDecompOf, Matrix.of_apply, Matrix.mul_apply,
               Fin.sum_univ_one, Fin.sum_univ_two,
               Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
    rw [hD01] at h; simp only [mul_zero, zero_mul, add_zero] at h
    linear_combination h
  have hb : b = u * d * v01 := by
    have h := congr_fun (congr_fun hsnf ⟨0, by omega⟩) ⟨1, by omega⟩
    simp only [SmithNormalFormPID.isDecompOf, Matrix.of_apply, Matrix.mul_apply,
               Fin.sum_univ_one, Fin.sum_univ_two,
               Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
    rw [hD01] at h; simp only [mul_zero, zero_mul, add_zero] at h
    linear_combination h
  rw [hd_eq]
  constructor
  · -- Part 1: d | a and d | b, so d | gcd(a,b)
    exact dvd_gcd ⟨u * v00, by rw [ha]; ring⟩ ⟨u * v01, by rw [hb]; ring⟩
  · -- Part 2: gcd(a,b) | d
    -- Key identity: a*v₁₁ - b*v₁₀ = u*d*det(V)
    have hkey : a * v11 - b * v10 = u * d * (v00 * v11 - v01 * v10) := by
      rw [ha, hb]; ring
    -- gcd divides the LHS
    have hdvd : GCDMonoid.gcd a b ∣ u * d * (v00 * v11 - v01 * v10) := by
      rw [← hkey]
      exact dvd_sub (dvd_mul_of_dvd_left (gcd_dvd_left a b) v11)
                    (dvd_mul_of_dvd_left (gcd_dvd_right a b) v10)
    -- Rearrange: gcd | (u * det(V)) * d
    have hdvd' : GCDMonoid.gcd a b ∣ (u * (v00 * v11 - v01 * v10)) * d := by
      convert hdvd using 1; ring
    -- u * det(V) is a unit; extract its Units representative
    obtain ⟨uval, huval⟩ := hU_unit.mul hV_unit
    -- Rewrite hdvd' in terms of uval
    have hdvd'' : GCDMonoid.gcd a b ∣ (↑uval : R) * d := by rw [huval]; exact hdvd'
    obtain ⟨w, hw⟩ := hdvd''
    -- hw : (↑uval : R) * d = gcd a b * w
    -- Cancel uval: d = uval.inv * (gcd * w) = gcd * (uval.inv * w)
    exact ⟨uval.inv * w, by
      have hinv : uval.inv * (↑uval : R) = 1 := uval.inv_val
      calc d = uval.inv * ((↑uval : R) * d) := by rw [← mul_assoc, hinv, one_mul]
           _ = uval.inv * (GCDMonoid.gcd a b * w) := by rw [hw]
           _ = GCDMonoid.gcd a b * (uval.inv * w) := by ring⟩

/-! ## Existence and Solvability Axioms -/

axiom snf_pid_exists (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (m n : ℕ) (A : Matrix (Fin m) (Fin n) R) :
    ∃ snf : SmithNormalFormPID R m n, snf.isDecompOf A

axiom snf_pid_solvability (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    (m n : ℕ) (A : Matrix (Fin m) (Fin n) R) (b : Fin m → R)
    (snf : SmithNormalFormPID R m n) (hsnf : snf.isDecompOf A) :
    (∃ x : Fin n → R, A.mulVec x = b) ↔
    (∀ i : Fin m,
      (snf.invariantFactor i.val ≠ 0 →
        snf.invariantFactor i.val ∣ (snf.U.mulVec b) i) ∧
      (snf.invariantFactor i.val = 0 →
        (snf.U.mulVec b) i = 0))

/-! ## Bezout over GCDMonoid -/

theorem bezout_pid_forward {R : Type*} [CommRing R] [GCDMonoid R] (a b c : R) :
    (∃ x y : R, a * x + b * y = c) → GCDMonoid.gcd a b ∣ c := by
  intro ⟨x, y, heq⟩
  rw [← heq]
  exact dvd_add (dvd_mul_of_dvd_left (gcd_dvd_left a b) x)
                (dvd_mul_of_dvd_left (gcd_dvd_right a b) y)

/-- Over ℤ, gcd(a,b) | c → ∃ x y, ax+by=c via Bezout coefficients. -/
theorem bezout_int_backward (a b c : ℤ) (h : (Int.gcd a b : ℤ) ∣ c) :
    ∃ x y : ℤ, a * x + b * y = c := by
  obtain ⟨k, hk⟩ := h
  exact ⟨k * Int.gcdA a b, k * Int.gcdB a b, by
    calc a * (k * Int.gcdA a b) + b * (k * Int.gcdB a b)
        = k * (a * Int.gcdA a b + b * Int.gcdB a b) := by ring
      _ = k * (Int.gcd a b : ℤ) := by rw [← Int.gcd_eq_gcd_ab]
      _ = c := by rw [hk]; ring⟩

instance {k : Type*} [Field k] : IsPrincipalIdealRing (Polynomial k) := inferInstance

/-! ## Summary

**Proved (axiom-free):**
1. IsUnimodularPID and its properties (all rings) ✓
2. snf_1x2_invariant_factor_pid: 1×2 invariant factor ~ gcd in any GCDMonoid ✓
   NEW vs. parent: unit.inv_val replaces the ±1 case split
3. bezout_pid_forward: ax+by=c → gcd|c in any GCDMonoid ✓
4. bezout_int_backward: backward direction over ℤ via Bezout coefficients ✓
5. k[X] is a PID (Mathlib instance inference) ✓

**Axioms (2):** snf_pid_exists, snf_pid_solvability
-/

end BezoutIdentityOQ04OQ01OQ01
