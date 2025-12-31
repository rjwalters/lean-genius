import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Quaternion
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Hurwitz's Theorem on n-Square Identities

## What This Proves
Hurwitz's Theorem (1898): An identity of the form
  (x₁² + ⋯ + xₙ²)(y₁² + ⋯ + yₙ²) = z₁² + ⋯ + zₙ²
where each zᵢ is a bilinear function of the xⱼ and yₖ, exists ONLY for n = 1, 2, 4, 8.

This profound theorem explains why the only finite-dimensional normed division
algebras over ℝ are:
  - ℝ (dimension 1) - real numbers
  - ℂ (dimension 2) - complex numbers
  - ℍ (dimension 4) - quaternions
  - 𝕆 (dimension 8) - octonions

## Approach
- **Foundation:** We prove the specific identities for n = 1, 2, 4 completely
- **Original Contributions:** Formalization of the n-square identity concept,
  complete proofs of the 2-square (Brahmagupta-Fibonacci) and 4-square (Euler)
  identities, and statement of the non-existence theorem for n = 3
- **Proof Techniques:** Algebraic ring tactics, bilinearity verification,
  structural analysis of norm-preserving multiplications

## Status
- [x] Complete proof of 2-square identity
- [x] Complete proof of 4-square identity
- [ ] Complete proof of n=3 impossibility (stated as theorem, proof outline given)
- [x] Uses Mathlib for quaternion structure
- [ ] Full Hurwitz theorem (requires advanced methods)

## Mathlib Dependencies
- `Quaternion.normSq_mul` : Quaternion norm is multiplicative
- `Quaternion.normSq_def` : Definition of quaternion norm
- Basic ring/algebra tactics

## Historical Note
Adolf Hurwitz proved this in 1898. If Hamilton had known this theorem, he
would not have spent years trying to find a 3-dimensional "triplet" algebra!

## References
- A. Hurwitz, "Über die Composition der quadratischen Formen", 1898
- John Baez, "The Octonions", Bull. AMS 39 (2002)
-/

namespace HurwitzTheorem

-- ============================================================
-- PART 1: The n-Square Identity Concept
-- ============================================================

/-
  An n-square identity is an algebraic identity that allows us to express
  the product of two sums of n squares as another sum of n squares.

  Formally, for vectors a = (a₁, ..., aₙ) and b = (b₁, ..., bₙ), we seek
  bilinear functions z₁, ..., zₙ in a and b such that:

    (a₁² + ⋯ + aₙ²)(b₁² + ⋯ + bₙ²) = z₁(a,b)² + ⋯ + zₙ(a,b)²

  Such an identity corresponds to a normed composition algebra structure.
-/

/-- The squared norm of a vector in ℝⁿ -/
def normSq {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  ∑ i, v i ^ 2

/-- An n-square identity structure: a bilinear product that preserves norm products -/
structure NSquareIdentity (n : ℕ) where
  /-- The bilinear multiplication that produces the z_i components -/
  mul : (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ)
  /-- Left linearity: mul(a + b, c) = mul(a, c) + mul(b, c) -/
  add_left : ∀ a b c, mul (a + b) c = mul a c + mul b c
  /-- Right linearity: mul(a, b + c) = mul(a, b) + mul(a, c) -/
  add_right : ∀ a b c, mul a (b + c) = mul a b + mul a c
  /-- Left scalar: mul(r • a, b) = r • mul(a, b) -/
  smul_left : ∀ (r : ℝ) a b, mul (r • a) b = r • mul a b
  /-- Right scalar: mul(a, r • b) = r • mul(a, b) -/
  smul_right : ∀ (r : ℝ) a b, mul a (r • b) = r • mul a b
  /-- The identity property: ‖a‖²·‖b‖² = ‖a⊗b‖² -/
  norm_mul : ∀ a b, normSq a * normSq b = normSq (mul a b)

-- ============================================================
-- PART 2: The Trivial Identity (n = 1)
-- ============================================================

/-
  The 1-square identity is trivial:
    x² · y² = (xy)²

  This corresponds to multiplication in ℝ, the simplest normed division algebra.
-/

/-- Multiplication for the 1-square identity -/
def oneMul (a b : Fin 1 → ℝ) : Fin 1 → ℝ :=
  fun _ => a 0 * b 0

/-- The 1-square identity holds -/
theorem one_square_identity (a b : Fin 1 → ℝ) :
    normSq a * normSq b = normSq (oneMul a b) := by
  simp only [normSq, oneMul, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  ring

/-- The 1-square identity structure -/
def oneSquareIdentity : NSquareIdentity 1 where
  mul := oneMul
  add_left := fun a b c => by ext; simp only [oneMul, Pi.add_apply]; ring
  add_right := fun a b c => by ext; simp only [oneMul, Pi.add_apply]; ring
  smul_left := fun r a b => by ext; simp only [oneMul, Pi.smul_apply, smul_eq_mul]; ring
  smul_right := fun r a b => by ext; simp only [oneMul, Pi.smul_apply, smul_eq_mul]; ring
  norm_mul := one_square_identity

-- ============================================================
-- PART 3: Brahmagupta-Fibonacci Identity (n = 2)
-- ============================================================

/-
  The 2-square identity (Brahmagupta 628 CE, Fibonacci 1202):
    (a² + b²)(c² + d²) = (ac - bd)² + (ad + bc)²

  This corresponds to the norm of complex number multiplication:
    |z₁|² · |z₂|² = |z₁z₂|²

  The identity encodes the multiplication rule for complex numbers!
-/

/-- Complex-like multiplication for the 2-square identity -/
def twoMul (a b : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![a 0 * b 0 - a 1 * b 1, a 0 * b 1 + a 1 * b 0]

/-- The Brahmagupta-Fibonacci 2-square identity -/
theorem two_square_identity (a b : Fin 2 → ℝ) :
    normSq a * normSq b = normSq (twoMul a b) := by
  simp only [normSq, twoMul]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  ring

/-- The 2-square identity structure (complex numbers) -/
def twoSquareIdentity : NSquareIdentity 2 where
  mul := twoMul
  add_left := fun a b c => by
    ext i
    fin_cases i <;> simp [twoMul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    all_goals ring
  add_right := fun a b c => by
    ext i
    fin_cases i <;> simp [twoMul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    all_goals ring
  smul_left := fun r a b => by
    ext i
    fin_cases i <;> simp [twoMul, Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    all_goals ring
  smul_right := fun r a b => by
    ext i
    fin_cases i <;> simp [twoMul, Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    all_goals ring
  norm_mul := two_square_identity

-- ============================================================
-- PART 4: Euler's Four-Square Identity (n = 4)
-- ============================================================

/-
  Euler's 4-square identity (1748):
    (a₁² + a₂² + a₃² + a₄²)(b₁² + b₂² + b₃² + b₄²)
      = (a₁b₁ - a₂b₂ - a₃b₃ - a₄b₄)²
      + (a₁b₂ + a₂b₁ + a₃b₄ - a₄b₃)²
      + (a₁b₃ - a₂b₄ + a₃b₁ + a₄b₂)²
      + (a₁b₄ + a₂b₃ - a₃b₂ + a₄b₁)²

  This is exactly the norm-multiplicativity of quaternions!
  For quaternions q = a₁ + a₂i + a₃j + a₄k, we have |q₁q₂|² = |q₁|²|q₂|²
-/

/-- Quaternion-like multiplication for the 4-square identity -/
def fourMul (a b : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![a 0 * b 0 - a 1 * b 1 - a 2 * b 2 - a 3 * b 3,
    a 0 * b 1 + a 1 * b 0 + a 2 * b 3 - a 3 * b 2,
    a 0 * b 2 - a 1 * b 3 + a 2 * b 0 + a 3 * b 1,
    a 0 * b 3 + a 1 * b 2 - a 2 * b 1 + a 3 * b 0]

set_option maxHeartbeats 800000 in
/-- Euler's 4-square identity -/
theorem four_square_identity (a b : Fin 4 → ℝ) :
    normSq a * normSq b = normSq (fourMul a b) := by
  simp only [normSq, fourMul, Fin.sum_univ_four, Fin.isValue]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.cons_val_three]
  ring

set_option maxHeartbeats 800000 in
/-- The 4-square identity structure (quaternions) -/
def fourSquareIdentity : NSquareIdentity 4 where
  mul := fourMul
  add_left := fun a b c => by
    funext i
    fin_cases i <;> simp [fourMul] <;> ring
  add_right := fun a b c => by
    funext i
    fin_cases i <;> simp [fourMul] <;> ring
  smul_left := fun r a b => by
    funext i
    fin_cases i <;> simp [fourMul, smul_eq_mul] <;> ring
  smul_right := fun r a b => by
    funext i
    fin_cases i <;> simp [fourMul, smul_eq_mul] <;> ring
  norm_mul := four_square_identity

-- ============================================================
-- PART 5: Connection to Quaternions in Mathlib
-- ============================================================

/-
  Mathlib formalizes quaternions and proves their norm is multiplicative.
  This provides an alternative proof of the 4-square identity.
-/

/-- The quaternion norm squared is multiplicative -/
theorem quaternion_norm_mul (q₁ q₂ : Quaternion ℝ) :
    Quaternion.normSq (q₁ * q₂) = Quaternion.normSq q₁ * Quaternion.normSq q₂ :=
  Quaternion.normSq.map_mul q₁ q₂

-- ============================================================
-- PART 6: The 8-Square Identity (Octonions)
-- ============================================================

/-
  The 8-square identity (Degen 1818, Cayley-Dickson construction):

  For octonions, we have |o₁o₂| = |o₁||o₂|, which gives an 8-square identity.
  The formula is complex, with 64 terms, each a sum of 8 products.

  We state the existence here; the full formula is given in the references.
-/

/-- Statement that an 8-square identity exists (via octonions) -/
axiom eight_square_identity_exists : NSquareIdentity 8

-- ============================================================
-- PART 7: Non-Existence for n = 3
-- ============================================================

/-
  HURWITZ'S KEY RESULT: There is NO 3-square identity!

  Hamilton searched for years for a 3-dimensional "triplet" algebra before
  discovering quaternions in 1843. Hurwitz's 1898 theorem explains why:
  there simply cannot be such an algebra.

  ## Why n = 3 Fails

  **Intuitive explanation:**
  A 3-square identity would give a multiplication on ℝ³ preserving norms.
  But consider: in ℝ³, the cross product a × b has norm |a||b|sin(θ),
  which equals |a||b| only when vectors are perpendicular.
  For parallel vectors, a × b = 0, destroying the required norm property.

  **Algebraic explanation:**
  A normed composition algebra on ℝⁿ requires a specific tensor structure.
  The constraints force n to be a power of 2 (from Cayley-Dickson construction),
  AND the algebra must be "alternative" (a weakening of associativity).
  Only n = 1, 2, 4, 8 satisfy both constraints.

  **Topological explanation:**
  The existence of a norm-multiplicative bilinear map ℝⁿ × ℝⁿ → ℝⁿ
  is related to the existence of n-1 linearly independent vector fields on Sⁿ⁻¹.
  By Adams' theorem (1962), this requires n to be 1, 2, 4, or 8.

  We state this as a theorem; the full proof requires methods beyond basic
  Mathlib (either representation theory, topology, or careful case analysis).
-/

/-
  ## Proof Strategy for n = 3 Impossibility

  The proof uses orthogonality constraints. Key insight:

  For any NSquareIdentity, if |a| = |b| = 1, then |mul(a,b)| = 1.
  If a ⊥ b (orthogonal unit vectors), then |a + b|² = 2, so
  |mul(a + b, c)|² = 2|c|² for any c.

  By bilinearity: mul(a + b, c) = mul(a, c) + mul(b, c)
  So: |mul(a,c) + mul(b,c)|² = 2 when |c| = 1

  Since |mul(a,c)|² = |mul(b,c)|² = 1, we get:
  1 + 2⟨mul(a,c), mul(b,c)⟩ + 1 = 2
  ⟨mul(a,c), mul(b,c)⟩ = 0

  This forces orthogonality: mul(a,c) ⊥ mul(b,c) whenever a ⊥ b.

  In 3D, we have 3 orthonormal basis vectors e₁, e₂, e₃.
  For fixed c = e₁:
  - mul(e₁, e₁), mul(e₂, e₁), mul(e₃, e₁) must be pairwise orthogonal unit vectors

  But that's 3 pairwise orthogonal unit vectors in ℝ³, which is fine (they form a basis).
  The contradiction comes from considering multiple right-hand arguments...

  For c = e₁: mul(eᵢ, e₁) pairwise orthogonal
  For c = e₂: mul(eᵢ, e₂) pairwise orthogonal
  For c = e₃: mul(eᵢ, e₃) pairwise orthogonal

  And additionally, for each fixed a = eᵢ:
  mul(eᵢ, e₁), mul(eᵢ, e₂), mul(eᵢ, e₃) must be pairwise orthogonal

  This creates 9 unit vectors in ℝ³ with a complex web of orthogonality constraints.
  The constraints are over-determined and lead to contradiction.
-/

/-- Inner product on ℝⁿ represented as functions -/
def innerProd {n : ℕ} (v w : Fin n → ℝ) : ℝ :=
  ∑ i, v i * w i

/-- Standard basis vector in ℝⁿ -/
def stdBasis {n : ℕ} (i : Fin n) : Fin n → ℝ :=
  fun j => if i = j then 1 else 0

/-- The norm squared of a standard basis vector is 1 -/
theorem normSq_stdBasis {n : ℕ} [NeZero n] (i : Fin n) :
    normSq (stdBasis i) = 1 := by
  simp only [normSq, stdBasis]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji.symm]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- normSq v = innerProd v v -/
lemma normSq_eq_innerProd (v : Fin n → ℝ) : normSq v = innerProd v v := by
  simp only [normSq, innerProd, sq]

/-- The norm squared expands with inner product -/
lemma normSq_add (a b : Fin n → ℝ) :
    normSq (a + b) = normSq a + 2 * innerProd a b + normSq b := by
  simp only [normSq, innerProd, Pi.add_apply, add_sq]
  simp only [Finset.sum_add_distrib, Finset.mul_sum]
  ring

/-- The norm squared expands with subtraction -/
lemma normSq_sub (a b : Fin n → ℝ) :
    normSq (a - b) = normSq a - 2 * innerProd a b + normSq b := by
  simp only [normSq, innerProd, Pi.sub_apply, sub_sq]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  ring

/-- normSq is non-negative -/
lemma normSq_nonneg (v : Fin n → ℝ) : 0 ≤ normSq v := by
  simp only [normSq]
  apply Finset.sum_nonneg
  intros; apply sq_nonneg

/-- normSq v = 0 iff v = 0 -/
lemma normSq_eq_zero (v : Fin n → ℝ) : normSq v = 0 ↔ v = 0 := by
  constructor
  · intro h
    ext i
    have h' : ∑ j : Fin n, (v j)^2 = 0 := h
    have hsum : ∀ j, (v j)^2 ≥ 0 := fun j => sq_nonneg _
    have hzero := Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hsum j) |>.mp h'
    have hvi : (v i)^2 = 0 := hzero i (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp hvi
  · intro h
    simp [h, normSq]

/-- normSq of negation -/
lemma normSq_neg (v : Fin n → ℝ) : normSq (-v) = normSq v := by
  simp only [normSq, Pi.neg_apply, neg_sq]

/-- Inner product in terms of normSq -/
lemma innerProd_eq_normSq (a b : Fin n → ℝ) :
    innerProd a b = (normSq (a + b) - normSq a - normSq b) / 2 := by
  rw [normSq_add]
  ring

/-- Key orthogonality lemma: if a ⊥ b are unit vectors, then mul(a,c) ⊥ mul(b,c)
    for any unit vector c -/
lemma orthogonality_constraint (nsi : NSquareIdentity n)
    (a b c : Fin n → ℝ)
    (ha : normSq a = 1) (hb : normSq b = 1) (hc : normSq c = 1)
    (hab : innerProd a b = 0) :
    innerProd (nsi.mul a c) (nsi.mul b c) = 0 := by
  -- Step 1: |a + b|² = 2 (since a, b are orthogonal unit vectors)
  have hab_normSq : normSq (a + b) = 2 := by
    rw [normSq_add, ha, hb, hab]
    ring

  -- Step 2: |mul(a,c)|² = 1 and |mul(b,c)|² = 1
  have hmac : normSq (nsi.mul a c) = 1 := by
    rw [← nsi.norm_mul, ha, hc]; ring
  have hmbc : normSq (nsi.mul b c) = 1 := by
    rw [← nsi.norm_mul, hb, hc]; ring

  -- Step 3: |mul(a+b, c)|² = |a+b|² * |c|² = 2
  have hmabc : normSq (nsi.mul (a + b) c) = 2 := by
    rw [← nsi.norm_mul, hab_normSq, hc]; ring

  -- Step 4: mul(a+b, c) = mul(a,c) + mul(b,c) by left linearity
  have hlin : nsi.mul (a + b) c = nsi.mul a c + nsi.mul b c := nsi.add_left a b c

  -- Step 5: |mul(a,c) + mul(b,c)|² = 2
  have hsum : normSq (nsi.mul a c + nsi.mul b c) = 2 := by
    rw [← hlin]; exact hmabc

  -- Step 6: Expand |mul(a,c) + mul(b,c)|² and solve for inner product
  rw [normSq_add] at hsum
  -- hsum : normSq (nsi.mul a c) + 2 * innerProd (nsi.mul a c) (nsi.mul b c)
  --        + normSq (nsi.mul b c) = 2
  rw [hmac, hmbc] at hsum
  -- hsum : 1 + 2 * innerProd ... + 1 = 2
  linarith

/-- Right orthogonality: if b ⊥ c are unit vectors, then mul(a,b) ⊥ mul(a,c)
    for any unit vector a -/
lemma orthogonality_constraint_right (nsi : NSquareIdentity n)
    (a b c : Fin n → ℝ)
    (ha : normSq a = 1) (hb : normSq b = 1) (hc : normSq c = 1)
    (hbc : innerProd b c = 0) :
    innerProd (nsi.mul a b) (nsi.mul a c) = 0 := by
  -- Similar to left orthogonality, using add_right instead of add_left
  have hbc_normSq : normSq (b + c) = 2 := by
    rw [normSq_add, hb, hc, hbc]; ring

  have hmab : normSq (nsi.mul a b) = 1 := by
    rw [← nsi.norm_mul, ha, hb]; ring
  have hmac : normSq (nsi.mul a c) = 1 := by
    rw [← nsi.norm_mul, ha, hc]; ring

  have hmabc : normSq (nsi.mul a (b + c)) = 2 := by
    rw [← nsi.norm_mul, ha, hbc_normSq]; ring

  have hlin : nsi.mul a (b + c) = nsi.mul a b + nsi.mul a c := nsi.add_right a b c

  have hsum : normSq (nsi.mul a b + nsi.mul a c) = 2 := by
    rw [← hlin]; exact hmabc

  rw [normSq_add] at hsum
  rw [hmab, hmac] at hsum
  linarith

-- ============================================================
-- PARSEVAL IDENTITY LEMMAS FOR ℝ³
-- ============================================================

/-- Scalar multiplication for vectors -/
def smul (c : ℝ) (v : Fin 3 → ℝ) : Fin 3 → ℝ := fun i => c * v i

/-- Projection onto orthonormal triple -/
def proj3 (v₁ v₂ v₃ w : Fin 3 → ℝ) : Fin 3 → ℝ :=
  smul (innerProd w v₁) v₁ + smul (innerProd w v₂) v₂ + smul (innerProd w v₃) v₃

lemma innerProd_add_left (u v w : Fin 3 → ℝ) :
    innerProd (u + v) w = innerProd u w + innerProd v w := by
  simp only [innerProd, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma innerProd_sub_left (u v w : Fin 3 → ℝ) :
    innerProd (u - v) w = innerProd u w - innerProd v w := by
  simp only [innerProd, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma innerProd_comm (v w : Fin 3 → ℝ) : innerProd v w = innerProd w v := by
  simp only [innerProd]; congr 1; ext i; ring

lemma innerProd_add_right (u v w : Fin 3 → ℝ) :
    innerProd u (v + w) = innerProd u v + innerProd u w := by
  rw [innerProd_comm, innerProd_add_left, innerProd_comm v u, innerProd_comm w u]

lemma innerProd_smul_left (c : ℝ) (v w : Fin 3 → ℝ) :
    innerProd (smul c v) w = c * innerProd v w := by
  simp only [innerProd, smul, mul_assoc, Finset.mul_sum]

lemma innerProd_smul_smul (a b : ℝ) (v w : Fin 3 → ℝ) :
    innerProd (smul a v) (smul b w) = a * b * innerProd v w := by
  simp only [innerProd, smul]
  have h : ∀ i, a * v i * (b * w i) = a * b * (v i * w i) := fun i => by ring
  simp only [h]
  rw [← Finset.mul_sum]

lemma normSq_smul (c : ℝ) (v : Fin 3 → ℝ) : normSq (smul c v) = c^2 * normSq v := by
  simp only [normSq, smul]
  rw [Finset.mul_sum]
  congr 1; ext i; ring

/-- In ℝ³, a vector orthogonal to an orthonormal triple is zero.
    This is the key linear algebra fact: orthonormal vectors span ℝ³. -/
lemma ortho_to_orthonormal_triple_eq_zero (v₁ v₂ v₃ u : Fin 3 → ℝ)
    (hv₁ : normSq v₁ = 1) (hv₂ : normSq v₂ = 1) (hv₃ : normSq v₃ = 1)
    (h12 : innerProd v₁ v₂ = 0) (h13 : innerProd v₁ v₃ = 0) (h23 : innerProd v₂ v₃ = 0)
    (hu1 : innerProd u v₁ = 0) (hu2 : innerProd u v₂ = 0) (hu3 : innerProd u v₃ = 0) :
    u = 0 := by
  -- Strategy: Define M = [v₁|v₂|v₃], show Mᵀ M = I, hence det(M) ≠ 0.
  -- The condition ⟨u, vᵢ⟩ = 0 means Mᵀ mulVec u = 0.
  -- Since M is invertible, u = 0.

  -- Define the matrix M with columns v₁, v₂, v₃
  let M : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of (fun i j =>
    match j with
    | 0 => v₁ i
    | 1 => v₂ i
    | 2 => v₃ i)

  -- The key: Mᵀ M = I (by orthonormality)
  -- First, extract the numeric forms of the hypotheses
  have hv₁' : v₁ 0 * v₁ 0 + v₁ 1 * v₁ 1 + v₁ 2 * v₁ 2 = 1 := by
    have := hv₁; simp only [normSq, Fin.sum_univ_three, sq] at this; linarith
  have hv₂' : v₂ 0 * v₂ 0 + v₂ 1 * v₂ 1 + v₂ 2 * v₂ 2 = 1 := by
    have := hv₂; simp only [normSq, Fin.sum_univ_three, sq] at this; linarith
  have hv₃' : v₃ 0 * v₃ 0 + v₃ 1 * v₃ 1 + v₃ 2 * v₃ 2 = 1 := by
    have := hv₃; simp only [normSq, Fin.sum_univ_three, sq] at this; linarith
  have h12' : v₁ 0 * v₂ 0 + v₁ 1 * v₂ 1 + v₁ 2 * v₂ 2 = 0 := by
    have := h12; simp only [innerProd, Fin.sum_univ_three] at this; linarith
  have h13' : v₁ 0 * v₃ 0 + v₁ 1 * v₃ 1 + v₁ 2 * v₃ 2 = 0 := by
    have := h13; simp only [innerProd, Fin.sum_univ_three] at this; linarith
  have h23' : v₂ 0 * v₃ 0 + v₂ 1 * v₃ 1 + v₂ 2 * v₃ 2 = 0 := by
    have := h23; simp only [innerProd, Fin.sum_univ_three] at this; linarith

  have hMTM : M.transpose * M = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Matrix.of_apply,
               Fin.sum_univ_three]
    fin_cases i <;> fin_cases j <;>
      simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, Fin.reduceFinMk]
    -- Now each goal has M i j entries - need to unfold them
    -- Use show to convert to v₁/v₂/v₃
    · show v₁ 0 * v₁ 0 + v₁ 1 * v₁ 1 + v₁ 2 * v₁ 2 = 1; linarith
    · show v₁ 0 * v₂ 0 + v₁ 1 * v₂ 1 + v₁ 2 * v₂ 2 = 0; linarith
    · show v₁ 0 * v₃ 0 + v₁ 1 * v₃ 1 + v₁ 2 * v₃ 2 = 0; linarith
    · show v₂ 0 * v₁ 0 + v₂ 1 * v₁ 1 + v₂ 2 * v₁ 2 = 0; linarith
    · show v₂ 0 * v₂ 0 + v₂ 1 * v₂ 1 + v₂ 2 * v₂ 2 = 1; linarith
    · show v₂ 0 * v₃ 0 + v₂ 1 * v₃ 1 + v₂ 2 * v₃ 2 = 0; linarith
    · show v₃ 0 * v₁ 0 + v₃ 1 * v₁ 1 + v₃ 2 * v₁ 2 = 0; linarith
    · show v₃ 0 * v₂ 0 + v₃ 1 * v₂ 1 + v₃ 2 * v₂ 2 = 0; linarith
    · show v₃ 0 * v₃ 0 + v₃ 1 * v₃ 1 + v₃ 2 * v₃ 2 = 1; linarith

  -- From Mᵀ M = I, we get det(M)² = 1, so det(M) ≠ 0
  have hdet : M.det ≠ 0 := by
    have h1 : (M.transpose * M).det = (1 : Matrix (Fin 3) (Fin 3) ℝ).det := by rw [hMTM]
    simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h1
    intro hzero
    rw [hzero] at h1
    simp at h1

  -- M is invertible (since det ≠ 0)
  have hMinv : Invertible M := by
    have hunit : IsUnit M.det := by
      rw [isUnit_iff_ne_zero]
      exact hdet
    exact Matrix.invertibleOfIsUnitDet M hunit

  -- Mᵀ is also invertible
  have hMTinv : Invertible M.transpose := Matrix.invertibleTranspose M

  -- The condition ⟨u, vᵢ⟩ = 0 means M.transpose.mulVec u = 0
  have hu1' : u 0 * v₁ 0 + u 1 * v₁ 1 + u 2 * v₁ 2 = 0 := by
    have := hu1; simp only [innerProd, Fin.sum_univ_three] at this; linarith
  have hu2' : u 0 * v₂ 0 + u 1 * v₂ 1 + u 2 * v₂ 2 = 0 := by
    have := hu2; simp only [innerProd, Fin.sum_univ_three] at this; linarith
  have hu3' : u 0 * v₃ 0 + u 1 * v₃ 1 + u 2 * v₃ 2 = 0 := by
    have := hu3; simp only [innerProd, Fin.sum_univ_three] at this; linarith

  have hMTu : M.transpose.mulVec u = 0 := by
    ext i
    simp only [Matrix.mulVec, Matrix.transpose_apply, Matrix.of_apply, Matrix.dotProduct,
               Pi.zero_apply, Fin.sum_univ_three]
    fin_cases i <;> simp only [Fin.isValue, Fin.reduceFinMk]
    · show v₁ 0 * u 0 + v₁ 1 * u 1 + v₁ 2 * u 2 = 0; linarith
    · show v₂ 0 * u 0 + v₂ 1 * u 1 + v₂ 2 * u 2 = 0; linarith
    · show v₃ 0 * u 0 + v₃ 1 * u 1 + v₃ 2 * u 2 = 0; linarith

  -- Use mulVec_injective: Mᵀ u = Mᵀ 0 = 0, so u = 0
  have hMT0 : M.transpose.mulVec 0 = 0 := by simp [Matrix.mulVec_zero]
  have h_eq : M.transpose.mulVec u = M.transpose.mulVec 0 := by rw [hMTu, hMT0]
  exact (Matrix.mulVec_injective_of_invertible M.transpose).eq_iff.mp h_eq

/-- Parseval identity: |w|² = ⟨w,v₁⟩² + ⟨w,v₂⟩² + ⟨w,v₃⟩² for orthonormal {v₁,v₂,v₃} -/
theorem inner_expansion_three (v₁ v₂ v₃ w : Fin 3 → ℝ)
    (hv₁ : normSq v₁ = 1) (hv₂ : normSq v₂ = 1) (hv₃ : normSq v₃ = 1)
    (h12 : innerProd v₁ v₂ = 0) (h13 : innerProd v₁ v₃ = 0) (h23 : innerProd v₂ v₃ = 0) :
    normSq w = (innerProd w v₁)^2 + (innerProd w v₂)^2 + (innerProd w v₃)^2 := by
  -- Let proj = ⟨w,v₁⟩v₁ + ⟨w,v₂⟩v₂ + ⟨w,v₃⟩v₃
  let c₁ := innerProd w v₁; let c₂ := innerProd w v₂; let c₃ := innerProd w v₃
  let proj := proj3 v₁ v₂ v₃ w
  let diff := w - proj

  -- diff is orthogonal to each vᵢ using our new lemmas
  have hdiff1 : innerProd diff v₁ = 0 := by
    simp only [diff, proj, proj3]
    rw [innerProd_sub_left, innerProd_add_left, innerProd_add_left]
    rw [innerProd_smul_left, innerProd_smul_left, innerProd_smul_left]
    have hv1v1 : innerProd v₁ v₁ = 1 := by rw [← normSq_eq_innerProd]; exact hv₁
    have hv2v1 : innerProd v₂ v₁ = 0 := by rw [innerProd_comm]; exact h12
    have hv3v1 : innerProd v₃ v₁ = 0 := by rw [innerProd_comm]; exact h13
    rw [hv1v1, hv2v1, hv3v1]; ring

  have hdiff2 : innerProd diff v₂ = 0 := by
    simp only [diff, proj, proj3]
    rw [innerProd_sub_left, innerProd_add_left, innerProd_add_left]
    rw [innerProd_smul_left, innerProd_smul_left, innerProd_smul_left]
    have hv1v2 : innerProd v₁ v₂ = 0 := h12
    have hv2v2 : innerProd v₂ v₂ = 1 := by rw [← normSq_eq_innerProd]; exact hv₂
    have hv3v2 : innerProd v₃ v₂ = 0 := by rw [innerProd_comm]; exact h23
    rw [hv1v2, hv2v2, hv3v2]; ring

  have hdiff3 : innerProd diff v₃ = 0 := by
    simp only [diff, proj, proj3]
    rw [innerProd_sub_left, innerProd_add_left, innerProd_add_left]
    rw [innerProd_smul_left, innerProd_smul_left, innerProd_smul_left]
    have hv1v3 : innerProd v₁ v₃ = 0 := h13
    have hv2v3 : innerProd v₂ v₃ = 0 := h23
    have hv3v3 : innerProd v₃ v₃ = 1 := by rw [← normSq_eq_innerProd]; exact hv₃
    rw [hv1v3, hv2v3, hv3v3]; ring

  -- Therefore diff = 0
  have hdiff_zero : diff = 0 :=
    ortho_to_orthonormal_triple_eq_zero v₁ v₂ v₃ diff hv₁ hv₂ hv₃ h12 h13 h23 hdiff1 hdiff2 hdiff3

  -- So w = proj
  have hw_eq_proj : w = proj := by
    have : w - proj = 0 := hdiff_zero
    simp only [sub_eq_zero] at this
    exact this

  -- Compute |proj|² = c₁² + c₂² + c₃² using orthonormality
  have hproj_norm : normSq proj = c₁^2 + c₂^2 + c₃^2 := by
    simp only [proj, proj3]
    have hproj_eq : smul c₁ v₁ + smul c₂ v₂ + smul c₃ v₃ = (smul c₁ v₁ + smul c₂ v₂) + smul c₃ v₃ := by
      simp only [add_assoc]
    rw [hproj_eq, normSq_add, normSq_add]
    have ns1 : normSq (smul c₁ v₁) = c₁^2 := by rw [normSq_smul, hv₁]; ring
    have ns2 : normSq (smul c₂ v₂) = c₂^2 := by rw [normSq_smul, hv₂]; ring
    have ns3 : normSq (smul c₃ v₃) = c₃^2 := by rw [normSq_smul, hv₃]; ring
    have ip12 : innerProd (smul c₁ v₁) (smul c₂ v₂) = 0 := by rw [innerProd_smul_smul, h12]; ring
    have ip13 : innerProd (smul c₁ v₁) (smul c₃ v₃) = 0 := by rw [innerProd_smul_smul, h13]; ring
    have ip23 : innerProd (smul c₂ v₂) (smul c₃ v₃) = 0 := by rw [innerProd_smul_smul, h23]; ring
    have ipcross : innerProd (smul c₁ v₁ + smul c₂ v₂) (smul c₃ v₃) = 0 := by
      rw [innerProd_add_left, ip13, ip23]; ring
    rw [ns1, ns2, ns3, ip12, ipcross]; ring

  calc normSq w = normSq proj := by rw [hw_eq_proj]
    _ = c₁^2 + c₂^2 + c₃^2 := hproj_norm

/-- In ℝ³, a unit vector orthogonal to two orthonormal vectors equals ±third -/
lemma unit_ortho_two_eq_pm_third (v₁ v₂ v₃ w : Fin 3 → ℝ)
    (hv₁ : normSq v₁ = 1) (hv₂ : normSq v₂ = 1) (hv₃ : normSq v₃ = 1)
    (h12 : innerProd v₁ v₂ = 0) (h13 : innerProd v₁ v₃ = 0) (h23 : innerProd v₂ v₃ = 0)
    (hw : normSq w = 1) (hw1 : innerProd w v₁ = 0) (hw2 : innerProd w v₂ = 0) :
    w = v₃ ∨ w = -v₃ := by
  have hparseval := inner_expansion_three v₁ v₂ v₃ w hv₁ hv₂ hv₃ h12 h13 h23
  rw [hw1, hw2, hw] at hparseval
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, zero_add] at hparseval
  -- So (innerProd w v₃)² = 1
  have hsq : (innerProd w v₃)^2 = 1 := by linarith
  have habs : innerProd w v₃ = 1 ∨ innerProd w v₃ = -1 := sq_eq_one_iff.mp hsq
  rcases habs with h | h
  · -- innerProd w v₃ = 1, so w = v₃
    left
    have hdiff : normSq (w - v₃) = 0 := by
      rw [normSq_sub, hw, hv₃, h]; ring
    have := (normSq_eq_zero (w - v₃)).mp hdiff
    simp only [sub_eq_zero] at this
    exact this
  · -- innerProd w v₃ = -1, so w = -v₃
    right
    have hnv₃ : normSq (-v₃) = 1 := by rw [normSq_neg]; exact hv₃
    have hinner_neg : innerProd w (-v₃) = -innerProd w v₃ := by
      simp only [innerProd, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    have hinner : innerProd w (-v₃) = 1 := by rw [hinner_neg, h]; ring
    have hdiff : normSq (w - (-v₃)) = 0 := by
      rw [normSq_sub, hw, hnv₃, hinner]; ring
    have := (normSq_eq_zero (w - (-v₃))).mp hdiff
    simp only [sub_eq_zero] at this
    exact this

set_option maxHeartbeats 400000 in
/-- Bilinear Parseval: ⟨u, w⟩ = Σᵢ ⟨u, vᵢ⟩⟨w, vᵢ⟩ for orthonormal basis {v₁, v₂, v₃} -/
lemma inner_bilinear_expansion (v₁ v₂ v₃ u w : Fin 3 → ℝ)
    (hv₁ : normSq v₁ = 1) (hv₂ : normSq v₂ = 1) (hv₃ : normSq v₃ = 1)
    (h12 : innerProd v₁ v₂ = 0) (h13 : innerProd v₁ v₃ = 0) (h23 : innerProd v₂ v₃ = 0) :
    innerProd u w = (innerProd u v₁) * (innerProd w v₁) +
                    (innerProd u v₂) * (innerProd w v₂) +
                    (innerProd u v₃) * (innerProd w v₃) := by
  -- By Parseval, u = ⟨u,v₁⟩v₁ + ⟨u,v₂⟩v₂ + ⟨u,v₃⟩v₃
  -- Similarly for w. Then ⟨u,w⟩ expands by orthonormality.
  let c₁ := innerProd u v₁; let c₂ := innerProd u v₂; let c₃ := innerProd u v₃
  let d₁ := innerProd w v₁; let d₂ := innerProd w v₂; let d₃ := innerProd w v₃

  -- u - (c₁v₁ + c₂v₂ + c₃v₃) is orthogonal to all vᵢ, hence zero
  let proj_u := smul c₁ v₁ + smul c₂ v₂ + smul c₃ v₃
  let diff_u := u - proj_u

  have hdiff_u1 : innerProd diff_u v₁ = 0 := by
    simp only [diff_u, proj_u]
    rw [innerProd_sub_left, innerProd_add_left, innerProd_add_left]
    rw [innerProd_smul_left, innerProd_smul_left, innerProd_smul_left]
    have hv1v1 : innerProd v₁ v₁ = 1 := by rw [← normSq_eq_innerProd]; exact hv₁
    have hv2v1 : innerProd v₂ v₁ = 0 := by rw [innerProd_comm]; exact h12
    have hv3v1 : innerProd v₃ v₁ = 0 := by rw [innerProd_comm]; exact h13
    rw [hv1v1, hv2v1, hv3v1]; ring

  have hdiff_u2 : innerProd diff_u v₂ = 0 := by
    simp only [diff_u, proj_u]
    rw [innerProd_sub_left, innerProd_add_left, innerProd_add_left]
    rw [innerProd_smul_left, innerProd_smul_left, innerProd_smul_left]
    have hv1v2 : innerProd v₁ v₂ = 0 := h12
    have hv2v2 : innerProd v₂ v₂ = 1 := by rw [← normSq_eq_innerProd]; exact hv₂
    have hv3v2 : innerProd v₃ v₂ = 0 := by rw [innerProd_comm]; exact h23
    rw [hv1v2, hv2v2, hv3v2]; ring

  have hdiff_u3 : innerProd diff_u v₃ = 0 := by
    simp only [diff_u, proj_u]
    rw [innerProd_sub_left, innerProd_add_left, innerProd_add_left]
    rw [innerProd_smul_left, innerProd_smul_left, innerProd_smul_left]
    have hv1v3 : innerProd v₁ v₃ = 0 := h13
    have hv2v3 : innerProd v₂ v₃ = 0 := h23
    have hv3v3 : innerProd v₃ v₃ = 1 := by rw [← normSq_eq_innerProd]; exact hv₃
    rw [hv1v3, hv2v3, hv3v3]; ring

  have hdiff_u_zero : diff_u = 0 :=
    ortho_to_orthonormal_triple_eq_zero v₁ v₂ v₃ diff_u hv₁ hv₂ hv₃ h12 h13 h23 hdiff_u1 hdiff_u2 hdiff_u3

  have hu_eq : u = proj_u := by
    have : u - proj_u = 0 := hdiff_u_zero
    simp only [sub_eq_zero] at this
    exact this

  -- Similarly for w
  let proj_w := smul d₁ v₁ + smul d₂ v₂ + smul d₃ v₃
  let diff_w := w - proj_w

  have hdiff_w1 : innerProd diff_w v₁ = 0 := by
    simp only [diff_w, proj_w]
    rw [innerProd_sub_left, innerProd_add_left, innerProd_add_left]
    rw [innerProd_smul_left, innerProd_smul_left, innerProd_smul_left]
    have hv1v1 : innerProd v₁ v₁ = 1 := by rw [← normSq_eq_innerProd]; exact hv₁
    have hv2v1 : innerProd v₂ v₁ = 0 := by rw [innerProd_comm]; exact h12
    have hv3v1 : innerProd v₃ v₁ = 0 := by rw [innerProd_comm]; exact h13
    rw [hv1v1, hv2v1, hv3v1]; ring

  have hdiff_w2 : innerProd diff_w v₂ = 0 := by
    simp only [diff_w, proj_w]
    rw [innerProd_sub_left, innerProd_add_left, innerProd_add_left]
    rw [innerProd_smul_left, innerProd_smul_left, innerProd_smul_left]
    have hv1v2 : innerProd v₁ v₂ = 0 := h12
    have hv2v2 : innerProd v₂ v₂ = 1 := by rw [← normSq_eq_innerProd]; exact hv₂
    have hv3v2 : innerProd v₃ v₂ = 0 := by rw [innerProd_comm]; exact h23
    rw [hv1v2, hv2v2, hv3v2]; ring

  have hdiff_w3 : innerProd diff_w v₃ = 0 := by
    simp only [diff_w, proj_w]
    rw [innerProd_sub_left, innerProd_add_left, innerProd_add_left]
    rw [innerProd_smul_left, innerProd_smul_left, innerProd_smul_left]
    have hv1v3 : innerProd v₁ v₃ = 0 := h13
    have hv2v3 : innerProd v₂ v₃ = 0 := h23
    have hv3v3 : innerProd v₃ v₃ = 1 := by rw [← normSq_eq_innerProd]; exact hv₃
    rw [hv1v3, hv2v3, hv3v3]; ring

  have hdiff_w_zero : diff_w = 0 :=
    ortho_to_orthonormal_triple_eq_zero v₁ v₂ v₃ diff_w hv₁ hv₂ hv₃ h12 h13 h23 hdiff_w1 hdiff_w2 hdiff_w3

  have hw_eq : w = proj_w := by
    have : w - proj_w = 0 := hdiff_w_zero
    simp only [sub_eq_zero] at this
    exact this

  -- Now compute ⟨u, w⟩ = ⟨proj_u, proj_w⟩
  -- We'll compute this directly using the definition
  have hv1v1 : innerProd v₁ v₁ = 1 := by rw [← normSq_eq_innerProd]; exact hv₁
  have hv2v2 : innerProd v₂ v₂ = 1 := by rw [← normSq_eq_innerProd]; exact hv₂
  have hv3v3 : innerProd v₃ v₃ = 1 := by rw [← normSq_eq_innerProd]; exact hv₃
  have hv1v2 : innerProd v₁ v₂ = 0 := h12
  have hv2v1 : innerProd v₂ v₁ = 0 := by rw [innerProd_comm]; exact h12
  have hv1v3 : innerProd v₁ v₃ = 0 := h13
  have hv3v1 : innerProd v₃ v₁ = 0 := by rw [innerProd_comm]; exact h13
  have hv2v3 : innerProd v₂ v₃ = 0 := h23
  have hv3v2 : innerProd v₃ v₂ = 0 := by rw [innerProd_comm]; exact h23

  calc innerProd u w = innerProd proj_u proj_w := by rw [hu_eq, hw_eq]
    _ = innerProd (smul c₁ v₁ + smul c₂ v₂ + smul c₃ v₃) (smul d₁ v₁ + smul d₂ v₂ + smul d₃ v₃) := rfl
    _ = c₁ * d₁ + c₂ * d₂ + c₃ * d₃ := by
        -- Expand using definition and compute
        simp only [innerProd, smul, Fin.sum_univ_three, Pi.add_apply]
        -- The expansion is:
        -- c₁d₁(v₁₀² + v₁₁² + v₁₂²) + c₂d₂(v₂₀² + v₂₁² + v₂₂²) + c₃d₃(v₃₀² + v₃₁² + v₃₂²)
        -- + cross terms that are 0 by orthogonality
        simp only [innerProd, Fin.sum_univ_three] at hv1v1 hv2v2 hv3v3 hv1v2 hv2v1 hv1v3 hv3v1 hv2v3 hv3v2
        -- Use linear_combination with orthonormality
        linear_combination c₁ * d₁ * hv1v1 + c₂ * d₂ * hv2v2 + c₃ * d₃ * hv3v3 +
          (c₁ * d₂ + c₂ * d₁) * hv1v2 + (c₁ * d₃ + c₃ * d₁) * hv1v3 + (c₂ * d₃ + c₃ * d₂) * hv2v3

-- ============================================================
-- THE CONTRADICTION
-- ============================================================

set_option maxHeartbeats 800000 in
/-- The n=3 case leads to a contradiction using the Parseval identity. -/
theorem no_three_square_identity_proof (nsi : NSquareIdentity 3) : False := by
  -- Setup: standard basis and image vectors
  let e₁ : Fin 3 → ℝ := stdBasis 0
  let e₂ : Fin 3 → ℝ := stdBasis 1
  let e₃ : Fin 3 → ℝ := stdBasis 2

  have he₁ : normSq e₁ = 1 := normSq_stdBasis 0
  have he₂ : normSq e₂ = 1 := normSq_stdBasis 1
  have he₃ : normSq e₃ = 1 := normSq_stdBasis 2

  have h12 : innerProd e₁ e₂ = 0 := by
    simp only [e₁, e₂, innerProd, stdBasis, Fin.sum_univ_three]
    simp (config := { decide := true }) only [ite_true, ite_false]
    ring
  have h13 : innerProd e₁ e₃ = 0 := by
    simp only [e₁, e₃, innerProd, stdBasis, Fin.sum_univ_three]
    simp (config := { decide := true }) only [ite_true, ite_false]
    ring
  have h23 : innerProd e₂ e₃ = 0 := by
    simp only [e₂, e₃, innerProd, stdBasis, Fin.sum_univ_three]
    simp (config := { decide := true }) only [ite_true, ite_false]
    ring

  let m₁₁ := nsi.mul e₁ e₁
  let m₁₂ := nsi.mul e₁ e₂
  let m₁₃ := nsi.mul e₁ e₃
  let m₂₁ := nsi.mul e₂ e₁
  let m₂₃ := nsi.mul e₂ e₃
  let m₃₁ := nsi.mul e₃ e₁

  -- Unit norms
  have hm₁₁ : normSq m₁₁ = 1 := by simp only [← nsi.norm_mul, he₁]; ring
  have hm₁₃ : normSq m₁₃ = 1 := by simp only [← nsi.norm_mul, he₁, he₃]; ring
  have hm₂₁ : normSq m₂₁ = 1 := by simp only [← nsi.norm_mul, he₂, he₁]; ring
  have hm₂₃ : normSq m₂₃ = 1 := by simp only [← nsi.norm_mul, he₂, he₃]; ring
  have hm₃₁ : normSq m₃₁ = 1 := by simp only [← nsi.norm_mul, he₃, he₁]; ring

  -- Column 1 orthonormality: {m₁₁, m₂₁, m₃₁}
  have col1_12 : innerProd m₁₁ m₂₁ = 0 := orthogonality_constraint nsi e₁ e₂ e₁ he₁ he₂ he₁ h12
  have col1_13 : innerProd m₁₁ m₃₁ = 0 := orthogonality_constraint nsi e₁ e₃ e₁ he₁ he₃ he₁ h13
  have col1_23 : innerProd m₂₁ m₃₁ = 0 := orthogonality_constraint nsi e₂ e₃ e₁ he₂ he₃ he₁ h23

  -- Row 2: m₂₁ ⊥ m₂₃
  have row2_13 : innerProd m₂₁ m₂₃ = 0 := orthogonality_constraint_right nsi e₂ e₁ e₃ he₂ he₁ he₃ h13

  -- Column 3: m₁₃ ⊥ m₂₃
  have col3_12 : innerProd m₁₃ m₂₃ = 0 := orthogonality_constraint nsi e₁ e₂ e₃ he₁ he₂ he₃ h12

  -- Cross-term constraint from |mul(e₁+e₂, e₁+e₃)|² = 4
  have hcross_zero : innerProd m₁₁ m₂₃ + innerProd m₁₃ m₂₁ = 0 := by
    have he12 : normSq (e₁ + e₂) = 2 := by rw [normSq_add, he₁, he₂, h12]; ring
    have he13 : normSq (e₁ + e₃) = 2 := by rw [normSq_add, he₁, he₃, h13]; ring
    have hbilin : nsi.mul (e₁ + e₂) (e₁ + e₃) = m₁₁ + m₁₃ + m₂₁ + m₂₃ := by
      calc nsi.mul (e₁ + e₂) (e₁ + e₃)
          = nsi.mul e₁ (e₁ + e₃) + nsi.mul e₂ (e₁ + e₃) := nsi.add_left e₁ e₂ (e₁ + e₃)
        _ = (nsi.mul e₁ e₁ + nsi.mul e₁ e₃) + (nsi.mul e₂ e₁ + nsi.mul e₂ e₃) := by
            rw [nsi.add_right, nsi.add_right]
        _ = m₁₁ + m₁₃ + m₂₁ + m₂₃ := by ring
    have hnorm : normSq (m₁₁ + m₁₃ + m₂₁ + m₂₃) = 4 := by
      rw [← hbilin, ← nsi.norm_mul, he12, he13]; ring
    have hexp : normSq (m₁₁ + m₁₃ + m₂₁ + m₂₃) =
        normSq (m₁₁ + m₁₃) + 2 * innerProd (m₁₁ + m₁₃) (m₂₁ + m₂₃) + normSq (m₂₁ + m₂₃) := by
      have : m₁₁ + m₁₃ + m₂₁ + m₂₃ = (m₁₁ + m₁₃) + (m₂₁ + m₂₃) := by ring
      rw [this, normSq_add]
    have row1_13 : innerProd m₁₁ m₁₃ = 0 := orthogonality_constraint_right nsi e₁ e₁ e₃ he₁ he₁ he₃ h13
    have hn1 : normSq (m₁₁ + m₁₃) = 2 := by rw [normSq_add, hm₁₁, hm₁₃, row1_13]; ring
    have hn2 : normSq (m₂₁ + m₂₃) = 2 := by rw [normSq_add, hm₂₁, hm₂₃, row2_13]; ring
    have hcross : innerProd (m₁₁ + m₁₃) (m₂₁ + m₂₃) = innerProd m₁₁ m₂₃ + innerProd m₁₃ m₂₁ := by
      rw [innerProd_add_left]
      rw [innerProd_add_right, innerProd_add_right]
      -- Now we have: innerProd m₁₁ m₂₁ + innerProd m₁₁ m₂₃ + innerProd m₁₃ m₂₁ + innerProd m₁₃ m₂₃
      rw [col1_12, col3_12]
      ring
    rw [hexp, hn1, hn2, hcross] at hnorm
    linarith

  -- From hcross_zero and the fact that m₁₃ ⊥ m₂₁ (column orthogonality won't help here)
  -- Actually we need: since m₁₃ is in span{m₂₁, m₃₁} (orthogonal to m₁₁), and m₁₃ is a unit vector...
  -- The key step: m₂₃ ⊥ m₂₁ (row2_13) and we need m₂₃ ⊥ m₁₁

  -- First show ⟨m₁₃, m₂₁⟩ = 0 implies ⟨m₁₁, m₂₃⟩ = 0
  -- But ⟨m₁₃, m₂₁⟩ = 0 only if m₁₃ ⊥ m₂₁

  -- Apply unit_ortho_two_eq_pm_third to m₂₃:
  -- m₂₃ ⊥ m₂₁ (row2_13), and we need m₂₃ ⊥ m₁₁
  -- From hcross_zero: ⟨m₁₁, m₂₃⟩ = -⟨m₁₃, m₂₁⟩

  -- For m₁₃: m₁₃ ⊥ m₁₁ (row 1 orthogonality)
  have row1_13' : innerProd m₁₁ m₁₃ = 0 := orthogonality_constraint_right nsi e₁ e₁ e₃ he₁ he₁ he₃ h13

  -- m₁₃ ⊥ m₁₁ and m₁₃ unit in ℝ³ with basis {m₁₁, m₂₁, m₃₁}
  -- So m₁₃ = ±m₂₁ or m₁₃ = ±m₃₁ or a combination
  -- Actually m₁₃ ⊥ m₁₂ too (row1_23), which gives more constraints

  -- Use Parseval: m₁₃ ∈ span{m₁₁, m₂₁, m₃₁} (column 1 is a basis)
  -- ⟨m₁₃, m₁₁⟩ = 0 (row1_13'), so coefficient of m₁₁ is 0
  -- Therefore m₁₃ ∈ span{m₂₁, m₃₁}

  -- Apply unit_ortho_two_eq_pm_third: m₂₃ with basis {m₁₁, m₂₁, m₃₁}
  -- m₂₃ ⊥ m₂₁ (row2_13)
  -- Need: m₂₃ ⊥ m₁₁?

  -- From hcross_zero: ⟨m₁₁, m₂₃⟩ = -⟨m₁₃, m₂₁⟩
  -- We need to determine ⟨m₁₃, m₂₁⟩

  -- Use inner_expansion_three on m₁₃ with basis {m₁₁, m₂₁, m₃₁}:
  have hm13_expand := inner_expansion_three m₁₁ m₂₁ m₃₁ m₁₃ hm₁₁ hm₂₁ hm₃₁ col1_12 col1_13 col1_23

  -- ⟨m₁₃, m₁₁⟩ = 0 (row1_13')
  have hm13_m11 : innerProd m₁₃ m₁₁ = 0 := by
    simp only [innerProd] at row1_13' ⊢
    convert row1_13' using 1; congr 1; ext i; ring

  -- So |m₁₃|² = 0 + ⟨m₁₃, m₂₁⟩² + ⟨m₁₃, m₃₁⟩²
  rw [hm13_m11] at hm13_expand
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at hm13_expand
  -- hm13_expand: 1 = ⟨m₁₃, m₂₁⟩² + ⟨m₁₃, m₃₁⟩²

  -- Similarly for m₂₃:
  have hm23_expand := inner_expansion_three m₁₁ m₂₁ m₃₁ m₂₃ hm₁₁ hm₂₁ hm₃₁ col1_12 col1_13 col1_23

  -- ⟨m₂₃, m₂₁⟩ = 0 (row2_13)
  have hm23_m21 : innerProd m₂₃ m₂₁ = 0 := by
    simp only [innerProd] at row2_13 ⊢
    convert row2_13 using 1; congr 1; ext i; ring

  rw [hm23_m21] at hm23_expand
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add] at hm23_expand
  -- hm23_expand: 1 = ⟨m₂₃, m₁₁⟩² + ⟨m₂₃, m₃₁⟩²

  -- From hcross_zero: ⟨m₁₁, m₂₃⟩ + ⟨m₁₃, m₂₁⟩ = 0
  -- So ⟨m₂₃, m₁₁⟩ = -⟨m₁₃, m₂₁⟩ (inner product is symmetric)
  have hm23_m11 : innerProd m₂₃ m₁₁ = -innerProd m₁₃ m₂₁ := by
    have h1 : innerProd m₁₁ m₂₃ = -innerProd m₁₃ m₂₁ := by linarith
    simp only [innerProd] at h1 ⊢
    convert h1 using 1; congr 1; ext i; ring

  -- Let x = ⟨m₁₃, m₂₁⟩ and y = ⟨m₁₃, m₃₁⟩
  -- From hm13_expand: x² + y² = 1
  -- From hm23_expand: (-x)² + ⟨m₂₃, m₃₁⟩² = 1, i.e., x² + ⟨m₂₃, m₃₁⟩² = 1
  -- So y² = ⟨m₂₃, m₃₁⟩², meaning |y| = |⟨m₂₃, m₃₁⟩|

  -- From col3_12: ⟨m₁₃, m₂₃⟩ = 0
  -- Expand using Parseval in basis {m₁₁, m₂₁, m₃₁}:
  -- ⟨m₁₃, m₂₃⟩ = ⟨m₁₃, m₁₁⟩⟨m₂₃, m₁₁⟩ + ⟨m₁₃, m₂₁⟩⟨m₂₃, m₂₁⟩ + ⟨m₁₃, m₃₁⟩⟨m₂₃, m₃₁⟩
  --            = 0·(-x) + x·0 + y·⟨m₂₃, m₃₁⟩
  --            = y · ⟨m₂₃, m₃₁⟩ = 0

  -- So either y = 0 or ⟨m₂₃, m₃₁⟩ = 0

  -- Case 1: y = 0, i.e., ⟨m₁₃, m₃₁⟩ = 0
  -- Then x² = 1, so x = ±1, meaning m₁₃ = ±m₂₁
  -- From hm23_expand with x² = 1: ⟨m₂₃, m₃₁⟩² = 0, so ⟨m₂₃, m₃₁⟩ = 0
  -- Then m₂₃ ⊥ m₂₁ and m₂₃ ⊥ m₃₁, so m₂₃ = ±m₁₁
  -- But then ⟨m₂₃, m₁₁⟩ = ±1 ≠ -x = ∓1... wait, this might be consistent
  -- Actually ⟨m₂₃, m₁₁⟩ = -x = ∓1, and if m₂₃ = ±m₁₁ then ⟨m₂₃, m₁₁⟩ = ±1
  -- So we need -x = ±1, i.e., x = ∓1, which is consistent with x = ±1
  -- Hmm, let's check: if x = 1, then ⟨m₂₃, m₁₁⟩ = -1, so m₂₃ = -m₁₁
  -- Then ⟨m₁₃, m₂₃⟩ = ⟨±m₂₁, -m₁₁⟩ = ∓⟨m₂₁, m₁₁⟩ = 0 ✓

  -- Case 2: ⟨m₂₃, m₃₁⟩ = 0
  -- Then from hm23_expand: ⟨m₂₃, m₁₁⟩² = 1, so ⟨m₂₃, m₁₁⟩ = ±1
  -- So m₂₃ = ±m₁₁ (since m₂₃ ⊥ m₂₁ and m₂₃ ⊥ m₃₁, must be ±m₁₁)
  -- Then ⟨m₂₃, m₁₁⟩ = ±1 = -x, so x = ∓1
  -- From hm13_expand: 1 + y² = 1, so y = 0
  -- Then m₁₃ = ±m₂₁

  -- In both cases: m₁₃ = ±m₂₁ and m₂₃ = ±m₁₁

  -- But wait, col3_12 says ⟨m₁₃, m₂₃⟩ = 0
  -- If m₁₃ = ±m₂₁ and m₂₃ = ±m₁₁, then ⟨m₁₃, m₂₃⟩ = ±⟨m₂₁, m₁₁⟩ = 0 ✓

  -- The contradiction comes from m₃₁:
  -- m₃₁ ⊥ m₂₁ (col1_23) and m₃₁ ⊥ m₁₁ (col1_13)
  -- So m₃₁ = ±m₁₂ or ±m₁₃ or... no, m₃₁ is the third column 1 vector

  -- Actually let's check row 3:
  -- m₃₁ ⊥ m₃₂ ⊥ m₃₃ and all are unit vectors

  -- The issue is that we have m₁₃ = ±m₂₁ but m₁₃ must also satisfy other constraints

  -- Let me try a cleaner approach: show that the system is overdetermined

  -- Key observation: From both cases, ⟨m₂₃, m₃₁⟩² = (1 - x²) = y²
  -- And from col3_12: y · ⟨m₂₃, m₃₁⟩ = 0
  -- If y ≠ 0, then ⟨m₂₃, m₃₁⟩ = 0, but then y² = ⟨m₂₃, m₃₁⟩² = 0, contradiction
  -- So y = 0, meaning ⟨m₁₃, m₃₁⟩ = 0

  -- With y = 0: x² = 1, so x = ±1
  -- And ⟨m₂₃, m₃₁⟩² = 1 - x² = 0, so ⟨m₂₃, m₃₁⟩ = 0

  -- So: m₁₃ ⊥ m₃₁ and m₂₃ ⊥ m₃₁

  -- Now use unit_ortho_two_eq_pm_third on m₁₃:
  -- m₁₃ ⊥ m₁₁ (row1_13') and m₁₃ ⊥ m₃₁ (just derived, y = 0)
  -- Hmm, but the basis is {m₁₁, m₂₁, m₃₁}, and m₁₃ ⊥ m₁₁ and m₁₃ ⊥ m₃₁
  -- So m₁₃ = ±m₂₁

  -- Similarly, m₂₃ ⊥ m₂₁ (row2_13) and m₂₃ ⊥ m₃₁ (just derived)
  -- So m₂₃ = ±m₁₁

  -- Now col3_12: ⟨m₁₃, m₂₃⟩ = ⟨±m₂₁, ±m₁₁⟩ = ±⟨m₂₁, m₁₁⟩ = 0 ✓

  -- But we need another constraint to get a contradiction...

  -- Actually, let's use a different approach: show that the existence of such vectors is impossible

  -- The problem is we need to show ⟨m₁₃, m₃₁⟩ = 0 from the constraints
  -- Let's derive this:

  have hy_eq : (innerProd m₁₃ m₃₁) * (innerProd m₂₃ m₃₁) = 0 := by
    -- From col3_12 and bilinear Parseval expansion
    have hbilin := inner_bilinear_expansion m₁₁ m₂₁ m₃₁ m₁₃ m₂₃ hm₁₁ hm₂₁ hm₃₁ col1_12 col1_13 col1_23
    -- hbilin: ⟨m₁₃, m₂₃⟩ = ⟨m₁₃, m₁₁⟩⟨m₂₃, m₁₁⟩ + ⟨m₁₃, m₂₁⟩⟨m₂₃, m₂₁⟩ + ⟨m₁₃, m₃₁⟩⟨m₂₃, m₃₁⟩
    rw [hm13_m11, hm23_m21] at hbilin
    simp only [zero_mul, mul_zero, zero_add, add_zero] at hbilin
    -- Now hbilin: ⟨m₁₃, m₂₃⟩ = ⟨m₁₃, m₃₁⟩ * ⟨m₂₃, m₃₁⟩
    -- And col3_12: ⟨m₁₃, m₂₃⟩ = 0
    linarith

  -- From hy_eq and the norm constraints, derive the contradiction
  -- Let x = ⟨m₁₃, m₂₁⟩, y = ⟨m₁₃, m₃₁⟩, z = ⟨m₂₃, m₃₁⟩
  -- From hm13_expand: x² + y² = 1
  -- From hm23_expand with hm23_m11: x² + z² = 1
  -- From hy_eq: y * z = 0
  -- Therefore y² = z², and with y * z = 0, both y = z = 0

  -- Substitute hm23_m11 into hm23_expand to get x² + z² = 1
  -- hm23_expand already has form: normSq m₂₃ = (innerProd m₂₃ m₁₁)² + 0 + (innerProd m₂₃ m₃₁)²
  -- (from line 932-933 where hm23_m21 was used to substitute)
  -- And hm23_m11: ⟨m₂₃, m₁₁⟩ = -⟨m₁₃, m₂₁⟩
  have hm23_expand' : (innerProd m₁₃ m₂₁)^2 + (innerProd m₂₃ m₃₁)^2 = 1 := by
    have h1 : normSq m₂₃ = 1 := hm₂₃
    rw [hm23_expand] at h1
    -- h1 now has form: 1 = (innerProd m₂₃ m₁₁)² + 0 + (innerProd m₂₃ m₃₁)²
    rw [hm23_m11] at h1
    -- h1 now has form: 1 = (-innerProd m₁₃ m₂₁)² + 0 + (innerProd m₂₃ m₃₁)²
    simp only [neg_sq, add_zero, zero_add] at h1
    linarith

  -- From x² + y² = 1 and x² + z² = 1, we get y² = z²
  have hyz_sq : (innerProd m₁₃ m₃₁)^2 = (innerProd m₂₃ m₃₁)^2 := by linarith

  -- From y * z = 0 and y² = z², we get y = 0 and z = 0
  have hy_zero : innerProd m₁₃ m₃₁ = 0 := by
    by_contra hy
    -- If y ≠ 0, then z = 0 (from y * z = 0)
    have hz : innerProd m₂₃ m₃₁ = 0 := by
      have := mul_eq_zero.mp hy_eq
      rcases this with h | h
      · exact absurd h hy
      · exact h
    -- But z = 0 implies z² = 0, and y² = z² implies y² = 0, so y = 0
    have : (innerProd m₂₃ m₃₁)^2 = 0 := by rw [hz]; ring
    have : (innerProd m₁₃ m₃₁)^2 = 0 := by linarith
    have : innerProd m₁₃ m₃₁ = 0 := by nlinarith [sq_nonneg (innerProd m₁₃ m₃₁)]
    exact hy this

  have hz_zero : innerProd m₂₃ m₃₁ = 0 := by
    have : (innerProd m₁₃ m₃₁)^2 = 0 := by rw [hy_zero]; ring
    have : (innerProd m₂₃ m₃₁)^2 = 0 := by linarith
    nlinarith [sq_nonneg (innerProd m₂₃ m₃₁)]

  -- With y = 0, from hm13_expand: x² = 1, so x = ±1
  have hx_sq : (innerProd m₁₃ m₂₁)^2 = 1 := by
    rw [hy_zero] at hm13_expand
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at hm13_expand
    linarith

  -- Now m₁₃ = ±m₂₁ (since m₁₃ ⊥ m₁₁ and m₁₃ ⊥ m₃₁)
  have hm13_eq_m21 : m₁₃ = m₂₁ ∨ m₁₃ = -m₂₁ := by
    apply unit_ortho_two_eq_pm_third m₁₁ m₃₁ m₂₁ m₁₃ hm₁₁ hm₃₁ hm₂₁
    · -- h12: ⟨m₁₁, m₃₁⟩ = 0
      exact col1_13
    · -- h13: ⟨m₁₁, m₂₁⟩ = 0
      exact col1_12
    · -- h23: ⟨m₃₁, m₂₁⟩ = 0
      simp only [innerProd] at col1_23 ⊢
      convert col1_23 using 1; congr 1; ext i; ring
    · exact hm₁₃
    · exact hm13_m11
    · exact hy_zero

  -- Similarly m₂₃ = ±m₁₁ (since m₂₃ ⊥ m₂₁ and m₂₃ ⊥ m₃₁)
  have hm23_eq_m11 : m₂₃ = m₁₁ ∨ m₂₃ = -m₁₁ := by
    apply unit_ortho_two_eq_pm_third m₂₁ m₃₁ m₁₁ m₂₃ hm₂₁ hm₃₁ hm₁₁
    · -- h12: ⟨m₂₁, m₃₁⟩ = 0
      exact col1_23
    · -- h13: ⟨m₂₁, m₁₁⟩ = 0
      simp only [innerProd] at col1_12 ⊢
      convert col1_12 using 1; congr 1; ext i; ring
    · -- h23: ⟨m₃₁, m₁₁⟩ = 0
      simp only [innerProd] at col1_13 ⊢
      convert col1_13 using 1; congr 1; ext i; ring
    · exact hm₂₃
    · exact hm23_m21
    · exact hz_zero

  -- Now we need m₃₃ for the final contradiction
  let m₃₃ := nsi.mul e₃ e₃
  have hm₃₃ : normSq m₃₃ = 1 := by simp only [← nsi.norm_mul, he₃]; ring

  -- Row 3 orthogonality: m₃₁ ⊥ m₃₃
  have row3_13 : innerProd m₃₁ m₃₃ = 0 := orthogonality_constraint_right nsi e₃ e₁ e₃ he₃ he₁ he₃ h13

  -- Column 3 orthogonalities: m₁₃ ⊥ m₃₃ and m₂₃ ⊥ m₃₃
  have col3_13 : innerProd m₁₃ m₃₃ = 0 := orthogonality_constraint nsi e₁ e₃ e₃ he₁ he₃ he₃ h13
  have col3_23 : innerProd m₂₃ m₃₃ = 0 := orthogonality_constraint nsi e₂ e₃ e₃ he₂ he₃ he₃ h23

  -- Since m₁₃ = ±m₂₁, we have m₃₃ ⊥ m₂₁
  have hm33_m21 : innerProd m₃₃ m₂₁ = 0 := by
    rcases hm13_eq_m21 with h | h
    · rw [← h]; simp only [innerProd] at col3_13 ⊢; convert col3_13 using 1; congr 1; ext i; ring
    · have : m₁₃ = -m₂₁ := h
      have hinner : innerProd m₃₃ m₂₁ = -innerProd m₃₃ m₁₃ := by
        simp only [innerProd]
        have : ∀ i, m₁₃ i = -m₂₁ i := fun i => by rw [h]; simp
        simp_rw [this]
        simp only [mul_neg, Finset.sum_neg_distrib, neg_neg]
      rw [hinner]
      simp only [innerProd] at col3_13 ⊢
      have hcomm : ∑ i : Fin 3, m₃₃ i * m₁₃ i = ∑ i : Fin 3, m₁₃ i * m₃₃ i := by
        congr 1; ext i; ring
      rw [hcomm, col3_13]; ring

  -- Since m₂₃ = ±m₁₁, we have m₃₃ ⊥ m₁₁
  have hm33_m11 : innerProd m₃₃ m₁₁ = 0 := by
    rcases hm23_eq_m11 with h | h
    · rw [← h]; simp only [innerProd] at col3_23 ⊢; convert col3_23 using 1; congr 1; ext i; ring
    · have : m₂₃ = -m₁₁ := h
      have hinner : innerProd m₃₃ m₁₁ = -innerProd m₃₃ m₂₃ := by
        simp only [innerProd]
        have : ∀ i, m₂₃ i = -m₁₁ i := fun i => by rw [h]; simp
        simp_rw [this]
        simp only [mul_neg, Finset.sum_neg_distrib, neg_neg]
      rw [hinner]
      simp only [innerProd] at col3_23 ⊢
      have hcomm : ∑ i : Fin 3, m₃₃ i * m₂₃ i = ∑ i : Fin 3, m₂₃ i * m₃₃ i := by
        congr 1; ext i; ring
      rw [hcomm, col3_23]; ring

  -- By unit_ortho_two_eq_pm_third, m₃₃ = ±m₃₁
  have hm33_eq_m31 : m₃₃ = m₃₁ ∨ m₃₃ = -m₃₁ := by
    apply unit_ortho_two_eq_pm_third m₁₁ m₂₁ m₃₁ m₃₃ hm₁₁ hm₂₁ hm₃₁ col1_12 col1_13 col1_23 hm₃₃
    · exact hm33_m11
    · exact hm33_m21

  -- But row3_13 says ⟨m₃₁, m₃₃⟩ = 0
  -- If m₃₃ = ±m₃₁, then ⟨m₃₁, m₃₃⟩ = ±1 ≠ 0. Contradiction!
  rcases hm33_eq_m31 with h | h
  · -- m₃₃ = m₃₁, so ⟨m₃₁, m₃₃⟩ = ⟨m₃₁, m₃₁⟩ = 1
    have : innerProd m₃₁ m₃₃ = innerProd m₃₁ m₃₁ := by rw [h]
    rw [this] at row3_13
    have hm31_self : innerProd m₃₁ m₃₁ = 1 := by
      rw [← normSq_eq_innerProd]; exact hm₃₁
    linarith
  · -- m₃₃ = -m₃₁, so ⟨m₃₁, m₃₃⟩ = ⟨m₃₁, -m₃₁⟩ = -1
    have : innerProd m₃₁ m₃₃ = innerProd m₃₁ (-m₃₁) := by rw [h]
    rw [this] at row3_13
    have hm31_neg : innerProd m₃₁ (-m₃₁) = -1 := by
      simp only [innerProd, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
      have hm31_self : innerProd m₃₁ m₃₁ = 1 := by
        rw [← normSq_eq_innerProd]; exact hm₃₁
      simp only [innerProd] at hm31_self
      linarith
    linarith

/-- Hurwitz's Theorem: There is no 3-square identity.

    This is equivalent to saying there is no 3-dimensional normed
    division algebra, or equivalently, no norm-multiplicative
    bilinear product on ℝ³. -/
theorem no_three_square_identity : ∀ f : NSquareIdentity 3, False := by
  intro nsi
  -- The 3 standard basis vectors
  let e₁ : Fin 3 → ℝ := stdBasis 0
  let e₂ : Fin 3 → ℝ := stdBasis 1
  let e₃ : Fin 3 → ℝ := stdBasis 2

  -- Each has norm 1
  have he₁ : normSq e₁ = 1 := normSq_stdBasis 0
  have he₂ : normSq e₂ = 1 := normSq_stdBasis 1
  have he₃ : normSq e₃ = 1 := normSq_stdBasis 2

  -- They are pairwise orthogonal
  have h12 : innerProd e₁ e₂ = 0 := by
    show innerProd (stdBasis 0) (stdBasis 1) = 0
    simp only [innerProd, stdBasis, Fin.sum_univ_three, Fin.isValue]
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceEq, ↓reduceIte]
    norm_num
  have h13 : innerProd e₁ e₃ = 0 := by
    show innerProd (stdBasis 0) (stdBasis 2) = 0
    simp only [innerProd, stdBasis, Fin.sum_univ_three, Fin.isValue]
    simp only [Fin.zero_eta, Fin.reduceEq, ↓reduceIte]
    norm_num
  have h23 : innerProd e₂ e₃ = 0 := by
    show innerProd (stdBasis 1) (stdBasis 2) = 0
    simp only [innerProd, stdBasis, Fin.sum_univ_three, Fin.isValue]
    simp only [Fin.mk_one, Fin.reduceEq, ↓reduceIte]
    norm_num

  -- Define the 9 image vectors M[i,j] = mul(eᵢ, eⱼ)
  let m₁₁ := nsi.mul e₁ e₁
  let m₁₂ := nsi.mul e₁ e₂
  let m₁₃ := nsi.mul e₁ e₃
  let m₂₁ := nsi.mul e₂ e₁
  let m₂₂ := nsi.mul e₂ e₂
  let m₂₃ := nsi.mul e₂ e₃
  let m₃₁ := nsi.mul e₃ e₁
  let m₃₂ := nsi.mul e₃ e₂
  let m₃₃ := nsi.mul e₃ e₃

  -- LEFT orthogonality: columns of M are orthonormal
  -- Column 1: m₁₁, m₂₁, m₃₁ pairwise orthogonal
  have col1_12 : innerProd m₁₁ m₂₁ = 0 := orthogonality_constraint nsi e₁ e₂ e₁ he₁ he₂ he₁ h12
  have col1_13 : innerProd m₁₁ m₃₁ = 0 := orthogonality_constraint nsi e₁ e₃ e₁ he₁ he₃ he₁ h13
  have col1_23 : innerProd m₂₁ m₃₁ = 0 := orthogonality_constraint nsi e₂ e₃ e₁ he₂ he₃ he₁ h23

  -- RIGHT orthogonality: rows of M are orthonormal
  -- Row 1: m₁₁, m₁₂, m₁₃ pairwise orthogonal
  have row1_12 : innerProd m₁₁ m₁₂ = 0 := orthogonality_constraint_right nsi e₁ e₁ e₂ he₁ he₁ he₂ h12
  have row1_13 : innerProd m₁₁ m₁₃ = 0 := orthogonality_constraint_right nsi e₁ e₁ e₃ he₁ he₁ he₃ h13
  have row1_23 : innerProd m₁₂ m₁₃ = 0 := orthogonality_constraint_right nsi e₁ e₂ e₃ he₁ he₂ he₃ h23

  -- Additional orthogonality constraints we need
  -- Column 3: m₁₃ ⊥ m₂₃
  have col3_12 : innerProd m₁₃ m₂₃ = 0 := orthogonality_constraint nsi e₁ e₂ e₃ he₁ he₂ he₃ h12
  -- Row 2: m₂₁ ⊥ m₂₃
  have row2_13 : innerProd m₂₁ m₂₃ = 0 := orthogonality_constraint_right nsi e₂ e₁ e₃ he₂ he₁ he₃ h13

  -- Unit norms of image vectors
  have hm₁₁ : normSq m₁₁ = 1 := by simp only [← nsi.norm_mul, he₁]; ring
  have hm₁₃ : normSq m₁₃ = 1 := by simp only [← nsi.norm_mul, he₁, he₃]; ring
  have hm₂₁ : normSq m₂₁ = 1 := by simp only [← nsi.norm_mul, he₂, he₁]; ring
  have hm₂₃ : normSq m₂₃ = 1 := by simp only [← nsi.norm_mul, he₂, he₃]; ring

  -- Key identity: |mul(e₁+e₂, e₁+e₃)|² = |e₁+e₂|² · |e₁+e₃|² = 2 · 2 = 4
  -- First compute |e₁+e₂|² and |e₁+e₃|²
  have he12_norm : normSq (e₁ + e₂) = 2 := by rw [normSq_add, he₁, he₂, h12]; ring
  have he13_norm : normSq (e₁ + e₃) = 2 := by rw [normSq_add, he₁, he₃, h13]; ring

  -- By bilinearity: mul(e₁+e₂, e₁+e₃) = m₁₁ + m₁₃ + m₂₁ + m₂₃
  have hbilin : nsi.mul (e₁ + e₂) (e₁ + e₃) = m₁₁ + m₁₃ + m₂₁ + m₂₃ := by
    calc nsi.mul (e₁ + e₂) (e₁ + e₃)
        = nsi.mul e₁ (e₁ + e₃) + nsi.mul e₂ (e₁ + e₃) := nsi.add_left e₁ e₂ (e₁ + e₃)
      _ = (nsi.mul e₁ e₁ + nsi.mul e₁ e₃) + (nsi.mul e₂ e₁ + nsi.mul e₂ e₃) := by
          rw [nsi.add_right, nsi.add_right]
      _ = m₁₁ + m₁₃ + m₂₁ + m₂₃ := by ring

  -- By norm-multiplicativity: |mul(e₁+e₂, e₁+e₃)|² = 4
  have hnorm_target : normSq (nsi.mul (e₁ + e₂) (e₁ + e₃)) = 4 := by
    rw [← nsi.norm_mul, he12_norm, he13_norm]; ring

  -- So |m₁₁ + m₁₃ + m₂₁ + m₂₃|² = 4
  have hsum_norm : normSq (m₁₁ + m₁₃ + m₂₁ + m₂₃) = 4 := by rw [← hbilin]; exact hnorm_target

  -- Expand using normSq_add
  -- |a + b + c + d|² = |a|² + |b|² + |c|² + |d|² + 2⟨a,b⟩ + 2⟨a,c⟩ + 2⟨a,d⟩ + 2⟨b,c⟩ + 2⟨b,d⟩ + 2⟨c,d⟩
  -- Group as ((m₁₁ + m₁₃) + (m₂₁ + m₂₃))
  have hexpand1 : normSq (m₁₁ + m₁₃ + m₂₁ + m₂₃) =
      normSq (m₁₁ + m₁₃) + 2 * innerProd (m₁₁ + m₁₃) (m₂₁ + m₂₃) + normSq (m₂₁ + m₂₃) := by
    have : m₁₁ + m₁₃ + m₂₁ + m₂₃ = (m₁₁ + m₁₃) + (m₂₁ + m₂₃) := by ring
    rw [this, normSq_add]

  -- |m₁₁ + m₁₃|² = 2 (using row1_13)
  have hnorm_11_13 : normSq (m₁₁ + m₁₃) = 2 := by
    rw [normSq_add, hm₁₁, hm₁₃, row1_13]; ring

  -- |m₂₁ + m₂₃|² = 2 (using row2_13)
  have hnorm_21_23 : normSq (m₂₁ + m₂₃) = 2 := by
    rw [normSq_add, hm₂₁, hm₂₃, row2_13]; ring

  -- Expand the cross term
  -- ⟨m₁₁ + m₁₃, m₂₁ + m₂₃⟩ = ⟨m₁₁,m₂₁⟩ + ⟨m₁₁,m₂₃⟩ + ⟨m₁₃,m₂₁⟩ + ⟨m₁₃,m₂₃⟩
  have hcross : innerProd (m₁₁ + m₁₃) (m₂₁ + m₂₃) =
      innerProd m₁₁ m₂₁ + innerProd m₁₁ m₂₃ + innerProd m₁₃ m₂₁ + innerProd m₁₃ m₂₃ := by
    simp only [innerProd, Pi.add_apply]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    congr 1; ext i; ring

  -- Substitute known zeros
  have hcross2 : innerProd (m₁₁ + m₁₃) (m₂₁ + m₂₃) = innerProd m₁₁ m₂₃ + innerProd m₁₃ m₂₁ := by
    rw [hcross, col1_12, col3_12]; ring

  -- From hsum_norm and expansions: 4 = 2 + 2*(innerProd m₁₁ m₂₃ + innerProd m₁₃ m₂₁) + 2
  -- So innerProd m₁₁ m₂₃ + innerProd m₁₃ m₂₁ = 0
  have hcross_zero : innerProd m₁₁ m₂₃ + innerProd m₁₃ m₂₁ = 0 := by
    have := hsum_norm
    rw [hexpand1, hnorm_11_13, hnorm_21_23, hcross2] at this
    linarith

  -- DIAGONAL CONSTRAINT: |mul(e₁+e₂, e₁+e₂)|² = 4
  -- mul(e₁+e₂, e₁+e₂) = m₁₁ + m₁₂ + m₂₁ + m₂₂
  have hbilin_diag : nsi.mul (e₁ + e₂) (e₁ + e₂) = m₁₁ + m₁₂ + m₂₁ + m₂₂ := by
    calc nsi.mul (e₁ + e₂) (e₁ + e₂)
        = nsi.mul e₁ (e₁ + e₂) + nsi.mul e₂ (e₁ + e₂) := nsi.add_left e₁ e₂ (e₁ + e₂)
      _ = (nsi.mul e₁ e₁ + nsi.mul e₁ e₂) + (nsi.mul e₂ e₁ + nsi.mul e₂ e₂) := by
          rw [nsi.add_right, nsi.add_right]
      _ = m₁₁ + m₁₂ + m₂₁ + m₂₂ := by ring

  have hnorm_diag : normSq (nsi.mul (e₁ + e₂) (e₁ + e₂)) = 4 := by
    rw [← nsi.norm_mul, he12_norm]; ring

  have hsum_diag : normSq (m₁₁ + m₁₂ + m₂₁ + m₂₂) = 4 := by rw [← hbilin_diag]; exact hnorm_diag

  -- Norms needed for diagonal constraint
  have hm₁₂' : normSq m₁₂ = 1 := by simp only [← nsi.norm_mul, he₁, he₂]; ring
  have hm₂₂' : normSq m₂₂ = 1 := by simp only [← nsi.norm_mul, he₂]; ring

  -- Orthogonality: m₂₁ ⊥ m₂₂ (column 1) and m₁₂ ⊥ m₂₂ (column 2)
  have col1_12' : innerProd m₂₁ m₂₂ = 0 := orthogonality_constraint_right nsi e₂ e₁ e₂ he₂ he₁ he₂ h12

  -- Expand: group as ((m₁₁ + m₂₂) + (m₁₂ + m₂₁))
  have hexpand_diag : normSq (m₁₁ + m₁₂ + m₂₁ + m₂₂) =
      normSq (m₁₁ + m₂₂) + 2 * innerProd (m₁₁ + m₂₂) (m₁₂ + m₂₁) + normSq (m₁₂ + m₂₁) := by
    have : m₁₁ + m₁₂ + m₂₁ + m₂₂ = (m₁₁ + m₂₂) + (m₁₂ + m₂₁) := by ring
    rw [this, normSq_add]

  have hnorm_11_22 : normSq (m₁₁ + m₂₂) = 2 + 2 * innerProd m₁₁ m₂₂ := by
    rw [normSq_add, hm₁₁, hm₂₂']; ring

  have hnorm_12_21 : normSq (m₁₂ + m₂₁) = 2 + 2 * innerProd m₁₂ m₂₁ := by
    rw [normSq_add, hm₁₂', hm₂₁]; ring

  -- Cross term: ⟨m₁₁ + m₂₂, m₁₂ + m₂₁⟩
  have hcross_diag : innerProd (m₁₁ + m₂₂) (m₁₂ + m₂₁) =
      innerProd m₁₁ m₁₂ + innerProd m₁₁ m₂₁ + innerProd m₂₂ m₁₂ + innerProd m₂₂ m₂₁ := by
    simp only [innerProd, Pi.add_apply]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    congr 1; ext i; ring

  -- Simplify: row1_12, col1_12, col2_12 (need col2_12 = ⟨m₁₂, m₂₂⟩ = 0, so ⟨m₂₂, m₁₂⟩ = 0)
  have col2_12' : innerProd m₂₂ m₁₂ = 0 := by
    have h := orthogonality_constraint nsi e₁ e₂ e₂ he₁ he₂ he₂ h12
    simp only [innerProd] at h ⊢
    convert h using 1; congr 1; ext i; ring
  have col1_21 : innerProd m₂₂ m₂₁ = 0 := by
    have h := col1_12'
    simp only [innerProd] at h ⊢
    convert h using 1; congr 1; ext i; ring

  have hcross_diag2 : innerProd (m₁₁ + m₂₂) (m₁₂ + m₂₁) = 0 := by
    rw [hcross_diag, row1_12, col1_12, col2_12', col1_21]; ring

  -- From hsum_diag: 4 = (2 + 2*⟨m₁₁,m₂₂⟩) + 0 + (2 + 2*⟨m₁₂,m₂₁⟩)
  -- So ⟨m₁₁,m₂₂⟩ + ⟨m₁₂,m₂₁⟩ = 0
  have hdiag_zero : innerProd m₁₁ m₂₂ + innerProd m₁₂ m₂₁ = 0 := by
    have := hsum_diag
    rw [hexpand_diag, hnorm_11_22, hnorm_12_21, hcross_diag2] at this
    linarith

  -- Now we derive a contradiction using another combination
  -- Consider |mul(e₁+e₂, e₂+e₃)|² = 2 · 2 = 4
  have he23_norm : normSq (e₂ + e₃) = 2 := by rw [normSq_add, he₂, he₃, h23]; ring

  -- mul(e₁+e₂, e₂+e₃) = m₁₂ + m₁₃ + m₂₂ + m₂₃
  have hbilin2 : nsi.mul (e₁ + e₂) (e₂ + e₃) = m₁₂ + m₁₃ + m₂₂ + m₂₃ := by
    calc nsi.mul (e₁ + e₂) (e₂ + e₃)
        = nsi.mul e₁ (e₂ + e₃) + nsi.mul e₂ (e₂ + e₃) := nsi.add_left e₁ e₂ (e₂ + e₃)
      _ = (nsi.mul e₁ e₂ + nsi.mul e₁ e₃) + (nsi.mul e₂ e₂ + nsi.mul e₂ e₃) := by
          rw [nsi.add_right, nsi.add_right]
      _ = m₁₂ + m₁₃ + m₂₂ + m₂₃ := by ring

  have hnorm_target2 : normSq (nsi.mul (e₁ + e₂) (e₂ + e₃)) = 4 := by
    rw [← nsi.norm_mul, he12_norm, he23_norm]; ring

  -- Additional orthogonality constraints
  -- Column 2: m₁₂ ⊥ m₂₂
  have col2_12 : innerProd m₁₂ m₂₂ = 0 := orthogonality_constraint nsi e₁ e₂ e₂ he₁ he₂ he₂ h12
  -- Row 2: m₂₂ ⊥ m₂₃
  have row2_23 : innerProd m₂₂ m₂₃ = 0 := orthogonality_constraint_right nsi e₂ e₂ e₃ he₂ he₂ he₃ h23

  have hm₁₂ : normSq m₁₂ = 1 := by simp only [← nsi.norm_mul, he₁, he₂]; ring
  have hm₂₂ : normSq m₂₂ = 1 := by simp only [← nsi.norm_mul, he₂]; ring

  -- Expand |m₁₂ + m₁₃ + m₂₂ + m₂₃|² = 4
  have hsum_norm2 : normSq (m₁₂ + m₁₃ + m₂₂ + m₂₃) = 4 := by rw [← hbilin2]; exact hnorm_target2

  -- Group as ((m₁₂ + m₂₂) + (m₁₃ + m₂₃))
  have hexpand2 : normSq (m₁₂ + m₁₃ + m₂₂ + m₂₃) =
      normSq (m₁₂ + m₂₂) + 2 * innerProd (m₁₂ + m₂₂) (m₁₃ + m₂₃) + normSq (m₁₃ + m₂₃) := by
    have : m₁₂ + m₁₃ + m₂₂ + m₂₃ = (m₁₂ + m₂₂) + (m₁₃ + m₂₃) := by ring
    rw [this, normSq_add]

  have hnorm_12_22 : normSq (m₁₂ + m₂₂) = 2 := by
    rw [normSq_add, hm₁₂, hm₂₂, col2_12]; ring

  have hnorm_13_23 : normSq (m₁₃ + m₂₃) = 2 := by
    rw [normSq_add, hm₁₃, hm₂₃, col3_12]; ring

  -- Cross term: ⟨m₁₂ + m₂₂, m₁₃ + m₂₃⟩
  have hcross3 : innerProd (m₁₂ + m₂₂) (m₁₃ + m₂₃) =
      innerProd m₁₂ m₁₃ + innerProd m₁₂ m₂₃ + innerProd m₂₂ m₁₃ + innerProd m₂₂ m₂₃ := by
    simp only [innerProd, Pi.add_apply]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    congr 1; ext i; ring

  have hcross4 : innerProd (m₁₂ + m₂₂) (m₁₃ + m₂₃) = innerProd m₁₂ m₂₃ + innerProd m₂₂ m₁₃ := by
    rw [hcross3, row1_23, row2_23]; ring

  -- From hsum_norm2: 4 = 2 + 2*(innerProd m₁₂ m₂₃ + innerProd m₂₂ m₁₃) + 2
  have hcross_zero2 : innerProd m₁₂ m₂₃ + innerProd m₂₂ m₁₃ = 0 := by
    have := hsum_norm2
    rw [hexpand2, hnorm_12_22, hnorm_13_23, hcross4] at this
    linarith

  -- Now use a third combination: |mul(e₂+e₃, e₁+e₃)|² = 4
  -- mul(e₂+e₃, e₁+e₃) = m₂₁ + m₂₃ + m₃₁ + m₃₃
  have hbilin3 : nsi.mul (e₂ + e₃) (e₁ + e₃) = m₂₁ + m₂₃ + m₃₁ + m₃₃ := by
    calc nsi.mul (e₂ + e₃) (e₁ + e₃)
        = nsi.mul e₂ (e₁ + e₃) + nsi.mul e₃ (e₁ + e₃) := nsi.add_left e₂ e₃ (e₁ + e₃)
      _ = (nsi.mul e₂ e₁ + nsi.mul e₂ e₃) + (nsi.mul e₃ e₁ + nsi.mul e₃ e₃) := by
          rw [nsi.add_right, nsi.add_right]
      _ = m₂₁ + m₂₃ + m₃₁ + m₃₃ := by ring

  have hnorm_target3 : normSq (nsi.mul (e₂ + e₃) (e₁ + e₃)) = 4 := by
    rw [← nsi.norm_mul, he23_norm, he13_norm]; ring

  -- Additional constraints
  have col1_23 : innerProd m₂₁ m₃₁ = 0 := orthogonality_constraint nsi e₂ e₃ e₁ he₂ he₃ he₁ h23
  have col3_23 : innerProd m₂₃ m₃₃ = 0 := orthogonality_constraint nsi e₂ e₃ e₃ he₂ he₃ he₃ h23
  have row3_13 : innerProd m₃₁ m₃₃ = 0 := orthogonality_constraint_right nsi e₃ e₁ e₃ he₃ he₁ he₃ h13

  have hm₃₁ : normSq m₃₁ = 1 := by simp only [← nsi.norm_mul, he₃, he₁]; ring
  have hm₃₃ : normSq m₃₃ = 1 := by simp only [← nsi.norm_mul, he₃]; ring

  have hsum_norm3 : normSq (m₂₁ + m₂₃ + m₃₁ + m₃₃) = 4 := by rw [← hbilin3]; exact hnorm_target3

  -- Group as ((m₂₁ + m₃₁) + (m₂₃ + m₃₃))
  have hexpand3 : normSq (m₂₁ + m₂₃ + m₃₁ + m₃₃) =
      normSq (m₂₁ + m₃₁) + 2 * innerProd (m₂₁ + m₃₁) (m₂₃ + m₃₃) + normSq (m₂₃ + m₃₃) := by
    have : m₂₁ + m₂₃ + m₃₁ + m₃₃ = (m₂₁ + m₃₁) + (m₂₃ + m₃₃) := by ring
    rw [this, normSq_add]

  have hnorm_21_31 : normSq (m₂₁ + m₃₁) = 2 := by
    rw [normSq_add, hm₂₁, hm₃₁, col1_23]; ring

  have hnorm_23_33 : normSq (m₂₃ + m₃₃) = 2 := by
    rw [normSq_add, hm₂₃, hm₃₃, col3_23]; ring

  have hcross5 : innerProd (m₂₁ + m₃₁) (m₂₃ + m₃₃) =
      innerProd m₂₁ m₂₃ + innerProd m₂₁ m₃₃ + innerProd m₃₁ m₂₃ + innerProd m₃₁ m₃₃ := by
    simp only [innerProd, Pi.add_apply]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    congr 1; ext i; ring

  have hcross6 : innerProd (m₂₁ + m₃₁) (m₂₃ + m₃₃) = innerProd m₂₁ m₃₃ + innerProd m₃₁ m₂₃ := by
    rw [hcross5, row2_13, row3_13]; ring

  have hcross_zero3 : innerProd m₂₁ m₃₃ + innerProd m₃₁ m₂₃ = 0 := by
    have := hsum_norm3
    rw [hexpand3, hnorm_21_31, hnorm_23_33, hcross6] at this
    linarith

  -- The contradiction comes from the over-determined system
  -- We have 6 "cross" inner products: ⟨m₁₁,m₂₃⟩, ⟨m₁₃,m₂₁⟩, ⟨m₁₂,m₂₃⟩, ⟨m₂₂,m₁₃⟩, ⟨m₂₁,m₃₃⟩, ⟨m₃₁,m₂₃⟩
  -- And constraints that they sum to 0 in various combinations
  -- The key is that we can derive a contradiction from the geometry

  -- Use symmetry: consider |mul(e₁, e₁+e₂+e₃)|² = 1 · 3 = 3
  have he123_norm : normSq (e₁ + e₂ + e₃) = 3 := by
    have h1 : normSq (e₁ + e₂ + e₃) = normSq (e₁ + e₂) + 2 * innerProd (e₁ + e₂) e₃ + normSq e₃ := by
      have : e₁ + e₂ + e₃ = (e₁ + e₂) + e₃ := by ring
      rw [this, normSq_add]
    have hcross_e : innerProd (e₁ + e₂) e₃ = innerProd e₁ e₃ + innerProd e₂ e₃ := by
      simp only [innerProd, Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      congr 1; ext i; ring
    rw [h1, he12_norm, hcross_e, h13, h23, he₃]; ring

  -- mul(e₁, e₁+e₂+e₃) = m₁₁ + m₁₂ + m₁₃
  have hbilin_row1 : nsi.mul e₁ (e₁ + e₂ + e₃) = m₁₁ + m₁₂ + m₁₃ := by
    calc nsi.mul e₁ (e₁ + e₂ + e₃)
        = nsi.mul e₁ (e₁ + (e₂ + e₃)) := by ring_nf
      _ = nsi.mul e₁ e₁ + nsi.mul e₁ (e₂ + e₃) := nsi.add_right e₁ e₁ (e₂ + e₃)
      _ = nsi.mul e₁ e₁ + (nsi.mul e₁ e₂ + nsi.mul e₁ e₃) := by rw [nsi.add_right]
      _ = m₁₁ + m₁₂ + m₁₃ := by ring

  have hnorm_row1 : normSq (nsi.mul e₁ (e₁ + e₂ + e₃)) = 3 := by
    rw [← nsi.norm_mul, he₁, he123_norm]; ring

  have hsum_row1 : normSq (m₁₁ + m₁₂ + m₁₃) = 3 := by rw [← hbilin_row1]; exact hnorm_row1

  -- |m₁₁ + m₁₂ + m₁₃|² = 3 with all pairwise orthogonal gives 1+1+1 = 3 ✓

  -- Now the key: consider mul((e₁+e₂+e₃), (e₁+e₂+e₃)) = sum of all 9 m_ij
  -- |...|² = 9

  -- Instead, let's use a more direct approach: the scalar triple product constraint
  -- In ℝ³, for any orthonormal basis {u,v,w}, we have det[u|v|w] = ±1

  -- The issue is that both {m₁₁, m₂₁, m₃₁} and {m₁₁, m₁₂, m₁₃} must be orthonormal bases
  -- This severely constrains the possible configurations

  -- For the final contradiction, we use:
  -- From the 3 constraints hcross_zero, hcross_zero2, hcross_zero3 and
  -- the fact that all these vectors are unit vectors in ℝ³,
  -- the system is overdetermined.

  -- Actually, let's derive a direct numerical contradiction
  -- Consider |mul(e₁+e₂+e₃, e₁)|² = 3
  have hbilin_col1 : nsi.mul (e₁ + e₂ + e₃) e₁ = m₁₁ + m₂₁ + m₃₁ := by
    calc nsi.mul (e₁ + e₂ + e₃) e₁
        = nsi.mul (e₁ + (e₂ + e₃)) e₁ := by ring_nf
      _ = nsi.mul e₁ e₁ + nsi.mul (e₂ + e₃) e₁ := nsi.add_left e₁ (e₂ + e₃) e₁
      _ = nsi.mul e₁ e₁ + (nsi.mul e₂ e₁ + nsi.mul e₃ e₁) := by rw [nsi.add_left]
      _ = m₁₁ + m₂₁ + m₃₁ := by ring

  have hnorm_col1 : normSq (nsi.mul (e₁ + e₂ + e₃) e₁) = 3 := by
    rw [← nsi.norm_mul, he123_norm, he₁]; ring

  have hsum_col1 : normSq (m₁₁ + m₂₁ + m₃₁) = 3 := by rw [← hbilin_col1]; exact hnorm_col1

  -- Both {m₁₁, m₂₁, m₃₁} and {m₁₁, m₁₂, m₁₃} are orthonormal sets in ℝ³
  -- By the constraint that m₁₂, m₁₃ ⊥ m₁₁, they must lie in span{m₂₁, m₃₁}
  -- This means det(m₁₂, m₂₁, m₃₁) = 0 and det(m₁₃, m₂₁, m₃₁) = 0

  -- But m₁₂ ⊥ m₁₃ and both are unit vectors in a 2D space
  -- So they form an orthonormal basis of that 2D space
  -- This means {m₁₂, m₁₃} = {±m₂₁, ±m₃₁} or rotations thereof

  -- The constraint hcross_zero says ⟨m₁₁, m₂₃⟩ + ⟨m₁₃, m₂₁⟩ = 0
  -- Since m₁₃ ∈ span{m₂₁, m₃₁}, write m₁₃ = α·m₂₁ + β·m₃₁
  -- Then ⟨m₁₃, m₂₁⟩ = α
  -- So ⟨m₁₁, m₂₃⟩ = -α

  -- The proof requires showing these constraints are inconsistent
  -- This is ultimately a finite computation in ℝ³

  -- For now, we note that a complete formalization would require
  -- either basis decomposition machinery or direct coordinate computation
  -- The mathematical argument is sound; the Lean formalization needs
  -- additional linear algebra infrastructure

  -- Here we use the key observation: the 9 vectors m_ij with the
  -- row/column orthogonality constraints cannot all be unit vectors in ℝ³
  -- This is because the constraints force certain vectors to coincide,
  -- which then violates the norm identity for specific combinations

  -- Use the Parseval-based proof
  exact no_three_square_identity_proof nsi

-- ============================================================
-- PART 8: Hurwitz's Complete Theorem
-- ============================================================

/-
  Hurwitz's Complete Theorem: An n-square identity exists if and only if
  n ∈ {1, 2, 4, 8}.

  We've proven the "if" direction (existence for these values) and
  stated the "only if" direction for n = 3. The complete theorem
  extends this to all n ∉ {1, 2, 4, 8}.
-/

/-- The set of dimensions admitting n-square identities -/
def admissibleDimensions : Set ℕ := {1, 2, 4, 8}

/-- Positive direction: n-square identities exist for n = 1, 2, 4, 8 -/
theorem identities_exist_for_admissible :
    ∀ n ∈ admissibleDimensions, Nonempty (NSquareIdentity n) := by
  intro n hn
  simp only [admissibleDimensions, Set.mem_insert_iff, Set.mem_singleton_iff] at hn
  rcases hn with rfl | rfl | rfl | rfl
  · exact ⟨oneSquareIdentity⟩
  · exact ⟨twoSquareIdentity⟩
  · exact ⟨fourSquareIdentity⟩
  · exact ⟨eight_square_identity_exists⟩

/-- **Axiom:** n-square identities do not exist for n ∉ {1, 2, 4, 8}.

    This captures the full negative direction of Hurwitz's theorem:
    - n = 3: Contradiction from overdetermined orthonormality (proven via no_three_square_identity)
    - n = 5, 6, 7: Similar overdetermined systems lead to contradictions
    - n > 8: The Cayley-Dickson construction fails to produce normed algebras beyond octonions

    The proof for n = 3 is formalized above. The cases n = 5, 6, 7 and n > 8
    require additional machinery (Clifford algebras, representation theory). -/
axiom hurwitz_only_if (n : ℕ) (hn : n > 0) (nsi : NSquareIdentity n) :
    n ∈ admissibleDimensions

/-- Hurwitz's Theorem: n-square identities exist only for n ∈ {1, 2, 4, 8} -/
theorem hurwitz_theorem (n : ℕ) (hn : n > 0) :
    Nonempty (NSquareIdentity n) ↔ n ∈ admissibleDimensions := by
  constructor
  · -- Only if direction: from the axiom
    intro ⟨nsi⟩
    exact hurwitz_only_if n hn nsi
  · -- If direction: we've constructed the identities
    intro hn'
    exact identities_exist_for_admissible n hn'

-- ============================================================
-- PART 9: The Four Division Algebras
-- ============================================================

/-
  The n-square identities correspond exactly to the four normed division algebras:

  | n | Algebra    | Symbol | Discovered    | Properties           |
  |---|------------|--------|---------------|----------------------|
  | 1 | Reals      | ℝ      | Ancient       | Ordered, complete    |
  | 2 | Complex    | ℂ      | 16th century  | Algebraically closed |
  | 4 | Quaternions| ℍ      | Hamilton 1843 | Non-commutative      |
  | 8 | Octonions  | 𝕆      | Cayley 1845   | Non-associative      |

  Each step in the sequence loses a property:
  ℝ → ℂ : lose ordering
  ℂ → ℍ : lose commutativity
  ℍ → 𝕆 : lose associativity

  After octonions, we cannot continue: the next step would require
  losing a property essential for division, so we hit a wall at n = 8.
-/

/-- The four fundamental division algebras over ℝ -/
inductive DivisionAlgebra : Type
  | reals : DivisionAlgebra      -- ℝ, dimension 1
  | complex : DivisionAlgebra    -- ℂ, dimension 2
  | quaternions : DivisionAlgebra -- ℍ, dimension 4
  | octonions : DivisionAlgebra  -- 𝕆, dimension 8

/-- Dimension of each division algebra -/
def DivisionAlgebra.dimension : DivisionAlgebra → ℕ
  | .reals => 1
  | .complex => 2
  | .quaternions => 4
  | .octonions => 8

/-- Each division algebra admits an n-square identity -/
theorem division_algebra_identity (A : DivisionAlgebra) :
    A.dimension ∈ admissibleDimensions := by
  cases A <;> simp [DivisionAlgebra.dimension, admissibleDimensions]

-- ============================================================
-- PART 10: Physical and Mathematical Significance
-- ============================================================

/-
  ## Why This Matters

  1. **Fundamental Constraint:**
     Mathematics itself "knows" that only these four dimensions work.
     This is not a human convention but a deep structural fact.

  2. **Physics Connections:**
     - ℝ: Classical mechanics, real-valued observables
     - ℂ: Quantum mechanics, wave functions
     - ℍ: 3D rotations (unit quaternions ≅ SU(2))
     - 𝕆: String theory, exceptional Lie groups

  3. **Historical Lesson:**
     Hamilton's 15-year search for "triplets" was doomed from the start.
     The universe of mathematics has only four slots for normed division
     algebras, and three dimensions doesn't fit.

  4. **Cayley-Dickson Construction:**
     Each algebra is built from the previous by "doubling":
     ℝ → ℂ → ℍ → 𝕆 → (sedenions) → ...
     But sedenions (16-dim) have zero divisors, breaking division.

  5. **Connection to Topology:**
     The existence of n-square identities is equivalent to the
     parallelizability of the (n-1)-sphere. Only S⁰, S¹, S³, S⁷
     are parallelizable (corresponding to n = 1, 2, 4, 8).
-/

end HurwitzTheorem

-- ============================================================
-- Final verification
-- ============================================================

#check HurwitzTheorem.oneSquareIdentity
#check HurwitzTheorem.twoSquareIdentity
#check HurwitzTheorem.fourSquareIdentity
#check HurwitzTheorem.no_three_square_identity
#check HurwitzTheorem.hurwitz_theorem
