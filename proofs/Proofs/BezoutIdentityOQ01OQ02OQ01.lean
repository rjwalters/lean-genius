/-
  The extended Euclidean algorithm as an explicit product of elementary step matrices
  Open Question: bezout-identity-oq-01-oq-02-oq-01

  The grandparent entry (bezout-identity-oq-01-oq-02) packages the extended Euclidean algorithm
  as a single closed-form unimodular matrix

        U(a,b) = ⎡  gcdA a b   gcdB a b ⎤
                 ⎣  -b/g        a/g     ⎦,   g = gcd a b,

  proving `U ·ᵥ (a, b) = (g, 0)` and `det U = 1` in the coprime case.  Its open question asks to
  *realize `U` as the explicit product of elementary step matrices*

        E(q) = ⎡ 0   1 ⎤
               ⎣ 1  -q ⎦

  *indexed by the Euclidean quotients qᵢ, connecting the closed-form matrix to the per-step
  recursion of the algorithm.*

  This entry answers that question.  A single Euclidean division step `a = q·b + r` (with
  `q = ⌊a/b⌋`, `r = a % b`) acts on the pair `(a, b)` as the linear map `E(q)`:

        E(q) ·ᵥ (a, b) = (b, a - q·b) = (b, a % b).

  Chaining these steps along the algorithm — `(a, b) ↦ (b, a % b) ↦ …` until the second coordinate
  hits `0` — yields, by construction, the product matrix

        euclidProd a b = E(q_k) · E(q_{k-1}) · ⋯ · E(q_1),

  where `q_1, …, q_k` are the successive quotients.  We prove:

    * **Reduction.**  `euclidProd a b ·ᵥ (a, b) = (gcd a b, 0)` for all `a, b : ℕ`
      (`euclidProd_mulVec`).  The net effect of the whole product is the same collapse to
      `(gcd, 0)` achieved by the closed-form `U`.

    * **Unimodularity.**  `det (euclidProd a b)` is a unit of `ℤ` (`euclidProd_det`): each factor
      `E(q)` has determinant `-1`, so the product has determinant `±1` and the reduction is an
      invertible integral change of basis — exactly the structural content of "the extended
      Euclidean algorithm is a product of elementary unimodular matrices."

    * **Explicit indexing by the quotients.**  `euclidProd a b = stepProduct (euclidQuots a b)`
      (`euclidProd_eq_stepProduct`), where `euclidQuots a b = [q_1, …, q_k]` is the list of
      Euclidean quotients and `stepProduct` folds them into `E(q_k) · ⋯ · E(q_1)`.  This is the
      literal "product of elementary step matrices indexed by qᵢ" requested.

  Specializing to a coprime pair recovers `euclidProd a b ·ᵥ (a, b) = (1, 0)`, the per-step
  realization of the closed-form coprime statement in the grandparent entry.

  Everything is derived from Mathlib's `Nat.gcd` machinery; no new axioms are introduced.

  References:
  - Bézout, "Théorie générale des équations algébriques" (1779).
  - Mathlib.Data.Nat.GCD.Basic (`Nat.gcd_rec`, `Nat.mod_add_div`).
  - Mathlib.LinearAlgebra.Matrix.Determinant (`Matrix.det_fin_two_of`, `Matrix.det_mul`).
  - Grandparent: BezoutIdentityOQ01OQ02.lean (closed-form unimodular matrix `U`).
-/

import Mathlib

namespace BezoutIdentityOQ01OQ02OQ01

open Matrix

/-- The elementary Euclidean **step matrix** for quotient `q`.  Acting on a column `(a, b)` it
performs one division step, sending `(a, b) ↦ (b, a - q·b)`. -/
def E (q : ℤ) : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, -q]

/-- The action of the step matrix on a length-2 vector: one Euclidean division step. -/
theorem E_mulVec (q a b : ℤ) : E q *ᵥ ![a, b] = ![b, a - q * b] := by
  funext i
  fin_cases i <;>
    simp [E, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons] <;> ring

/-- Each step matrix has determinant `-1`, hence lies in `GL₂(ℤ)`. -/
theorem E_det (q : ℤ) : (E q).det = -1 := by
  rw [E, Matrix.det_fin_two_of]; ring

/-- The product of Euclidean step matrices for the pair `(a, b)`, assembled along the recursion
`(a, b) ↦ (b, a % b)` of the Euclidean algorithm.  Terminates when the second coordinate is `0`
(returning the identity).  By construction `euclidProd a b = E(q_k)·⋯·E(q_1)`, the quotients
appearing right-to-left. -/
def euclidProd (a b : ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  if h : b = 0 then 1
  else euclidProd b (a % b) * E ((a / b : ℕ) : ℤ)
termination_by b
decreasing_by simp_wf; exact Nat.mod_lt a (Nat.pos_of_ne_zero h)

@[simp] theorem euclidProd_zero (a : ℕ) : euclidProd a 0 = 1 := by
  rw [euclidProd]; simp

theorem euclidProd_pos {a b : ℕ} (h : b ≠ 0) :
    euclidProd a b = euclidProd b (a % b) * E ((a / b : ℕ) : ℤ) := by
  rw [euclidProd]; simp [h]

/-- **Reduction.**  The full product of step matrices carries `(a, b)` to `(gcd a b, 0)`: the
per-step Euclidean algorithm, realized as a single matrix product, has the same net effect as the
closed-form reduction matrix `U` of the grandparent entry. -/
theorem euclidProd_mulVec (a b : ℕ) :
    euclidProd a b *ᵥ ![(a : ℤ), (b : ℤ)] = ![(Nat.gcd a b : ℤ), 0] := by
  induction a, b using euclidProd.induct with
  | case1 a =>
      simp [Nat.gcd_zero_right]
  | case2 a b hb ih =>
      rw [euclidProd_pos hb, ← Matrix.mulVec_mulVec, E_mulVec]
      have hmod : (a : ℤ) - ((a / b : ℕ) : ℤ) * (b : ℤ) = ((a % b : ℕ) : ℤ) := by
        have h : ((a % b : ℕ) : ℤ) + (b : ℤ) * ((a / b : ℕ) : ℤ) = (a : ℤ) := by
          exact_mod_cast Nat.mod_add_div a b
        linarith
      rw [hmod, ih]
      have hg : Nat.gcd a b = Nat.gcd b (a % b) := by
        conv_lhs => rw [Nat.gcd_comm]
        rw [Nat.gcd_rec, Nat.gcd_comm]
      rw [hg]

/-- **Unimodularity.**  `det (euclidProd a b)` is a unit of `ℤ` (in fact `±1`), so the product of
step matrices is an invertible integral change of basis. -/
theorem euclidProd_det (a b : ℕ) : IsUnit (euclidProd a b).det := by
  induction a, b using euclidProd.induct with
  | case1 a =>
      simp
  | case2 a b hb ih =>
      rw [euclidProd_pos hb, Matrix.det_mul, E_det]
      exact ih.mul (isUnit_one.neg)

/-- **Coprime specialization.**  When `a, b` are coprime the product carries `(a, b)` to the
standard basis vector `(1, 0)` — the per-step realization of the grandparent's coprime statement. -/
theorem euclidProd_mulVec_coprime (a b : ℕ) (h : Nat.Coprime a b) :
    euclidProd a b *ᵥ ![(a : ℤ), (b : ℤ)] = ![1, 0] := by
  rw [euclidProd_mulVec, show Nat.gcd a b = 1 from h]; norm_num

/-!
### Explicit indexing by the Euclidean quotients

We expose the list of quotients `q₁, …, q_k` and fold them into the product of step matrices,
making the phrase "product of elementary step matrices indexed by qᵢ" literal.
-/

/-- The list of Euclidean quotients `qᵢ = ⌊aᵢ / bᵢ⌋` produced along the algorithm, in order. -/
def euclidQuots (a b : ℕ) : List ℤ :=
  if h : b = 0 then []
  else ((a / b : ℕ) : ℤ) :: euclidQuots b (a % b)
termination_by b
decreasing_by simp_wf; exact Nat.mod_lt a (Nat.pos_of_ne_zero h)

@[simp] theorem euclidQuots_zero (a : ℕ) : euclidQuots a 0 = [] := by
  rw [euclidQuots]; simp

theorem euclidQuots_pos {a b : ℕ} (h : b ≠ 0) :
    euclidQuots a b = ((a / b : ℕ) : ℤ) :: euclidQuots b (a % b) := by
  rw [euclidQuots]; simp [h]

/-- Fold a list of quotients into the corresponding product of step matrices:
`stepProduct [q₁, …, q_k] = E q_k · ⋯ · E q₁`. -/
def stepProduct (qs : List ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  qs.foldr (fun q acc => acc * E q) 1

@[simp] theorem stepProduct_nil : stepProduct [] = 1 := rfl

@[simp] theorem stepProduct_cons (q : ℤ) (qs : List ℤ) :
    stepProduct (q :: qs) = stepProduct qs * E q := rfl

/-- **Explicit product.**  `euclidProd a b` is exactly the product of the step matrices indexed by
the Euclidean quotients: `euclidProd a b = E(q_k) · ⋯ · E(q_1)`. -/
theorem euclidProd_eq_stepProduct (a b : ℕ) :
    euclidProd a b = stepProduct (euclidQuots a b) := by
  induction a, b using euclidProd.induct with
  | case1 a =>
      simp
  | case2 a b hb ih =>
      rw [euclidProd_pos hb, ih, euclidQuots_pos hb, stepProduct_cons]

/-- Sanity check: `(12, 8)` reduces to `(gcd = 4, 0)`. -/
example : euclidProd 12 8 *ᵥ ![(12 : ℤ), 8] = ![4, 0] := by
  simpa using euclidProd_mulVec 12 8

/-- Sanity check: the coprime pair `(7, 5)` is carried to `(1, 0)`. -/
example : euclidProd 7 5 *ᵥ ![(7 : ℤ), 5] = ![1, 0] := by
  simpa using euclidProd_mulVec 7 5

/-- Sanity check: the quotient list for `(12, 8)` is `[1, 2]` (12 = 1·8 + 4, 8 = 2·4 + 0),
so `euclidProd 12 8 = E 2 · E 1`. -/
example : euclidQuots 12 8 = [(1 : ℤ), 2] := by
  rw [euclidQuots_pos (by norm_num : (8 : ℕ) ≠ 0),
      euclidQuots_pos (by norm_num : (12 % 8 : ℕ) ≠ 0)]
  norm_num

end BezoutIdentityOQ01OQ02OQ01
