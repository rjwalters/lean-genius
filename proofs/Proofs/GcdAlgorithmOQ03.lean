/-
  Lehmer's GCD variant — the unimodular-invariance core.

  Lehmer's algorithm accelerates the Euclidean GCD of two *multi-precision*
  integers `u, v` by computing a batch of partial quotients from only the
  *single-precision* leading words of `u` and `v`.  Those quotients are folded
  into a 2×2 integer matrix `[[a, b], [c, d]]`, which is then applied in one shot
  to the full-precision pair: `(u, v) ↦ (a·u + b·v, c·u + d·v)`.  The single
  multi-precision multiplication replaces many multi-precision divisions.

  Why is this correct even though the quotients were computed only approximately
  from the leading digits?  Because every such matrix is **unimodular**
  (`det = ±1`), and a unimodular transformation *exactly preserves the GCD*.
  The approximate quotients can only affect how fast the algorithm converges —
  never the value it computes.  That safety property is the content of this file.

  Main results
  ------------
  * `gcd_unimodular`      — `det = ±1` ⇒ `gcd (a·u+b·v) (c·u+d·v) = gcd u v`.
  * `det_mul`             — determinants multiply (Cauchy–Binet, 2×2): a product
                            of unimodular matrices is unimodular, so *batching*
                            many Euclidean steps stays GCD-preserving.
  * `gcd_euclid_step`     — one Euclidean step is the unimodular case `det = -1`.
  * `applyQuotients_gcd`  — applying *any* list of partial quotients as Euclidean
                            steps preserves the true GCD (the Lehmer safety net).

  This is the mathematical kernel that justifies the single-precision/
  multi-precision split in Lehmer's algorithm.  Verified, 0 axioms, 0 sorries.
-/
import Mathlib

namespace GcdAlgorithmOQ03

/-! ## Part I. Unimodular invariance (the headline) -/

/-- The GCD of `u` and `v` divides every integer combination `a·u + b·v`.
    This direction needs no determinant hypothesis. -/
theorem gcd_dvd_comb (a b u v : ℤ) :
    (↑(Int.gcd u v) : ℤ) ∣ (a * u + b * v) :=
  dvd_add (dvd_mul_of_dvd_right (Int.gcd_dvd_left _ _) a) (dvd_mul_of_dvd_right (Int.gcd_dvd_right _ _) b)

/-- **Unimodular invariance, `det = 1`.**  If `a·d - b·c = 1` then the linear
    map `(u, v) ↦ (a·u + b·v, c·u + d·v)` preserves the GCD exactly. -/
theorem gcd_unimodular_one {a b c d u v : ℤ} (h : a * d - b * c = 1) :
    Int.gcd (a * u + b * v) (c * u + d * v) = Int.gcd u v := by
  apply Nat.dvd_antisymm
  · -- gcd of the image divides gcd of the source, using the inverse matrix
    apply Int.dvd_gcd
    · -- u = d·(a·u+b·v) - b·(c·u+d·v)
      have hu : d * (a * u + b * v) - b * (c * u + d * v) = u := by
        linear_combination u * h
      have key : (↑(Int.gcd (a * u + b * v) (c * u + d * v)) : ℤ)
          ∣ (d * (a * u + b * v) - b * (c * u + d * v)) :=
        dvd_sub (dvd_mul_of_dvd_right (Int.gcd_dvd_left _ _) d)
          (dvd_mul_of_dvd_right (Int.gcd_dvd_right _ _) b)
      rwa [hu] at key
    · -- v = (-c)·(a·u+b·v) + a·(c·u+d·v)
      have hv : (-c) * (a * u + b * v) + a * (c * u + d * v) = v := by
        linear_combination v * h
      have key : (↑(Int.gcd (a * u + b * v) (c * u + d * v)) : ℤ)
          ∣ ((-c) * (a * u + b * v) + a * (c * u + d * v)) :=
        dvd_add (dvd_mul_of_dvd_right (Int.gcd_dvd_left _ _) (-c))
          (dvd_mul_of_dvd_right (Int.gcd_dvd_right _ _) a)
      rwa [hv] at key
  · -- gcd of the source divides gcd of the image (always true)
    exact Int.dvd_gcd (gcd_dvd_comb a b u v) (gcd_dvd_comb c d u v)

/-- **Unimodular invariance, `det = -1`.** -/
theorem gcd_unimodular_neg_one {a b c d u v : ℤ} (h : a * d - b * c = -1) :
    Int.gcd (a * u + b * v) (c * u + d * v) = Int.gcd u v := by
  apply Nat.dvd_antisymm
  · apply Int.dvd_gcd
    · -- u = (-d)·(a·u+b·v) + b·(c·u+d·v)
      have hu : (-d) * (a * u + b * v) + b * (c * u + d * v) = u := by
        linear_combination (-u) * h
      have key : (↑(Int.gcd (a * u + b * v) (c * u + d * v)) : ℤ)
          ∣ ((-d) * (a * u + b * v) + b * (c * u + d * v)) :=
        dvd_add (dvd_mul_of_dvd_right (Int.gcd_dvd_left _ _) (-d))
          (dvd_mul_of_dvd_right (Int.gcd_dvd_right _ _) b)
      rwa [hu] at key
    · -- v = c·(a·u+b·v) + (-a)·(c·u+d·v)
      have hv : c * (a * u + b * v) + (-a) * (c * u + d * v) = v := by
        linear_combination (-v) * h
      have key : (↑(Int.gcd (a * u + b * v) (c * u + d * v)) : ℤ)
          ∣ (c * (a * u + b * v) + (-a) * (c * u + d * v)) :=
        dvd_add (dvd_mul_of_dvd_right (Int.gcd_dvd_left _ _) c)
          (dvd_mul_of_dvd_right (Int.gcd_dvd_right _ _) (-a))
      rwa [hv] at key
  · exact Int.dvd_gcd (gcd_dvd_comb a b u v) (gcd_dvd_comb c d u v)

/-- **Unimodular invariance (general).**  Any integer matrix with determinant
    `±1` preserves the GCD.  This is *the* correctness invariant of Lehmer's
    multi-precision step: the matrix assembled from the single-precision partial
    quotients is unimodular, so applying it to the full inputs cannot change
    their GCD. -/
theorem gcd_unimodular {a b c d u v : ℤ} (h : a * d - b * c = 1 ∨ a * d - b * c = -1) :
    Int.gcd (a * u + b * v) (c * u + d * v) = Int.gcd u v := by
  rcases h with h | h
  · exact gcd_unimodular_one h
  · exact gcd_unimodular_neg_one h

/-! ## Part II. Determinants multiply — batching stays unimodular -/

/-- **Cauchy–Binet for 2×2 matrices.**  The determinant of a product is the
    product of the determinants.  Consequently a *product* of unimodular matrices
    is unimodular, which is exactly what lets Lehmer fold many Euclidean steps
    into one matrix and still preserve the GCD. -/
theorem det_mul (a b c d a' b' c' d' : ℤ) :
    (a * a' + b * c') * (c * b' + d * d') - (a * b' + b * d') * (c * a' + d * c')
      = (a * d - b * c) * (a' * d' - b' * c') := by
  ring

/-- A product of two unimodular matrices is unimodular (`det = ±1`). -/
theorem det_mul_unimodular {a b c d a' b' c' d' : ℤ}
    (h : a * d - b * c = 1 ∨ a * d - b * c = -1)
    (h' : a' * d' - b' * c' = 1 ∨ a' * d' - b' * c' = -1) :
    (a * a' + b * c') * (c * b' + d * d') - (a * b' + b * d') * (c * a' + d * c') = 1
      ∨ (a * a' + b * c') * (c * b' + d * d') - (a * b' + b * d') * (c * a' + d * c') = -1 := by
  rw [det_mul]
  rcases h with h | h <;> rcases h' with h' | h' <;> rw [h, h'] <;> simp

/-! ## Part III. One Euclidean step as the unimodular case `det = -1` -/

/-- A single Euclidean step `(u, v) ↦ (v, u - q·v)` is the unimodular matrix
    `[[0, 1], [1, -q]]` (determinant `-1`), hence preserves the GCD. -/
theorem gcd_euclid_step (u v q : ℤ) :
    Int.gcd v (u - q * v) = Int.gcd u v := by
  have h : (0 : ℤ) * (-q) - 1 * 1 = -1 := by ring
  have := gcd_unimodular_neg_one (a := 0) (b := 1) (c := 1) (d := -q) (u := u) (v := v) h
  simpa using this

/-- Swapping the arguments is the unimodular matrix `[[0,1],[1,0]]`
    (determinant `-1`); recovers `Int.gcd_comm`. -/
theorem gcd_swap (u v : ℤ) : Int.gcd v u = Int.gcd u v := by
  have h : (0 : ℤ) * 0 - 1 * 1 = -1 := by ring
  have := gcd_unimodular_neg_one (a := 0) (b := 1) (c := 1) (d := 0) (u := u) (v := v) h
  simpa using this

/-! ## Part IV. The Lehmer safety net: folding a list of partial quotients -/

/-- Apply a list of partial quotients as successive Euclidean steps.  In Lehmer's
    algorithm the quotients in this list are produced from the single-precision
    leading words of `u` and `v`; here we simply fold them over the *exact*
    multi-precision pair. -/
def applyQuotients : List ℤ → ℤ × ℤ → ℤ × ℤ
  | [], p => p
  | q :: qs, (u, v) => applyQuotients qs (v, u - q * v)

@[simp] theorem applyQuotients_nil (p : ℤ × ℤ) : applyQuotients [] p = p := rfl

@[simp] theorem applyQuotients_cons (q : ℤ) (qs : List ℤ) (u v : ℤ) :
    applyQuotients (q :: qs) (u, v) = applyQuotients qs (v, u - q * v) := rfl

/-- **Lehmer safety property.**  Folding *any* list of partial quotients as
    Euclidean steps preserves the true GCD of the inputs.  The quotients only
    govern efficiency (how quickly the pair shrinks); correctness is independent
    of how — or how approximately — they were computed.  This is precisely why
    Lehmer may derive them from single-precision leading words and still get the
    exact multi-precision GCD. -/
theorem applyQuotients_gcd (qs : List ℤ) (u v : ℤ) :
    Int.gcd (applyQuotients qs (u, v)).1 (applyQuotients qs (u, v)).2
      = Int.gcd u v := by
  induction qs generalizing u v with
  | nil => simp
  | cons q qs ih =>
      rw [applyQuotients_cons]
      rw [ih v (u - q * v)]
      exact gcd_euclid_step u v q

/-! ## Part V. Worked example -/

/-- A concrete Lehmer-style batched step.  Two Euclidean steps with quotients
    `2` then `3` fold into the unimodular matrix `[[1, -3], [-2, 7]]`
    (`det = 1·7 - (-3)·(-2) = 1`).  Applying it to `(1071, 462)` preserves the
    GCD, which is `21`. -/
example : Int.gcd (1 * 1071 + (-3) * 462) ((-2) * 1071 + 7 * 462) = Int.gcd 1071 462 :=
  gcd_unimodular_one (by ring)

example : Int.gcd 1071 462 = 21 := by decide

/-- The batched matrix really is unimodular. -/
example : (1 : ℤ) * 7 - (-3) * (-2) = 1 := by ring

end GcdAlgorithmOQ03
