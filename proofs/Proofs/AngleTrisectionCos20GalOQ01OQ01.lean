/-
  Unifying cos(20°) and cos(π/7): Irreducibility via Eisenstein-Shift Pattern
  (angle-trisection-cos-20-gal-oq-01-oq-01)

  Question: Can the irreducibility proofs for:
    - 8X³-6X-1 (minimal polynomial of cos(20°) = cos(π/9))
    - 8X³-4X²-4X+1 (minimal polynomial of cos(π/7))
  be unified into a single theorem parameterized by the Eisenstein prime?

  Answer: Yes. The key abstract lemma is:
    If q ∈ K[X] is irreducible and ℓ = aX+b (a≠0) is an invertible linear polynomial
    over an infinite field K, then q.comp(ℓ) is also irreducible.

  Both cases use the same linear substitution ℓ = 2X+2:
  - cos(20°): q₃ = X³-6X²+9X-3 (Eisenstein at 3) → q₃.comp(2X+2) = 8X³-6X-1
  - cos(π/7): r₇ = X³-7X²+14X-7 (Eisenstein at 7) → r₇.comp(2X+2) = 8X³-4X²-4X+1

  The "Eisenstein prime" is the parameter p in the Eisenstein criterion:
  - p=3 for q₃ (cos(20°) case)
  - p=7 for r₇ (cos(π/7) case)
  The same abstract linear-shift machinery applies in both cases.

  References:
  - AngleTrisectionCos20Gal.lean: Galois group proof for cos(20°)
  - AngleTrisectionCos20GalOQ01.lean: Galois group proof for cos(π/7)
-/
import Mathlib

set_option maxHeartbeats 800000

open Polynomial IntermediateField FiniteDimensional

namespace AngleTrisectionEisensteinUnification

-- ============================================================
-- PART I: Abstract Lemma — Irreducibility Under Linear Shift
-- ============================================================

/-- **Key Abstract Lemma**: Irreducibility is preserved under invertible linear substitution.
    For an infinite field K: if q ∈ K[X] is irreducible and a ≠ 0,
    then q.comp(aX+b) is also irreducible.

    Proof: The composition map p ↦ p.comp(aX+b) has inverse p ↦ p.comp(a⁻¹X - a⁻¹b).
    Any nontrivial factorization of q.comp(ℓ) pulls back to a nontrivial factorization
    of q via the inverse, contradicting irreducibility. -/
theorem irreducible_of_comp_linear {K : Type*} [Field K] [Infinite K]
    (q : K[X]) (a b : K) (ha : a ≠ 0) (hq : Irreducible q) :
    Irreducible (q.comp (C a * X + C b)) := by
  set ℓ := C a * X + C b with hℓ_def
  set ℓ_inv := C a⁻¹ * X + C (-a⁻¹ * b) with hℓ_inv_def
  -- ℓ ∘ ℓ_inv = X  (proven via evaluation at every point, valid over infinite fields)
  have hℓ_ℓ_inv : ℓ.comp ℓ_inv = X := Polynomial.funext fun x => by
    simp only [ℓ, ℓ_inv, eval_comp, eval_add, eval_mul, eval_C, eval_X]; field_simp
  -- ℓ_inv ∘ ℓ = X
  have hℓ_inv_ℓ : ℓ_inv.comp ℓ = X := Polynomial.funext fun x => by
    simp only [ℓ, ℓ_inv, eval_comp, eval_add, eval_mul, eval_C, eval_X]; field_simp
  rw [irreducible_iff]
  refine ⟨?_, ?_⟩
  · -- Not a unit: if q.comp ℓ = C c, then q = C c, contradicting irreducibility.
    intro h
    obtain ⟨c, hc_ne, hc_eq⟩ := Polynomial.isUnit_iff.mp h
    exact hq.not_unit <| Polynomial.isUnit_iff.mpr ⟨c, hc_ne, by
      calc q = q.comp X := q.comp_X.symm
        _ = q.comp (ℓ.comp ℓ_inv) := by rw [hℓ_ℓ_inv]
        _ = (q.comp ℓ).comp ℓ_inv := (q.comp_assoc ℓ ℓ_inv).symm
        _ = (C c).comp ℓ_inv := by rw [hc_eq]
        _ = C c := C_comp⟩
  · -- Factorizations of q.comp ℓ pull back to factorizations of q.
    intro s t hst
    have hq_factor : q = s.comp ℓ_inv * t.comp ℓ_inv :=
      calc q = q.comp X := q.comp_X.symm
        _ = q.comp (ℓ.comp ℓ_inv) := by rw [hℓ_ℓ_inv]
        _ = (q.comp ℓ).comp ℓ_inv := (q.comp_assoc ℓ ℓ_inv).symm
        _ = (s * t).comp ℓ_inv := by rw [hst]
        _ = s.comp ℓ_inv * t.comp ℓ_inv := mul_comp s t ℓ_inv
    rcases hq.isUnit_or_isUnit hq_factor with hs | ht
    · left
      obtain ⟨c, hc_ne, hc_eq⟩ := Polynomial.isUnit_iff.mp hs
      exact Polynomial.isUnit_iff.mpr ⟨c, hc_ne, by
        calc s = s.comp X := s.comp_X.symm
          _ = s.comp (ℓ_inv.comp ℓ) := by rw [hℓ_inv_ℓ]
          _ = (s.comp ℓ_inv).comp ℓ := (s.comp_assoc ℓ_inv ℓ).symm
          _ = (C c).comp ℓ := by rw [hc_eq]
          _ = C c := C_comp⟩
    · right
      obtain ⟨c, hc_ne, hc_eq⟩ := Polynomial.isUnit_iff.mp ht
      exact Polynomial.isUnit_iff.mpr ⟨c, hc_ne, by
        calc t = t.comp X := t.comp_X.symm
          _ = t.comp (ℓ_inv.comp ℓ) := by rw [hℓ_inv_ℓ]
          _ = (t.comp ℓ_inv).comp ℓ := (t.comp_assoc ℓ_inv ℓ).symm
          _ = (C c).comp ℓ := by rw [hc_eq]
          _ = C c := C_comp⟩

-- ============================================================
-- PART II: Application to cos(20°) — Eisenstein at 3
-- ============================================================

-- The Eisenstein polynomial q₃ = X³-6X²+9X-3 over ℤ
private noncomputable def q3_int : ℤ[X] := X ^ 3 - C 6 * X ^ 2 + C 9 * X - C 3

private theorem q3_int_natDegree : q3_int.natDegree = 3 := by
  unfold q3_int; compute_degree!

private theorem q3_int_degree : q3_int.degree = 3 := by
  unfold q3_int; compute_degree!

private theorem q3_int_monic : q3_int.Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, q3_int_natDegree]
  unfold q3_int
  simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

/-- q₃ is irreducible over ℤ by the Eisenstein criterion at p=3. -/
private theorem q3_int_irreducible : Irreducible q3_int := by
  apply Polynomial.irreducible_of_eisenstein_criterion (P := Ideal.span {(3 : ℤ)})
  · rw [Ideal.span_singleton_prime (show (3 : ℤ) ≠ 0 from by norm_num)]
    exact Int.prime_iff_natAbs_prime.mpr (by norm_num)
  · rw [q3_int_monic.leadingCoeff, Ideal.mem_span_singleton]; norm_num
  · intro k hk
    rw [q3_int_degree] at hk
    simp only [Ideal.mem_span_singleton]
    unfold q3_int
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    interval_cases k <;> norm_num
  · rw [q3_int_degree]; exact_mod_cast Nat.zero_lt_succ 2
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    unfold q3_int
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    norm_num
  · exact q3_int_monic.isPrimitive

-- q₃ over ℚ
private noncomputable def q3 : ℚ[X] := X ^ 3 - C 6 * X ^ 2 + C 9 * X - C 3

private theorem q3_eq_map : q3 = Polynomial.map (Int.castRingHom ℚ) q3_int := by
  unfold q3 q3_int
  simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]; norm_num

/-- q₃ is irreducible over ℚ (Gauss's lemma: monic + ℤ-irreducible → ℚ-irreducible). -/
private theorem q3_irreducible : Irreducible q3 := by
  rw [q3_eq_map]
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    q3_int_monic.isPrimitive).mp q3_int_irreducible

/-- The minimal polynomial of cos(20°): p_cos20 = 8X³-6X-1 = q₃(2X+2). -/
noncomputable def p_cos20 : ℚ[X] := C 8 * X ^ 3 - C 6 * X - C 1

/-- Composition identity: q₃(2X+2) = p_cos20 (verified by ring computation). -/
private theorem q3_comp_eq_p_cos20 : q3.comp (C 2 * X + C 2) = p_cos20 :=
  Polynomial.funext fun x => by
    simp only [eval_comp, eval_add, eval_mul, eval_C, eval_X, eval_pow,
      eval_sub, eval_ofNat]
    unfold q3 p_cos20
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    ring

/-- **cos(20°) case**: 8X³-6X-1 is irreducible over ℚ.
    The Eisenstein prime is p=3; the linear shift is ℓ = 2X+2. -/
theorem p_cos20_irreducible : Irreducible (p_cos20 : ℚ[X]) := by
  rw [← q3_comp_eq_p_cos20]
  exact irreducible_of_comp_linear q3 2 2 (by norm_num) q3_irreducible

-- ============================================================
-- PART III: Application to cos(π/7) — Eisenstein at 7
-- ============================================================

-- The Eisenstein polynomial r₇ = X³-7X²+14X-7 over ℤ
private noncomputable def r7_int : ℤ[X] := X ^ 3 - C 7 * X ^ 2 + C 14 * X - C 7

private theorem r7_int_natDegree : r7_int.natDegree = 3 := by
  unfold r7_int; compute_degree!

private theorem r7_int_degree : r7_int.degree = 3 := by
  unfold r7_int; compute_degree!

private theorem r7_int_monic : r7_int.Monic := by
  rw [Polynomial.Monic, Polynomial.leadingCoeff, r7_int_natDegree]
  unfold r7_int
  simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
  norm_num

/-- r₇ is irreducible over ℤ by the Eisenstein criterion at p=7. -/
private theorem r7_int_irreducible : Irreducible r7_int := by
  apply Polynomial.irreducible_of_eisenstein_criterion (P := Ideal.span {(7 : ℤ)})
  · rw [Ideal.span_singleton_prime (show (7 : ℤ) ≠ 0 from by norm_num)]
    exact Int.prime_iff_natAbs_prime.mpr (by norm_num)
  · rw [r7_int_monic.leadingCoeff, Ideal.mem_span_singleton]; norm_num
  · intro k hk
    rw [r7_int_degree] at hk
    simp only [Ideal.mem_span_singleton]
    unfold r7_int
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    interval_cases k <;> norm_num
  · rw [r7_int_degree]; exact_mod_cast Nat.zero_lt_succ 2
  · rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    unfold r7_int
    simp only [coeff_sub, coeff_add, coeff_C_mul, coeff_X_pow, coeff_C, coeff_X]
    norm_num
  · exact r7_int_monic.isPrimitive

-- r₇ over ℚ
private noncomputable def r7 : ℚ[X] := X ^ 3 - C 7 * X ^ 2 + C 14 * X - C 7

private theorem r7_eq_map : r7 = Polynomial.map (Int.castRingHom ℚ) r7_int := by
  unfold r7 r7_int
  simp [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X]; norm_num

/-- r₇ is irreducible over ℚ (Gauss's lemma). -/
private theorem r7_irreducible : Irreducible r7 := by
  rw [r7_eq_map]
  exact (IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    r7_int_monic.isPrimitive).mp r7_int_irreducible

/-- The minimal polynomial of cos(π/7): p_cos_pi7 = 8X³-4X²-4X+1 = r₇(2X+2). -/
noncomputable def p_cos_pi7 : ℚ[X] := C 8 * X ^ 3 - C 4 * X ^ 2 - C 4 * X + C 1

/-- Composition identity: r₇(2X+2) = p_cos_pi7. -/
private theorem r7_comp_eq_p_cos_pi7 : r7.comp (C 2 * X + C 2) = p_cos_pi7 :=
  Polynomial.funext fun x => by
    simp only [eval_comp, eval_add, eval_mul, eval_C, eval_X, eval_pow,
      eval_sub, eval_ofNat]
    unfold r7 p_cos_pi7
    simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    ring

/-- **cos(π/7) case**: 8X³-4X²-4X+1 is irreducible over ℚ.
    The Eisenstein prime is p=7; the linear shift is ℓ = 2X+2. -/
theorem p_cos_pi7_irreducible : Irreducible (p_cos_pi7 : ℚ[X]) := by
  rw [← r7_comp_eq_p_cos_pi7]
  exact irreducible_of_comp_linear r7 2 2 (by norm_num) r7_irreducible

-- ============================================================
-- PART IV: Unified Summary Theorems
-- ============================================================

/-- **Unification**: Both cos(20°) and cos(π/7) minimal polynomials are irreducible.
    The proof structure is identical in both cases:
      (1) Apply Eisenstein at the appropriate prime p to get q_p irreducible over ℤ
      (2) Gauss's lemma gives q_p irreducible over ℚ
      (3) Apply `irreducible_of_comp_linear` with the same shift ℓ = 2X+2 -/
theorem eisenstein_shift_unification :
    Irreducible (p_cos20 : ℚ[X]) ∧ Irreducible (p_cos_pi7 : ℚ[X]) :=
  ⟨p_cos20_irreducible, p_cos_pi7_irreducible⟩

/-- The Eisenstein-shift pattern: both cases use the same linear shift 2X+2,
    differing only in the Eisenstein prime (p=3 vs p=7). -/
theorem same_shift_different_prime :
    (q3.comp (C 2 * X + C 2) = p_cos20) ∧
    (r7.comp (C 2 * X + C 2) = p_cos_pi7) :=
  ⟨q3_comp_eq_p_cos20, r7_comp_eq_p_cos_pi7⟩

/-- Galois group bound: 3 divides |Gal(p_cos20/ℚ)|.
    Irreducible prime-degree polynomial → Galois group contains a p-cycle. -/
theorem cos20_gal_three_dvd_card :
    3 ∣ Fintype.card p_cos20.Gal :=
  Polynomial.Gal.prime_degree_dvd_card p_cos20_irreducible

/-- Galois group bound: 3 divides |Gal(p_cos_pi7/ℚ)|. -/
theorem cos_pi7_gal_three_dvd_card :
    3 ∣ Fintype.card p_cos_pi7.Gal :=
  Polynomial.Gal.prime_degree_dvd_card p_cos_pi7_irreducible

end AngleTrisectionEisensteinUnification
