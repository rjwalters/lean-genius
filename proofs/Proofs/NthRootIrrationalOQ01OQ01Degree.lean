/-
  Nth Root Irrationality OQ-01-OQ-01 (exact degree of the real subfield).

  The sibling files in this family proved:
  - `NthRootIrrationalOQ01OQ01Real.lean`: `φ(n) ≥ 3 ⟹ ζ + ζ⁻¹ ∉ ℚ` (the real
    cyclotomic generator `2·cos(2π/n)` is irrational), i.e. `[ℚ(ζ+ζ⁻¹):ℚ] > 1`.
  - `NthRootIrrationalOQ01OQ01CosRational.lean` / `...Cos.lean`: the full Niven
    classification `cos(2π/n) ∈ ℚ ⟺ n ∈ {1,2,3,4,6}`.

  Those prior sessions repeatedly flagged the **exact degree**
  `[ℚ(ζ+ζ⁻¹):ℚ] = φ(n)/2` as the sole remaining open item, deferred as needing
  "IntermediateField tower machinery". This file closes it.

  **Main result** (`finrank_adjoin_trace_eq`, division-free form):

      `3 ≤ n  ⟹  2 · [ℚ(ζ+ζ⁻¹):ℚ] = φ(n)`.

  Here `ζ : ℂ` is a primitive `n`-th root of unity and `ζ + ζ⁻¹ = 2·cos(2π/n)`
  is the generator of the maximal real subfield `ℚ(ζ)⁺` of the cyclotomic field.

  **Proof outline.**
  1. `[ℚ(ζ):ℚ] = φ(n)` — `adjoin.finrank` + `cyclotomic_eq_minpoly_rat`.
  2. The tower `ℚ ⊆ ℚ(ζ+ζ⁻¹) ⊆ ℚ(ζ)` gives, via `finrank_bot_mul_relfinrank`,
       `[ℚ(ζ+ζ⁻¹):ℚ] · [ℚ(ζ):ℚ(ζ+ζ⁻¹)] = φ(n)`.
  3. `[ℚ(ζ):ℚ(ζ+ζ⁻¹)] = 2`:
       - `≤ 2`: with `α := ζ+ζ⁻¹ ∈ ℚ(ζ+ζ⁻¹)`, `ζ` is a root of the degree-2
         polynomial `X² − α·X + 1` over `ℚ(ζ+ζ⁻¹)`, so `minpoly` has degree ≤ 2;
       - `≥ 2`: a degree-1 minimal polynomial would force `ζ ∈ ℚ(ζ+ζ⁻¹)`; but
         `ζ+ζ⁻¹` is real (`|ζ| = 1`), so `ℚ(ζ+ζ⁻¹)` is a *real* subfield, while
         `ζ` is non-real for `n ≥ 3` — contradiction.

  The relative degree is computed through `relfinrank`/`extendScalars`:
  `relfinrank ℚ(α) ℚ(ζ) = finrank ℚ(α) (extendScalars h) = finrank ℚ(α) ℚ(α)(ζ)
  = (minpoly ℚ(α) ζ).natDegree`, using `extendScalars_adjoin` to identify the
  relative extension with the simple adjoin `ℚ(α)(ζ)`.

  **Key Mathlib facts:**
  - `IntermediateField.adjoin.finrank` : `[K(x):K] = deg(minpoly K x)`.
  - `IntermediateField.finrank_bot_mul_relfinrank` : tower multiplicativity.
  - `IntermediateField.extendScalars_adjoin` : `extendScalars h = adjoin K S`.
  - `Polynomial.cyclotomic_eq_minpoly_rat`, `Polynomial.natDegree_cyclotomic`.
  - `Complex.norm_eq_one_of_pow_eq_one`, `Complex.inv_im` (real subfield).

  **Results (0 axioms, 0 sorries):**
  1. `relfinrank_adjoin_trace_eq_two` : `[ℚ(ζ):ℚ(ζ+ζ⁻¹)] = 2` for `n ≥ 3`.
  2. `finrank_adjoin_trace_eq`        : `2 · [ℚ(ζ+ζ⁻¹):ℚ] = φ(n)` for `n ≥ 3`.
  3. `fifthRoot_finrank_adjoin_trace` : concrete `n = 5`, `[ℚ(2cos(2π/5)):ℚ] = 2`.

  ## References
  - Washington, L. (1997). "Introduction to Cyclotomic Fields." §2 (real subfield).
  - Niven, I. (1956). "Irrational Numbers." Carus Math. Monographs.
-/

import Mathlib

set_option maxHeartbeats 1600000
-- The `Module (↥ℚ⟮α⟯) (↥ℚ⟮α⟯)[X]` instance over the IntermediateField subtype is
-- synthesizable but exceeds the default 20000 synthInstance budget; raise it.
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedVariables false

open Polynomial Module IntermediateField

namespace NthRootIrrationalOQ01OQ01Degree

noncomputable section

-- ============================================================================
-- The maximal real subfield: the im = 0 intermediate field of ℂ over ℚ
-- ============================================================================

/-- The real subfield `{z : ℂ | z.im = 0}` of `ℂ`, as an intermediate field over
    `ℚ`.  Every rational is real; the reals are closed under the field
    operations and inverses. -/
def realField : IntermediateField ℚ ℂ where
  carrier := {z : ℂ | z.im = 0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Complex.mul_im] at *
    rw [ha, hb]; ring
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Complex.add_im] at *
    rw [ha, hb]; ring
  zero_mem' := by simp
  algebraMap_mem' := by
    intro r
    simp only [Set.mem_setOf_eq, eq_ratCast]
    exact Complex.ratCast_im r
  inv_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq, Complex.inv_im] at *
    rw [hx]; simp

@[simp] theorem mem_realField {z : ℂ} : z ∈ realField ↔ z.im = 0 := Iff.rfl

-- ============================================================================
-- Setup lemmas about a primitive n-th root of unity
-- ============================================================================

variable {n : ℕ} {ζ : ℂ}

/-- A primitive `n`-th root of unity (for `0 < n`) is nonzero. -/
theorem primitiveRoot_ne_zero (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) : ζ ≠ 0 := by
  intro h
  have hpow : ζ ^ n = 1 := hζ.pow_eq_one
  rw [h, zero_pow hn.ne'] at hpow
  exact one_ne_zero hpow.symm

/-- A primitive `n`-th root of unity is integral over `ℚ`.  It is integral over
    `ℤ` (a root of `Xⁿ − 1`); lift along the tower `ℤ → ℚ → ℂ`. -/
theorem primitiveRoot_isIntegral (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) :
    IsIntegral ℚ ζ :=
  (hζ.isIntegral hn).tower_top

/-- The real cyclotomic generator `α = ζ + ζ⁻¹` is real, i.e. lies in `realField`.
    Indeed `α = 2·Re ζ` because `|ζ| = 1`. -/
theorem trace_mem_realField (hn : 0 < n) (hζ : IsPrimitiveRoot ζ n) :
    ζ + ζ⁻¹ ∈ realField := by
  have hnorm : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one hn.ne'
  have hns : Complex.normSq ζ = 1 := by
    rw [Complex.normSq_eq_norm_sq, hnorm]; norm_num
  simp only [mem_realField, Complex.add_im, Complex.inv_im, hns]
  ring

/-- For `n ≥ 3`, a primitive `n`-th root of unity is **not** real:
    if `ζ.im = 0` then `ζ⁻¹ = ζ`, so `ζ² = 1`, forcing `n ∣ 2`. -/
theorem primitiveRoot_not_real (hn : 3 ≤ n) (hζ : IsPrimitiveRoot ζ n) :
    ζ.im ≠ 0 := by
  have hn0 : 0 < n := by omega
  have hζ0 : ζ ≠ 0 := primitiveRoot_ne_zero hn0 hζ
  intro him
  -- `ζ.im = 0 ⟹ ζ = conj ζ`, and for a root of unity `conj ζ = ζ⁻¹`, so `ζ = ζ⁻¹`.
  have hns : Complex.normSq ζ = 1 := by
    rw [Complex.normSq_eq_norm_sq,
      Complex.norm_eq_one_of_pow_eq_one hζ.pow_eq_one hn0.ne']; norm_num
  -- `ζ⁻¹ = ζ` because `ζ⁻¹ = conj ζ / normSq = conj ζ` and `conj ζ = ζ` when `im = 0`.
  have hinv : ζ⁻¹ = ζ := by
    apply Complex.ext
    · rw [Complex.inv_re, hns]; simp
    · rw [Complex.inv_im, hns, him]; simp
  -- Hence `ζ ^ 2 = 1`.
  have hsq : ζ ^ 2 = 1 := by
    have : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hζ0
    rw [hinv] at this; rw [sq]; exact this
  -- A primitive root with `ζ ^ 2 = 1` forces `n ∣ 2`, impossible for `n ≥ 3`.
  have hdvd : n ∣ 2 := hζ.dvd_of_pow_eq_one 2 hsq
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

-- ============================================================================
-- The relative degree [ℚ(ζ) : ℚ(ζ + ζ⁻¹)] = 2
-- ============================================================================

/-- **The cyclotomic field is degree 2 over its maximal real subfield.**
    For `n ≥ 3` and `ζ` a primitive `n`-th root of unity,
    `[ℚ(ζ) : ℚ(ζ + ζ⁻¹)] = 2`. -/
theorem relfinrank_adjoin_trace_eq_two (hn : 3 ≤ n) (hζ : IsPrimitiveRoot ζ n) :
    relfinrank (ℚ⟮ζ + ζ⁻¹⟯ : IntermediateField ℚ ℂ) ℚ⟮ζ⟯ = 2 := by
  have hn0 : 0 < n := by omega
  have hζ0 : ζ ≠ 0 := primitiveRoot_ne_zero hn0 hζ
  set α : ℂ := ζ + ζ⁻¹ with hαdef
  -- `α ∈ ℚ⟮ζ⟯`, so `ℚ⟮α⟯ ≤ ℚ⟮ζ⟯`.
  have hαmem : α ∈ (ℚ⟮ζ⟯ : IntermediateField ℚ ℂ) := by
    rw [hαdef]
    exact add_mem (mem_adjoin_simple_self ℚ ζ) (inv_mem (mem_adjoin_simple_self ℚ ζ))
  have hle : (ℚ⟮α⟯ : IntermediateField ℚ ℂ) ≤ ℚ⟮ζ⟯ := adjoin_simple_le_iff.mpr hαmem
  -- `ζ` is integral over the subfield `ℚ⟮α⟯`.
  have hζintℚ : IsIntegral ℚ ζ := primitiveRoot_isIntegral hn0 hζ
  have hζint : IsIntegral (ℚ⟮α⟯ : IntermediateField ℚ ℂ) ζ := hζintℚ.tower_top
  -- `α` as an element of the subfield `ℚ⟮α⟯`.
  set αK : (ℚ⟮α⟯ : IntermediateField ℚ ℂ) := ⟨α, mem_adjoin_simple_self ℚ α⟩ with hαK
  have hαKcoe : (algebraMap (ℚ⟮α⟯ : IntermediateField ℚ ℂ) ℂ) αK = α := rfl
  -- The rational (over `ℚ⟮α⟯`) quadratic `q = X² − αK·X + 1` has `ζ` as a root.
  set q : (ℚ⟮α⟯ : IntermediateField ℚ ℂ)[X] := X ^ 2 - C αK * X + 1 with hq
  have haeval : (aeval ζ) q = 0 := by
    have hmul : ζ⁻¹ * ζ = 1 := inv_mul_cancel₀ hζ0
    rw [hq]
    simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, map_one, hαKcoe, hαdef]
    linear_combination -hmul
  have hqdeg : q.natDegree = 2 := by rw [hq]; compute_degree!
  have hqne : q ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hqdeg; omega
  -- The minimal polynomial of `ζ` over `ℚ⟮α⟯` divides `q`, so has degree ≤ 2.
  have hdvd : minpoly (ℚ⟮α⟯ : IntermediateField ℚ ℂ) ζ ∣ q :=
    minpoly.dvd (ℚ⟮α⟯ : IntermediateField ℚ ℂ) ζ haeval
  have hle2 : (minpoly (ℚ⟮α⟯ : IntermediateField ℚ ℂ) ζ).natDegree ≤ 2 := by
    rw [← hqdeg]; exact natDegree_le_of_dvd hdvd hqne
  -- The minimal polynomial has positive degree (ζ is integral).
  have hpos : 0 < (minpoly (ℚ⟮α⟯ : IntermediateField ℚ ℂ) ζ).natDegree :=
    minpoly.natDegree_pos hζint
  -- Every element of `ℚ⟮α⟯` is real, because its generator `α = ζ + ζ⁻¹` is.
  have hαreal : (ℚ⟮α⟯ : IntermediateField ℚ ℂ) ≤ realField :=
    adjoin_simple_le_iff.mpr (by rw [hαdef]; exact trace_mem_realField hn0 hζ)
  -- Degree ≠ 1: else `ζ ∈ ℚ⟮α⟯`, contradicting that `ℚ⟮α⟯` is real but `ζ` is not.
  have hne1 : (minpoly (ℚ⟮α⟯ : IntermediateField ℚ ℂ) ζ).natDegree ≠ 1 := by
    intro hdeg1
    -- `[ℚ⟮α⟯(ζ) : ℚ⟮α⟯] = 1`, so `ℚ⟮α⟯(ζ) = ⊥`, so `ζ ∈ range(algebraMap ℚ⟮α⟯ ℂ)`.
    have hfr : finrank (ℚ⟮α⟯ : IntermediateField ℚ ℂ)
        (ℚ⟮α⟯ : IntermediateField ℚ ℂ)⟮ζ⟯ = 1 := by
      rw [IntermediateField.adjoin.finrank hζint, hdeg1]
    have hbot : (ℚ⟮α⟯ : IntermediateField ℚ ℂ)⟮ζ⟯ = ⊥ :=
      IntermediateField.finrank_eq_one_iff.mp hfr
    have hζbot : ζ ∈ (⊥ : IntermediateField (ℚ⟮α⟯ : IntermediateField ℚ ℂ) ℂ) := by
      rw [← hbot]; exact mem_adjoin_simple_self _ ζ
    rw [IntermediateField.mem_bot] at hζbot
    obtain ⟨k, hk⟩ := hζbot
    -- `ζ = ↑k` with `k ∈ ℚ⟮α⟯`; but every element of `ℚ⟮α⟯` is real.
    have hkreal : (k : ℂ).im = 0 := (mem_realField).mp (hαreal k.2)
    have hcoe : (algebraMap (ℚ⟮α⟯ : IntermediateField ℚ ℂ) ℂ) k = (k : ℂ) := rfl
    rw [hcoe] at hk
    exact primitiveRoot_not_real hn hζ (hk ▸ hkreal)
  -- Combine: degree is exactly 2.
  have hdeg2 : (minpoly (ℚ⟮α⟯ : IntermediateField ℚ ℂ) ζ).natDegree = 2 := by omega
  -- Translate to the relative degree via `extendScalars`.
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle,
    IntermediateField.extendScalars_adjoin hle,
    IntermediateField.adjoin.finrank hζint, hdeg2]

-- ============================================================================
-- Main theorem: 2 · [ℚ(ζ + ζ⁻¹) : ℚ] = φ(n)
-- ============================================================================

/-- **Exact degree of the maximal real subfield.**  For `n ≥ 3` and `ζ` a
    primitive `n`-th root of unity, the real cyclotomic generator
    `ζ + ζ⁻¹ = 2·cos(2π/n)` generates a subfield of degree `φ(n)/2`:

        `2 · [ℚ(ζ + ζ⁻¹) : ℚ] = φ(n)`.

    (Stated division-free.  Since `φ(n)` is even for `n ≥ 3`, this pins the
    degree to exactly `φ(n)/2`.) -/
theorem finrank_adjoin_trace_eq (hn : 3 ≤ n) (hζ : IsPrimitiveRoot ζ n) :
    2 * finrank ℚ (ℚ⟮ζ + ζ⁻¹⟯ : IntermediateField ℚ ℂ) = n.totient := by
  have hn0 : 0 < n := by omega
  set α : ℂ := ζ + ζ⁻¹ with hαdef
  have hαmem : α ∈ (ℚ⟮ζ⟯ : IntermediateField ℚ ℂ) := by
    rw [hαdef]
    exact add_mem (mem_adjoin_simple_self ℚ ζ) (inv_mem (mem_adjoin_simple_self ℚ ζ))
  have hle : (ℚ⟮α⟯ : IntermediateField ℚ ℂ) ≤ ℚ⟮ζ⟯ := adjoin_simple_le_iff.mpr hαmem
  have hζintℚ : IsIntegral ℚ ζ := primitiveRoot_isIntegral hn0 hζ
  -- `[ℚ(ζ) : ℚ] = φ(n)`.
  have hcycdeg : finrank ℚ (ℚ⟮ζ⟯ : IntermediateField ℚ ℂ) = n.totient := by
    rw [IntermediateField.adjoin.finrank hζintℚ,
      ← cyclotomic_eq_minpoly_rat hζ hn0, natDegree_cyclotomic]
  -- Tower: `[ℚ(α):ℚ] · [ℚ(ζ):ℚ(α)] = [ℚ(ζ):ℚ]`.
  have htower := IntermediateField.finrank_bot_mul_relfinrank hle
  rw [relfinrank_adjoin_trace_eq_two hn hζ, hcycdeg] at htower
  -- `finrank ℚ ℚ⟮α⟯ * 2 = φ(n)`.
  omega

-- ============================================================================
-- Concrete instance: [ℚ(2·cos(2π/5)) : ℚ] = 2  (φ(5) = 4)
-- ============================================================================

/-- For `n = 5`, the real cyclotomic generator `2·cos(2π/5) = (√5 − 1)/2`
    generates a degree-2 subfield (`φ(5)/2 = 2`). -/
theorem fifthRoot_finrank_adjoin_trace :
    2 * finrank ℚ
        (ℚ⟮Complex.exp (2 * ↑Real.pi * Complex.I / (5 : ℕ)) +
          (Complex.exp (2 * ↑Real.pi * Complex.I / (5 : ℕ)))⁻¹⟯ :
          IntermediateField ℚ ℂ) = 4 := by
  have h := finrank_adjoin_trace_eq (n := 5) (by norm_num)
    (Complex.isPrimitiveRoot_exp 5 (by norm_num))
  rw [show Nat.totient 5 = 4 from by decide] at h
  exact h

end

end NthRootIrrationalOQ01OQ01Degree
