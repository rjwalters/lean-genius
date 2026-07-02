/-
  Reciprocals of Simplicial (Figurate) Numbers — the General-Depth Telescoping Sum

  Result.  For every depth `d ≥ 2`,

      ∑_{n=1}^∞  1 / C(n+d-1, d)  =  d / (d-1).

  Here `C(n+d-1, d)` is the `n`-th `d`-simplicial number
  (`d = 2`: triangular numbers `n(n+1)/2`; `d = 3`: tetrahedral numbers
  `n(n+1)(n+2)/6`; and so on).  Reindexing the running term to `n : ℕ` (so the
  term is `1 / C(n+d, d)`), the statement becomes

      ∑_{n=0}^∞  1 / C(n+d, d)  =  d / (d-1).

  This generalizes the parent entry `TriangularReciprocalsOQ04`, which proves the
  single depth `d = 3` case (tetrahedral reciprocals sum to `3/2`), and the
  classical depth `d = 2` case (triangular reciprocals sum to `2`).

  The proof is a single depth-`d` telescoping, uniform in `d`.  Writing `d = m+2`
  (so `m ≥ 0` ⟺ `d ≥ 2`), the summand telescopes as

      1 / C(n+m+2, m+2)  =  G(n) - G(n+1),
      G(n) := (m+2)/(m+1) · 1 / C(n+m+1, m+1).

  The telescoping identity reduces to two standard binomial absorption identities
  (`Nat.succ_mul_choose_eq`, `Nat.choose_succ_right_eq`):

      (n+m+2) · C(n+m+1, m+1) = (m+2) · C(n+m+2, m+2)          (R1)
      (n+1)   · C(n+m+2, m+1) = (m+2) · C(n+m+2, m+2)          (R2)

  from which `C(n+m+1,m+1)⁻¹ - C(n+m+2,m+1)⁻¹ = (m+1) / ((m+2)·C(n+m+2,m+2))`,
  and multiplying by `(m+2)/(m+1)` gives `C(n+m+2,m+2)⁻¹`.  The partial sums
  collapse to `(m+2)/(m+1) - G(N)`, and `G(N) → 0` because
  `C(N+m+1, m+1) ≥ N+1 → ∞`.

  No axioms, no sorries.
-/

import Mathlib

set_option linter.unusedVariables false

open Finset BigOperators Filter Topology

namespace TriangularReciprocalsOQ04OQ01

/-- The reciprocal of the `n`-th depth-`(m+2)` simplicial number,
`1 / C(n+m+2, m+2)` (depth `d = m+2 ≥ 2`). -/
noncomputable def simpReciprocal (m n : ℕ) : ℝ :=
  ((Nat.choose (n + m + 2) (m + 2) : ℝ))⁻¹

/-- The telescoping antiderivative `G(n) = (m+2)/(m+1) · 1 / C(n+m+1, m+1)`. -/
noncomputable def gTele (m n : ℕ) : ℝ :=
  ((m : ℝ) + 2) / ((m : ℝ) + 1) * ((Nat.choose (n + m + 1) (m + 1) : ℝ))⁻¹

-- ═══════════════════════════════════════════════════
-- Positivity of the binomial coefficients involved
-- ═══════════════════════════════════════════════════

private theorem choose_pos_a (m n : ℕ) : 0 < Nat.choose (n + m + 2) (m + 2) :=
  Nat.choose_pos (by omega)

private theorem choose_pos_p (m n : ℕ) : 0 < Nat.choose (n + m + 1) (m + 1) :=
  Nat.choose_pos (by omega)

private theorem choose_pos_q (m n : ℕ) : 0 < Nat.choose (n + m + 2) (m + 1) :=
  Nat.choose_pos (by omega)

-- ═══════════════════════════════════════════════════
-- The two absorption identities (as ℕ equalities)
-- ═══════════════════════════════════════════════════

/-- (R1)  `(n+m+2) · C(n+m+1, m+1) = (m+2) · C(n+m+2, m+2)`. -/
private theorem absorb_R1 (m n : ℕ) :
    (n + m + 2) * Nat.choose (n + m + 1) (m + 1)
      = (m + 2) * Nat.choose (n + m + 2) (m + 2) := by
  have h := Nat.add_one_mul_choose_eq (n + m + 1) (m + 1)
  -- h : (n+m+1+1) * C(n+m+1, m+1) = C(n+m+1+1, m+1+1) * (m+1+1)
  have e1 : n + m + 1 + 1 = n + m + 2 := by ring
  have e2 : m + 1 + 1 = m + 2 := by ring
  rw [e1, e2] at h
  rw [h]; ring

/-- (R2)  `(n+1) · C(n+m+2, m+1) = (m+2) · C(n+m+2, m+2)`. -/
private theorem absorb_R2 (m n : ℕ) :
    (n + 1) * Nat.choose (n + m + 2) (m + 1)
      = (m + 2) * Nat.choose (n + m + 2) (m + 2) := by
  have h := Nat.choose_succ_right_eq (n + m + 2) (m + 1)
  -- h : C(n+m+2, m+1+1) * (m+1+1) = C(n+m+2, m+1) * (n+m+2 - (m+1))
  have e2 : m + 1 + 1 = m + 2 := by ring
  have e3 : n + m + 2 - (m + 1) = n + 1 := by omega
  rw [e2, e3] at h
  -- h : C(n+m+2, m+2) * (m+2) = C(n+m+2, m+1) * (n+1)
  rw [mul_comm (m + 2), mul_comm (n + 1)] at *
  linarith [h]

-- ═══════════════════════════════════════════════════
-- Lemma: the depth-d telescoping identity
-- ═══════════════════════════════════════════════════

/-- `1 / C(n+m+2, m+2) = G(n) - G(n+1)`. -/
theorem simp_telescope (m n : ℕ) :
    simpReciprocal m n = gTele m n - gTele m (n + 1) := by
  unfold simpReciprocal gTele
  -- Real casts of the three (positive) binomials.
  set a : ℝ := (Nat.choose (n + m + 2) (m + 2) : ℝ) with ha_def
  set p : ℝ := (Nat.choose (n + m + 1) (m + 1) : ℝ) with hp_def
  set q : ℝ := (Nat.choose (n + m + 2) (m + 1) : ℝ) with hq_def
  have ha : 0 < a := by rw [ha_def]; exact_mod_cast choose_pos_a m n
  have hp : 0 < p := by rw [hp_def]; exact_mod_cast choose_pos_p m n
  have hq : 0 < q := by rw [hq_def]; exact_mod_cast choose_pos_q m n
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hm2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  -- The (n+1)-shifted G uses C(n+1+m+1, m+1) = C(n+m+2, m+1) = q.
  have hshift : ((Nat.choose (n + 1 + m + 1) (m + 1) : ℝ)) = q := by
    rw [hq_def]
    have e : n + 1 + m + 1 = n + m + 2 := by ring
    rw [e]
  rw [hshift]
  -- Cast the two absorption identities to ℝ.
  have R1 : ((n : ℝ) + m + 2) * p = ((m : ℝ) + 2) * a := by
    have := absorb_R1 m n
    rw [ha_def, hp_def]
    have : ((( n + m + 2) * Nat.choose (n + m + 1) (m + 1) : ℕ) : ℝ)
        = (((m + 2) * Nat.choose (n + m + 2) (m + 2) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this ⊢
    linarith [this]
  have R2 : ((n : ℝ) + 1) * q = ((m : ℝ) + 2) * a := by
    have := absorb_R2 m n
    rw [ha_def, hq_def]
    have : (((n + 1) * Nat.choose (n + m + 2) (m + 1) : ℕ) : ℝ)
        = (((m + 2) * Nat.choose (n + m + 2) (m + 2) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this ⊢
    linarith [this]
  -- p⁻¹ and q⁻¹ in terms of a.
  have hp_ne : p ≠ 0 := ne_of_gt hp
  have hq_ne : q ≠ 0 := ne_of_gt hq
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have hpinv : p⁻¹ = ((n : ℝ) + m + 2) / (((m : ℝ) + 2) * a) := by
    rw [eq_div_iff (by positivity)]
    field_simp
    nlinarith [R1]
  have hqinv : q⁻¹ = ((n : ℝ) + 1) / (((m : ℝ) + 2) * a) := by
    rw [eq_div_iff (by positivity)]
    field_simp
    nlinarith [R2]
  rw [hpinv, hqinv]
  field_simp
  ring

-- ═══════════════════════════════════════════════════
-- Partial sums via telescoping
-- ═══════════════════════════════════════════════════

/-- `∑_{i<N} 1/C(i+m+2, m+2) = (m+2)/(m+1) - G(N)`. -/
theorem partial_sum_closed_form (m N : ℕ) :
    ∑ i ∈ Finset.range N, simpReciprocal m i
      = ((m : ℝ) + 2) / ((m : ℝ) + 1) - gTele m N := by
  have htel : ∑ i ∈ Finset.range N, simpReciprocal m i
      = ∑ i ∈ Finset.range N, (gTele m i - gTele m (i + 1)) :=
    Finset.sum_congr rfl (fun i _ => simp_telescope m i)
  rw [htel, Finset.sum_range_sub' (gTele m) N]
  -- G(0) = (m+2)/(m+1) · 1/C(m+1, m+1) = (m+2)/(m+1).
  have hG0 : gTele m 0 = ((m : ℝ) + 2) / ((m : ℝ) + 1) := by
    unfold gTele
    have : Nat.choose (0 + m + 1) (m + 1) = 1 := by
      simp [Nat.choose_self]
    rw [this]; norm_num
  rw [hG0]

-- ═══════════════════════════════════════════════════
-- Lower bound on the binomial (for convergence)
-- ═══════════════════════════════════════════════════

/-- `C(N + (m+1), m+1) ≥ N + 1`.  The tail `1/C(N+m+1, m+1)` is therefore squeezed
by `1/(N+1)`. -/
private theorem choose_ge (m N : ℕ) : N + 1 ≤ Nat.choose (N + m + 1) (m + 1) := by
  induction N with
  | zero => simp [Nat.choose_self]
  | succ K ih =>
    -- C(K+1+m+1, m+1) = C((K+m+1)+1, m+1) = C(K+m+1, m+1) + C(K+m+1, m).
    have hp : K + 1 + m + 1 = (K + m + 1) + 1 := by ring
    rw [hp, Nat.choose_succ_succ' (K + m + 1) m]
    have hpos : 1 ≤ Nat.choose (K + m + 1) m := Nat.choose_pos (by omega)
    omega

-- ═══════════════════════════════════════════════════
-- Tail G(N) → 0
-- ═══════════════════════════════════════════════════

theorem gTele_tendsto_zero (m : ℕ) :
    Tendsto (fun N : ℕ => gTele m N) atTop (𝓝 0) := by
  -- G N = c · (C(N+m+1, m+1))⁻¹ with c = (m+2)/(m+1); the reciprocal → 0.
  have hrec : Tendsto (fun N : ℕ => ((Nat.choose (N + m + 1) (m + 1) : ℝ))⁻¹)
      atTop (𝓝 0) := by
    have hbound : Tendsto (fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    apply squeeze_zero (g := fun N : ℕ => (1 : ℝ) / ((N : ℝ) + 1))
    · intro N; positivity
    · intro N
      have hchoose : (N : ℝ) + 1 ≤ (Nat.choose (N + m + 1) (m + 1) : ℝ) := by
        have := choose_ge m N
        have hc : ((N + 1 : ℕ) : ℝ) ≤ ((Nat.choose (N + m + 1) (m + 1) : ℕ) : ℝ) := by
          exact_mod_cast this
        push_cast at hc; linarith [hc]
      have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      simpa [one_div] using one_div_le_one_div_of_le hpos hchoose
    · exact hbound
  have := hrec.const_mul (((m : ℝ) + 2) / ((m : ℝ) + 1))
  rw [mul_zero] at this
  simpa [gTele, mul_comm] using this

-- ═══════════════════════════════════════════════════
-- Main Theorem
-- ═══════════════════════════════════════════════════

/-- **General-depth simplicial reciprocals.**  For every depth `d = m+2 ≥ 2`,

      ∑_{n=0}^∞  1 / C(n+d, d)  =  d / (d-1),

    i.e. `HasSum (fun n => 1 / C(n+m+2, m+2)) ((m+2)/(m+1))`.  Reindexing the term to
    `n ≥ 1` (term `1/C(n+d-1, d)`) this is the classical `∑_{n≥1} 1/C(n+d-1,d) = d/(d-1)`. -/
theorem simplicial_reciprocals (m : ℕ) :
    HasSum (simpReciprocal m) (((m : ℝ) + 2) / ((m : ℝ) + 1)) := by
  have h_nonneg : ∀ n : ℕ, 0 ≤ simpReciprocal m n := by
    intro n; unfold simpReciprocal; positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg h_nonneg]
  rw [show (fun N : ℕ => ∑ i ∈ Finset.range N, simpReciprocal m i)
        = fun N : ℕ => ((m : ℝ) + 2) / ((m : ℝ) + 1) - gTele m N from
      funext (partial_sum_closed_form m)]
  have h_lim : Tendsto
      (fun N : ℕ => ((m : ℝ) + 2) / ((m : ℝ) + 1) - gTele m N)
      atTop (𝓝 (((m : ℝ) + 2) / ((m : ℝ) + 1) - 0)) :=
    tendsto_const_nhds.sub (gTele_tendsto_zero m)
  rwa [sub_zero] at h_lim

/-- tsum form of the general-depth simplicial reciprocal sum. -/
theorem simplicial_reciprocals_tsum (m : ℕ) :
    ∑' n : ℕ, simpReciprocal m n = ((m : ℝ) + 2) / ((m : ℝ) + 1) :=
  (simplicial_reciprocals m).tsum_eq

-- ═══════════════════════════════════════════════════
-- Specializations recovering the classical cases
-- ═══════════════════════════════════════════════════

/-- Depth `d = 2` (triangular reciprocals): `∑ 1/C(n+2, 2) = 2`. -/
theorem triangular_case : HasSum (simpReciprocal 0) (2 : ℝ) := by
  have h := simplicial_reciprocals 0
  norm_num at h
  simpa using h

/-- Depth `d = 3` (tetrahedral reciprocals, the parent entry): `∑ 1/C(n+3, 3) = 3/2`. -/
theorem tetrahedral_case : HasSum (simpReciprocal 1) (3 / 2 : ℝ) := by
  have h := simplicial_reciprocals 1
  norm_num at h
  simpa using h

-- Sanity checks of the summand.
/-- First term at depth `d`: `1/C(m+2, m+2) = 1`. -/
example (m : ℕ) : simpReciprocal m 0 = 1 := by
  unfold simpReciprocal; simp [Nat.choose_self]

end TriangularReciprocalsOQ04OQ01
