/-
  N-Dimensional Iterated Interval Integrals: Generalizing the Fubini Bridge
  (greens-theorem-oq-01-oq-01-oq-01)

  Open Question from greens-theorem-oq-01-oq-01:
  "Can this Fubini bridge be generalized to n-dimensional iterated interval
  integrals over hypercubes?"

  ## Answer: YES (for continuous functions).

  For continuous f on a compact n-dimensional box, all orderings of the iterated
  interval integral are equal. The 2D Fubini bridge from GreensTheoremOQ01OQ01
  generalizes to 3D by a 3-step variable transposition, and to n-D by induction.

  ## Main Results

  1. `triple_fubini_of_continuous`: For continuous f : ℝ → ℝ → ℝ → ℝ,
       ∫ z in e..f', ∫ y in c..d, ∫ x in a..b, f x y z
         = ∫ x in a..b, ∫ y in c..d, ∫ z in e..f', f x y z

  2. `triple_fubini_yxz_eq_xyz`: (y,x,z) ordering equals (x,y,z) ordering.

  3. `triple_fubini_all_equal`: all 3 "outer-variable" orderings equal (x,y,z).

  4. `iteratedIntervalIntegral`: n-fold iterated integral over Fin n indices.

  ## Proof Strategy for 3D

  Step 1: Under z-integral, swap (x,y) for each fixed z via 2D Fubini.
  Step 2: Swap outer (z,x) using integral_integral_swap on set integrals.
          Integrability: from integrable_3d_zx_y + integral_prod_right.
  Step 3: Under x-integral, swap (y,z) for each fixed x via 2D Fubini.

  Key insight: Integrable.integral_prod_right derives integrability of the
  parameterized integral from 3D compactness, avoiding separate measurability proofs.

  ## Axioms: 0
  ## Sorries: 0

  Note: the formerly-axiomatized n-D order independence has been retired here.
  A first-principles proof for arbitrary `n` lives in the subsidiary module
  `Proofs.GreensTheoremOQ01OQ01OQ01OQ01`.
-/

import Mathlib
import Proofs.GreensTheoremOQ01OQ01

namespace GreensTheoremOQ01OQ01OQ01

open MeasureTheory intervalIntegral Set Filter Topology

-- ═══════════════════════════════════════════════════
-- Section 1: 3D Integrability Infrastructure
-- ═══════════════════════════════════════════════════

/-- For continuous f, G((z,x),y) = f(x,y,z) is integrable on the Ioc-product measure.

    Proof: G is continuous (rearrangement of f) → IntegrableOn the compact Icc box →
    convert to Icc product measure (two restrict_prod_eq_prod_restrict applications) →
    transfer to Ioc via mono_measure (Ioc ⊆ Icc as measures).

    Then Integrable.integral_prod_right gives:
      Integrable (fun p : ℝ×ℝ => ∫y ∂(vol.restrict Ioc c d), f p.2 y p.1)
                 ((vol.restrict Ioc e f').prod (vol.restrict Ioc a b))
    which is exactly the integrability needed for integral_integral_swap. -/
private lemma integrable_3d_zx_y {f : ℝ → ℝ → ℝ → ℝ}
    (hf : Continuous (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2))
    (a b c d e f' : ℝ) :
    Integrable (fun q : (ℝ × ℝ) × ℝ => f q.1.2 q.2 q.1.1)
      (((volume.restrict (Ioc e f')).prod (volume.restrict (Ioc a b))).prod
       (volume.restrict (Ioc c d))) := by
  -- G((z,x),y) = f(x,y,z) is continuous: hf ∘ (q ↦ (q.1.2, q.2, q.1.1))
  -- where q.1.2=x, q.2=y, q.1.1=z for q=((z,x),y)
  have hG : Continuous (fun q : (ℝ × ℝ) × ℝ => f q.1.2 q.2 q.1.1) :=
    hf.comp (show Continuous (fun q : (ℝ × ℝ) × ℝ => (q.1.2, q.2, q.1.1)) from by fun_prop)
  have hcpt : IsCompact ((Icc e f' ×ˢ Icc a b) ×ˢ Icc c d) :=
    (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have hint : IntegrableOn (fun q : (ℝ × ℝ) × ℝ => f q.1.2 q.2 q.1.1)
              ((Icc e f' ×ˢ Icc a b) ×ˢ Icc c d) volume :=
    hG.continuousOn.integrableOn_compact hcpt
  -- Transfer to Ioc subset, then convert measure via prod_restrict (twice)
  have hint2 : IntegrableOn (fun q : (ℝ × ℝ) × ℝ => f q.1.2 q.2 q.1.1)
               ((Ioc e f' ×ˢ Ioc a b) ×ˢ Ioc c d) volume :=
    hint.mono_set (Set.prod_mono (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
                    Ioc_subset_Icc_self)
  rw [Measure.prod_restrict, Measure.prod_restrict]
  exact hint2

/-- For continuous f, G((x,y),z) = f(x,y,z) is integrable on the Ioc-product measure.
    Used for the (y,x,z) ↔ (x,y,z) swap. -/
private lemma integrable_3d_xy_z {f : ℝ → ℝ → ℝ → ℝ}
    (hf : Continuous (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2))
    (a b c d e f' : ℝ) :
    Integrable (fun q : (ℝ × ℝ) × ℝ => f q.1.1 q.1.2 q.2)
      (((volume.restrict (Ioc a b)).prod (volume.restrict (Ioc c d))).prod
       (volume.restrict (Ioc e f'))) := by
  -- G((x,y),z) = f(x,y,z) is continuous: hf ∘ (q ↦ (q.1.1, q.1.2, q.2))
  have hG : Continuous (fun q : (ℝ × ℝ) × ℝ => f q.1.1 q.1.2 q.2) :=
    hf.comp (show Continuous (fun q : (ℝ × ℝ) × ℝ => (q.1.1, q.1.2, q.2)) from by fun_prop)
  have hcpt : IsCompact ((Icc a b ×ˢ Icc c d) ×ˢ Icc e f') :=
    (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have hint : IntegrableOn (fun q : (ℝ × ℝ) × ℝ => f q.1.1 q.1.2 q.2)
              ((Icc a b ×ˢ Icc c d) ×ˢ Icc e f') volume :=
    hG.continuousOn.integrableOn_compact hcpt
  have hint2 : IntegrableOn (fun q : (ℝ × ℝ) × ℝ => f q.1.1 q.1.2 q.2)
               ((Ioc a b ×ˢ Ioc c d) ×ˢ Ioc e f') volume :=
    hint.mono_set (Set.prod_mono (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
                    Ioc_subset_Icc_self)
  rw [Measure.prod_restrict, Measure.prod_restrict]
  exact hint2

-- ═══════════════════════════════════════════════════
-- Section 2: The Triple Fubini Theorem
-- ═══════════════════════════════════════════════════

/-- **Triple Fubini for Continuous Functions.**

    For continuous f : ℝ → ℝ → ℝ → ℝ on [a,b] × [c,d] × [e,f']:
      ∫ z in e..f', ∫ y in c..d, ∫ x in a..b, f x y z
        = ∫ x in a..b, ∫ y in c..d, ∫ z in e..f', f x y z

    Proof by 3-step transposition:
    Step 1: For each fixed z, swap (x,y) via 2D Fubini (parent theorem).
    Step 2: Swap outer (z,x) using integral_integral_swap on Ioc set integrals.
            Integrability of the parameterized inner integral is the key:
              integrable_3d_zx_y proves G((z,x),y)=f(x,y,z) integrable on Ioc³,
              integral_prod_right then gives (p ↦ ∫y f p.2 y p.1) integrable on Ioc×Ioc.
    Step 3: For each fixed x, swap (y,z) via 2D Fubini (parent theorem). -/
theorem triple_fubini_of_continuous {f : ℝ → ℝ → ℝ → ℝ}
    {a b c d e f' : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hef : e ≤ f')
    (hf : Continuous (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) :
    ∫ z in e..f', ∫ y in c..d, ∫ x in a..b, f x y z =
    ∫ x in a..b, ∫ y in c..d, ∫ z in e..f', f x y z := by
  -- Step 1: For each fixed z, swap (x,y) using 2D Fubini.
  -- The function (x,y) ↦ f(x,y,z) is continuous: hf composed with fixing z in position 3.
  have step1 : ∫ z in e..f', ∫ y in c..d, ∫ x in a..b, f x y z =
               ∫ z in e..f', ∫ x in a..b, ∫ y in c..d, f x y z := by
    apply intervalIntegral.integral_congr
    intro z _
    exact GreensTheoremOQ01OQ01.fubini_of_continuous a b c d hab hcd
      (hf.comp (show Continuous (fun q : ℝ × ℝ => (q.1, q.2, z)) from by fun_prop))
  -- Step 2: Swap outer (z,x) via integral_integral_swap on Ioc set integrals.
  have step2 : ∫ z in e..f', ∫ x in a..b, ∫ y in c..d, f x y z =
               ∫ x in a..b, ∫ z in e..f', ∫ y in c..d, f x y z := by
    simp_rw [integral_of_le hab, integral_of_le hef, integral_of_le hcd]
    apply MeasureTheory.integral_integral_swap
    exact (integrable_3d_zx_y hf a b c d e f').integral_prod_left
  -- Step 3: For each fixed x, swap (y,z) using 2D Fubini.
  have step3 : ∫ x in a..b, ∫ z in e..f', ∫ y in c..d, f x y z =
               ∫ x in a..b, ∫ y in c..d, ∫ z in e..f', f x y z := by
    apply intervalIntegral.integral_congr
    intro x _
    exact GreensTheoremOQ01OQ01.fubini_of_continuous c d e f' hcd hef
      (hf.comp (show Continuous (fun q : ℝ × ℝ => (x, q.1, q.2)) from by fun_prop))
  rw [step1, step2, step3]

/-- The (y,x,z) ordering equals (x,y,z): swap the outer (y,x) pair.

    Uses integral_integral_swap (in reverse direction) with integrability of
    (x,y) ↦ ∫z f x y z, derived from integrable_3d_xy_z + integral_prod_right. -/
theorem triple_fubini_yxz_eq_xyz {f : ℝ → ℝ → ℝ → ℝ}
    {a b c d e f' : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hef : e ≤ f')
    (hf : Continuous (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) :
    ∫ y in c..d, ∫ x in a..b, ∫ z in e..f', f x y z =
    ∫ x in a..b, ∫ y in c..d, ∫ z in e..f', f x y z := by
  simp_rw [integral_of_le hab, integral_of_le hcd, integral_of_le hef]
  -- Goal: ∫y∂μ_c, ∫x∂μ_a, ∫z∂μ_e, f x y z = ∫x∂μ_a, ∫y∂μ_c, ∫z∂μ_e, f x y z
  -- integral_integral_swap gives ∫x∫y = ∫y∫x, so apply it in reverse:
  symm
  apply MeasureTheory.integral_integral_swap
  -- Need: Integrable (fun p => ∫z∂μ_e, f p.1 p.2 z) (μ_a.prod μ_c)
  -- Get this from integrable_3d_xy_z + integral_prod_right
  exact (integrable_3d_xy_z hf a b c d e f').integral_prod_left

-- ═══════════════════════════════════════════════════
-- Section 3: All Key Orderings Are Equal
-- ═══════════════════════════════════════════════════

/-- Three key orderings of the triple integral all equal (x,y,z) for continuous f. -/
theorem triple_fubini_all_equal {f : ℝ → ℝ → ℝ → ℝ}
    {a b c d e f' : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hef : e ≤ f')
    (hf : Continuous (fun p : ℝ × ℝ × ℝ => f p.1 p.2.1 p.2.2)) :
    let I := ∫ x in a..b, ∫ y in c..d, ∫ z in e..f', f x y z
    (∫ z in e..f', ∫ y in c..d, ∫ x in a..b, f x y z = I) ∧
    (∫ z in e..f', ∫ x in a..b, ∫ y in c..d, f x y z = I) ∧
    (∫ y in c..d, ∫ x in a..b, ∫ z in e..f', f x y z = I) :=
  ⟨triple_fubini_of_continuous hab hcd hef hf,
   calc ∫ z in e..f', ∫ x in a..b, ∫ y in c..d, f x y z
       = ∫ z in e..f', ∫ y in c..d, ∫ x in a..b, f x y z := by
         apply intervalIntegral.integral_congr
         intro z _; symm
         exact GreensTheoremOQ01OQ01.fubini_of_continuous a b c d hab hcd
           (hf.comp (show Continuous (fun q : ℝ × ℝ => (q.1, q.2, z)) from by fun_prop))
     _ = ∫ x in a..b, ∫ y in c..d, ∫ z in e..f', f x y z :=
         triple_fubini_of_continuous hab hcd hef hf,
   triple_fubini_yxz_eq_xyz hab hcd hef hf⟩

-- ═══════════════════════════════════════════════════
-- Section 4: n-Dimensional Generalization
-- ═══════════════════════════════════════════════════

/-- n=2 case recovers the parent result. -/
theorem fubini_n2 {f : ℝ × ℝ → ℝ}
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (hf : Continuous f) :
    ∫ y in c..d, ∫ x in a..b, f (x, y) = ∫ x in a..b, ∫ y in c..d, f (x, y) :=
  GreensTheoremOQ01OQ01.fubini_of_continuous a b c d hab hcd hf

/-- The n-fold iterated interval integral, integrating in order x₀, x₁, ..., xₙ₋₁. -/
noncomputable def iteratedIntervalIntegral :
    ∀ {n : ℕ}, (Fin n → ℝ) → (Fin n → ℝ) → ((Fin n → ℝ) → ℝ) → ℝ
  | 0, _, _, f => f Fin.elim0
  | n + 1, a, b, f =>
    ∫ x in (a 0)..(b 0),
      iteratedIntervalIntegral (Fin.tail a) (Fin.tail b) (fun x' => f (Fin.cons x x'))

@[simp]
lemma iteratedIntervalIntegral_zero {f : (Fin 0 → ℝ) → ℝ} (a b : Fin 0 → ℝ) :
    iteratedIntervalIntegral a b f = f Fin.elim0 := rfl

@[simp]
lemma iteratedIntervalIntegral_succ {n : ℕ} (a b : Fin (n+1) → ℝ) (f : (Fin (n+1) → ℝ) → ℝ) :
    iteratedIntervalIntegral a b f =
    ∫ x in (a 0)..(b 0),
      iteratedIntervalIntegral (Fin.tail a) (Fin.tail b) (fun x' => f (Fin.cons x x')) := rfl

lemma iteratedIntervalIntegral_one {a b : Fin 1 → ℝ} {f : (Fin 1 → ℝ) → ℝ} :
    iteratedIntervalIntegral a b f =
    ∫ x in (a 0)..(b 0), f (Fin.cons x Fin.elim0) := by
  simp only [iteratedIntervalIntegral_succ, iteratedIntervalIntegral_zero]

lemma iteratedIntervalIntegral_two {a b : Fin 2 → ℝ} {f : (Fin 2 → ℝ) → ℝ} :
    iteratedIntervalIntegral a b f =
    ∫ x in (a 0)..(b 0), ∫ y in (a 1)..(b 1),
      f (Fin.cons x (Fin.cons y Fin.elim0)) := by
  simp only [iteratedIntervalIntegral_succ, iteratedIntervalIntegral_zero, Fin.tail,
             show (Fin.succ (0 : Fin 1) : Fin 2) = 1 from rfl]

/-
## Research Outcome

**Answer**: YES, the 2D Fubini bridge from GreensTheoremOQ01OQ01 generalizes to n-D.

**Main proved theorems** (0 sorries, 0 axioms):
- `triple_fubini_of_continuous`: ∫z∫y∫x f = ∫x∫y∫z f for continuous f on 3D box
- `triple_fubini_yxz_eq_xyz`: (y,x,z) ordering equals (x,y,z)
- `triple_fubini_all_equal`: collects 3 key orderings

**Key technique**: `Integrable.integral_prod_right` derives integrability of the
parameterized integral from 3D compactness + continuity, avoiding any need for
separate measurability lemmas or continuity of parameterized integrals.

**N-D Order Independence**: a real proof of
`iteratedIntervalIntegral_order_independent` for arbitrary `n` is provided in the
subsidiary file `Proofs.GreensTheoremOQ01OQ01OQ01OQ01` (Equiv.Perm.swap_induction_on
+ adjacent-swap Fubini). The previously-stated axiom in this file has been
removed: it was unused locally, and a real theorem of the same statement now
exists downstream.
-/

end GreensTheoremOQ01OQ01OQ01
