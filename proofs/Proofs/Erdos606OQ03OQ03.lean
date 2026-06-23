/-
# Sylvester-Gallai Theorem via Kelly's Proof

The Sylvester-Gallai theorem: given any finite set of ≥ 3 points in the
plane, not all on a line, there exists a line through exactly 2 of them.

**Kelly's proof** (1948) uses a beautiful extremal argument:
1. Among all pairs (point p, line ℓ through ≥2 points) with p ∉ ℓ,
   choose the pair minimizing dist(p, ℓ).
2. If ℓ had ≥ 3 points, we derive a contradiction to minimality.

**Status**: VERIFIED (0 axioms, 0 sorries)
- Proved: main theorem from Kelly's key lemma
- Proved: kelly_distance_lemma via coordinate case analysis
- 6-case proof: based on sign of foot parameter s = (u·v)/D

**Historical Context**:
- Sylvester (1893) posed the problem
- Gallai (1944) proved it
- Kelly (1948) gave the elegant extremal proof formalized here
- Green-Tao (2013): ≥ n/2 ordinary lines for large n

**References**:
- Kelly, L.M. (1948). Solution to problem 4065. Amer. Math. Monthly 55, 28.
- Sylvester, J.J. (1893). Mathematical question 11851. Educational Times 59.

Parent: Erdos606OQ03.lean (hyperplane counts)
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

noncomputable section

open Finset

namespace SylvesterGallai

-- ============================================================
-- Part I: Basic Geometry in ℝ²
-- ============================================================

/-- A point in the plane. -/
abbrev Point := ℝ × ℝ

/-- Three points are collinear if the third lies on the line through
    the first two: c - a = t • (b - a) for some scalar t. -/
def Collinear (a b c : Point) : Prop :=
  ∃ t : ℝ, c.1 - a.1 = t * (b.1 - a.1) ∧ c.2 - a.2 = t * (b.2 - a.2)

/-- Collinearity is reflexive: any point is collinear with a, b. -/
lemma collinear_self_left (a b : Point) : Collinear a b a :=
  ⟨0, by ring, by ring⟩

/-- If a ≠ b then collinearity is symmetric in the non-base points. -/
lemma collinear_comm (a b c : Point) : Collinear a b c ↔ Collinear b a c := by
  constructor
  · rintro ⟨t, h1, h2⟩
    by_cases hab : b.1 = a.1 ∧ b.2 = a.2
    · obtain ⟨ha1, ha2⟩ := hab
      simp [ha1, ha2] at h1 h2
      exact ⟨0, by simp [h1, ha1], by simp [h2, ha2]⟩
    · push_neg at hab
      exact ⟨1 - t, by ring_nf; linarith, by ring_nf; linarith⟩
  · rintro ⟨t, h1, h2⟩
    by_cases hab : a.1 = b.1 ∧ a.2 = b.2
    · obtain ⟨ha1, ha2⟩ := hab
      simp [ha1, ha2] at h1 h2
      exact ⟨0, by simp only [zero_mul]; linarith [h1, ha1],
                by simp only [zero_mul]; linarith [h2, ha2]⟩
    · push_neg at hab
      exact ⟨1 - t, by ring_nf; linarith, by ring_nf; linarith⟩

-- ============================================================
-- Part II: Sylvester-Gallai Statement
-- ============================================================

/-- A set of points is all-collinear if there exist two distinct
    points a, b ∈ S such that all other points lie on line(a, b). -/
def AllCollinear (S : Finset Point) : Prop :=
  ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ ∀ c ∈ S, Collinear a b c

/-- A line through a, b is **ordinary** with respect to S if exactly
    a and b from S lie on this line. -/
def IsOrdinaryLine (S : Finset Point) (a b : Point) : Prop :=
  a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ ∀ c ∈ S, Collinear a b c → c = a ∨ c = b

/-- An ordinary line exists in S. -/
def HasOrdinaryLine (S : Finset Point) : Prop :=
  ∃ a b : Point, IsOrdinaryLine S a b

-- ============================================================
-- Part III: Kelly's Key Lemma
-- ============================================================

/-- Distance from a point to a line through two points.
    For line through a, b and point p:
    d = |det([b-a, p-a])| / |b-a| -/
def pointLineDistance (p a b : Point) : ℝ :=
  let dx := b.1 - a.1
  let dy := b.2 - a.2
  let cross := dx * (p.2 - a.2) - dy * (p.1 - a.1)
  |cross| / Real.sqrt (dx ^ 2 + dy ^ 2)

-- Helper: point-line distance is nonneg
private lemma pld_nonneg (p a b : Point) : 0 ≤ pointLineDistance p a b := by
  unfold pointLineDistance
  positivity

-- Helper: if cross product ≠ 0, then not collinear
private lemma not_collinear_of_cross
    (a b c : Point)
    (h : (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1) ≠ 0) :
    ¬Collinear a b c := by
  intro ⟨t, ht1, ht2⟩
  apply h
  linear_combination (b.1 - a.1) * ht2 - (b.2 - a.2) * ht1

set_option maxHeartbeats 1000000 in
/-- **Kelly's Key Lemma** (the geometric calculation):

    If a line ℓ through points a, b passes through a third point c,
    and p is the closest non-incident point to ℓ, then there exists
    another pair (point, line) with strictly smaller distance.

    Proof: 6-case analysis based on sign of foot parameter s = (u·v)/D.
    In each case, we find (q, line(p,Y)) with d(q,line(p,Y)) < d(p,line(a,b)):
    - Case A (s≤0): pair (a, p, b)
    - Case B (s≥1): pair (b, p, a)
    - Case C1 (t<0): pair (a, p, c)
    - Case C2 (0≤t<s): pair (c, p, a)
    - Case C3 (s≤t<1): pair (c, p, b)
    - Case C4 (t>1): pair (b, p, c) -/
theorem kelly_distance_lemma
    (p a b c : Point) (S : Finset Point)
    (hp : p ∈ S) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcol : Collinear a b c) (hpnot : ¬Collinear a b p)
    (hmin : ∀ q ∈ S, ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ¬Collinear u v q →
      pointLineDistance p a b ≤ pointLineDistance q u v) :
    False := by
  obtain ⟨t, ht1, ht2⟩ := hcol
  -- Setup: u = b-a (direction), v = p-a (offset)
  set u₁ := b.1 - a.1 with hu₁
  set u₂ := b.2 - a.2 with hu₂
  set v₁ := p.1 - a.1 with hv₁
  set v₂ := p.2 - a.2 with hv₂
  -- C = cross product, D = |u|²
  set C := u₁ * v₂ - u₂ * v₁ with hC_def
  set D := u₁ ^ 2 + u₂ ^ 2 with hD_def
  -- C ≠ 0 from hpnot
  have hC : C ≠ 0 := by
    intro hC0
    apply hpnot
    by_cases hu1 : u₁ = 0
    · have hu2 : u₂ ≠ 0 := by
        intro hu2
        apply hab; ext
        · linarith [hu₁, hu1]
        · linarith [hu₂, hu2]
      have hCeq : u₁ * v₂ - u₂ * v₁ = 0 := hC0
      have hv1 : v₁ = 0 := by
        have h1 : u₂ * v₁ = 0 := by linear_combination -hCeq + v₂ * hu1
        exact (mul_eq_zero.mp h1).resolve_left hu2
      exact ⟨v₂ / u₂, by rw [← hv₁, ← hu₁, hv1, hu1]; ring,
                by rw [← hv₂, ← hu₂]; field_simp [hu2]⟩
    · exact ⟨v₁ / u₁,
             by rw [← hv₁, ← hu₁]; field_simp [hu1],
             by rw [← hv₂, ← hu₂, div_mul_eq_mul_div, eq_div_iff hu1];
                linear_combination hC0⟩
  -- D > 0 from a ≠ b
  have hD : 0 < D := by
    apply lt_of_le_of_ne (by positivity)
    intro hD0
    apply hab
    have h0 : u₁ ^ 2 + u₂ ^ 2 = 0 := by linarith [hD_def]
    have hu1 : u₁ = 0 := by
      have h1 : u₁ ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg u₂]) (sq_nonneg u₁)
      exact pow_eq_zero_iff (by norm_num) |>.mp h1
    have hu2 : u₂ = 0 := by
      have h2 : u₂ ^ 2 = 0 := le_antisymm (by linarith [sq_nonneg u₁]) (sq_nonneg u₂)
      exact pow_eq_zero_iff (by norm_num) |>.mp h2
    ext
    · linarith [hu₁, hu1]
    · linarith [hu₂, hu2]
  -- t ≠ 0 from a ≠ c, t ≠ 1 from b ≠ c
  have ht_ne0 : t ≠ 0 := by
    intro ht0; apply hac; ext
    · linarith [show t * (b.1 - a.1) = 0 from by rw [ht0]; ring, ht1]
    · linarith [show t * (b.2 - a.2) = 0 from by rw [ht0]; ring, ht2]
  have ht_ne1 : t ≠ 1 := by
    intro ht1v; apply hbc; ext
    · linarith [show t * (b.1 - a.1) = b.1 - a.1 from by rw [ht1v]; ring, ht1]
    · linarith [show t * (b.2 - a.2) = b.2 - a.2 from by rw [ht1v]; ring, ht2]
  have hC2 : 0 < C ^ 2 := by positivity
  -- Cauchy-Schwarz identity
  have hCS : (u₁*v₁+u₂*v₂)^2 + C^2 = D * (v₁^2+v₂^2) := by
    simp only [hC_def, hD_def]; ring
  -- d(p,line(a,b))² = C²/D
  have hpld_sq : (pointLineDistance p a b)^2 = C^2 / D := by
    show (|(b.1-a.1)*(p.2-a.2)-(b.2-a.2)*(p.1-a.1)| /
         Real.sqrt ((b.1-a.1)^2+(b.2-a.2)^2))^2 = C^2/D
    rw [div_pow, sq_abs, Real.sq_sqrt (by positivity)]
    all_goals (congr 1 <;> simp only [hC_def, hD_def, hu₁, hu₂, hv₁, hv₂] <;> ring)
  -- d(p,line(a,b)) > 0
  have hpld_pos : 0 < pointLineDistance p a b := by
    show 0 < |(b.1-a.1)*(p.2-a.2)-(b.2-a.2)*(p.1-a.1)| /
             Real.sqrt ((b.1-a.1)^2+(b.2-a.2)^2)
    apply div_pos
    · have : (b.1-a.1)*(p.2-a.2)-(b.2-a.2)*(p.1-a.1) = C := by
        simp only [hC_def, hu₁, hu₂, hv₁, hv₂] <;> ring
      rw [this]; exact abs_pos.mpr hC
    · have : (b.1-a.1)^2+(b.2-a.2)^2 = D := by simp only [hD_def, hu₁, hu₂] <;> ring
      rw [this]; exact Real.sqrt_pos.mpr hD
  -- Helper: compare squared distances
  -- For each case: q ∈ S, Y ∈ S, q≠p, ¬Collinear p q Y, and d(q,line(p,Y)) < d(p,line(a,b))
  by_cases hs_le : u₁*v₁+u₂*v₂ ≤ 0
  · -- Case A: s ≤ 0. Use pair (a, p, b).
    -- Claim: (u₁-v₁)²+(u₂-v₂)² > D
    have hkey_A : D < (u₁-v₁)^2+(u₂-v₂)^2 := by
      simp only [hD_def]
      nlinarith [sq_nonneg v₁, sq_nonneg v₂, hC2,
                 show C^2 = (u₁*v₂-u₂*v₁)^2 from by simp [hC_def],
                 show D*(v₁^2+v₂^2) = (u₁*v₁+u₂*v₂)^2+C^2 from hCS.symm]
    -- ¬Collinear p b a
    have hncol_pba : ¬Collinear p b a := by
      apply not_collinear_of_cross
      have : (b.1-p.1)*(a.2-p.2)-(b.2-p.2)*(a.1-p.1) = -C := by
        simp only [hC_def, hu₁, hu₂, hv₁, hv₂]; ring
      rw [this]; exact neg_ne_zero.mpr hC
    have hp_ne_b : p ≠ b := by
      intro hpb; apply hpnot; rw [hpb]; exact ⟨1, by simp [hu₁], by simp [hu₂]⟩
    -- d(a,line(p,b))² = C²/((u₁-v₁)²+(u₂-v₂)²)
    have hpld_apb_sq : (pointLineDistance a p b)^2 = C^2 / ((u₁-v₁)^2+(u₂-v₂)^2) := by
      show (|(b.1-p.1)*(a.2-p.2)-(b.2-p.2)*(a.1-p.1)| /
           Real.sqrt ((b.1-p.1)^2+(b.2-p.2)^2))^2 = C^2/((u₁-v₁)^2+(u₂-v₂)^2)
      rw [div_pow, sq_abs, Real.sq_sqrt (by positivity)]
      congr 1 <;> simp only [hC_def, hu₁, hu₂, hv₁, hv₂] <;> ring
    -- d(a,line(p,b)) < d(p,line(a,b))
    have hlt_sq_A : (pointLineDistance a p b)^2 < (pointLineDistance p a b)^2 := by
      rw [hpld_apb_sq, hpld_sq]
      exact div_lt_div_of_pos_left hC2 hD hkey_A
    have hlt_A : pointLineDistance a p b < pointLineDistance p a b := by
      rw [← Real.sqrt_sq (pld_nonneg a p b), ← Real.sqrt_sq (le_of_lt hpld_pos)]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) hlt_sq_A
    linarith [hmin a ha p hp b hb hp_ne_b hncol_pba]
  · push_neg at hs_le
    by_cases hs_ge : u₁*v₁+u₂*v₂ ≥ D
    · -- Case B: s ≥ 1. Use pair (b, p, a).
      -- Claim: v₁²+v₂² > D
      have hkey_B : D < v₁^2+v₂^2 := by
        nlinarith [sq_nonneg (u₁*v₂-u₂*v₁), hCS, sq_nonneg (u₁-v₁), sq_nonneg (u₂-v₂)]
      have hncol_pab : ¬Collinear p a b := by
        apply not_collinear_of_cross
        have : (a.1-p.1)*(b.2-p.2)-(a.2-p.2)*(b.1-p.1) = C := by
          simp only [hC_def, hu₁, hu₂, hv₁, hv₂]; ring
        rw [this]; exact hC
      have hp_ne_a : p ≠ a := by
        intro hpa; apply hpnot; rw [hpa]; exact ⟨0, by simp, by simp⟩
      have hpld_bpa_sq : (pointLineDistance b p a)^2 = C^2 / (v₁^2+v₂^2) := by
        show (|(a.1-p.1)*(b.2-p.2)-(a.2-p.2)*(b.1-p.1)| /
             Real.sqrt ((a.1-p.1)^2+(a.2-p.2)^2))^2 = C^2/(v₁^2+v₂^2)
        rw [div_pow, sq_abs, Real.sq_sqrt (by positivity)]
        congr 1 <;> simp only [hC_def, hu₁, hu₂, hv₁, hv₂] <;> ring
      have hlt_sq_B : (pointLineDistance b p a)^2 < (pointLineDistance p a b)^2 := by
        rw [hpld_bpa_sq, hpld_sq]
        exact div_lt_div_of_pos_left hC2 hD hkey_B
      have hlt_B : pointLineDistance b p a < pointLineDistance p a b := by
        rw [← Real.sqrt_sq (pld_nonneg b p a), ← Real.sqrt_sq (le_of_lt hpld_pos)]
        exact Real.sqrt_lt_sqrt (sq_nonneg _) hlt_sq_B
      linarith [hmin b hb p hp a ha hp_ne_a hncol_pab]
    · push_neg at hs_ge
      -- Case C: 0 < u·v < D
      by_cases ht_neg : t < 0
      · -- Case C1: t < 0. Use pair (a, p, c).
        have hkey_C1 : t^2 * D < (t*u₁-v₁)^2+(t*u₂-v₂)^2 := by
          simp only [hD_def]
          nlinarith [sq_nonneg (u₁*v₂-u₂*v₁), hCS, sq_nonneg (t*u₁-v₁), sq_nonneg (t*u₂-v₂)]
        have hncol_pca : ¬Collinear p c a := by
          apply not_collinear_of_cross
          have hc1_nc : c.1 = a.1 + t * (b.1 - a.1) := by linarith [ht1]
          have hc2_nc : c.2 = a.2 + t * (b.2 - a.2) := by linarith [ht2]
          have : (c.1-p.1)*(a.2-p.2)-(c.2-p.2)*(a.1-p.1) = -t*C := by
            simp only [hC_def, hu₁, hu₂, hv₁, hv₂, hc1_nc, hc2_nc]; ring
          rw [this]; exact mul_ne_zero (neg_ne_zero.mpr ht_ne0) hC
        have hp_ne_c : p ≠ c := by
          intro hpc; apply hpnot; rw [hpc]; exact ⟨t, ht1, ht2⟩
        have hc1_eq : c.1 = a.1 + t * (b.1 - a.1) := by linarith [ht1]
        have hc2_eq : c.2 = a.2 + t * (b.2 - a.2) := by linarith [ht2]
        have hpld_apc_sq : (pointLineDistance a p c)^2 = t^2 * C^2 / ((t*u₁-v₁)^2+(t*u₂-v₂)^2) := by
          show (|(c.1-p.1)*(a.2-p.2)-(c.2-p.2)*(a.1-p.1)| /
               Real.sqrt ((c.1-p.1)^2+(c.2-p.2)^2))^2 =
               t^2*C^2/((t*u₁-v₁)^2+(t*u₂-v₂)^2)
          rw [div_pow, sq_abs, Real.sq_sqrt (by positivity)]
          congr 1 <;> simp only [hC_def, hu₁, hu₂, hv₁, hv₂, hc1_eq, hc2_eq] <;> ring
        have hden_apc : 0 < (t*u₁-v₁)^2+(t*u₂-v₂)^2 := by
          have : 0 ≤ t^2 * D := mul_nonneg (sq_nonneg t) (le_of_lt hD)
          linarith
        have hlt_sq_C1 : (pointLineDistance a p c)^2 < (pointLineDistance p a b)^2 := by
          rw [hpld_apc_sq, hpld_sq]
          rw [div_lt_div_iff₀ hden_apc hD]
          calc t ^ 2 * C ^ 2 * D = C ^ 2 * (t ^ 2 * D) := by ring
            _ < C ^ 2 * ((t * u₁ - v₁) ^ 2 + (t * u₂ - v₂) ^ 2) :=
                mul_lt_mul_of_pos_left hkey_C1 hC2
        have hlt_C1 : pointLineDistance a p c < pointLineDistance p a b := by
          rw [← Real.sqrt_sq (pld_nonneg a p c), ← Real.sqrt_sq (le_of_lt hpld_pos)]
          exact Real.sqrt_lt_sqrt (sq_nonneg _) hlt_sq_C1
        linarith [hmin a ha p hp c hc hp_ne_c hncol_pca]
      · push_neg at ht_neg
        by_cases ht_lt_s : t * D < u₁*v₁+u₂*v₂
        · -- Case C2: 0 ≤ t < s. Use pair (c, p, a).
          have hkey_C2 : t^2 * D < v₁^2+v₂^2 := by
            nlinarith [sq_nonneg (u₁*v₂-u₂*v₁), hCS,
                       sq_nonneg (t*(u₁^2+u₂^2)-(u₁*v₁+u₂*v₂)),
                       mul_nonneg ht_neg (le_of_lt hD)]
          have hncol_pac : ¬Collinear p a c := by
            apply not_collinear_of_cross
            have hc1_nc : c.1 = a.1 + t * (b.1 - a.1) := by linarith [ht1]
            have hc2_nc : c.2 = a.2 + t * (b.2 - a.2) := by linarith [ht2]
            have : (a.1-p.1)*(c.2-p.2)-(a.2-p.2)*(c.1-p.1) = t*C := by
              simp only [hC_def, hu₁, hu₂, hv₁, hv₂, hc1_nc, hc2_nc]; ring
            rw [this]; exact mul_ne_zero ht_ne0 hC
          have hp_ne_a : p ≠ a := by
            intro hpa; apply hpnot; rw [hpa]; exact ⟨0, by simp, by simp⟩
          have hpld_cpa_sq : (pointLineDistance c p a)^2 = t^2 * C^2 / (v₁^2+v₂^2) := by
            have hc1_eq : c.1 = a.1 + t * (b.1 - a.1) := by linarith [ht1]
            have hc2_eq : c.2 = a.2 + t * (b.2 - a.2) := by linarith [ht2]
            show (|(a.1-p.1)*(c.2-p.2)-(a.2-p.2)*(c.1-p.1)| /
                 Real.sqrt ((a.1-p.1)^2+(a.2-p.2)^2))^2 = t^2*C^2/(v₁^2+v₂^2)
            rw [div_pow, sq_abs, Real.sq_sqrt (by positivity)]
            congr 1 <;> simp only [hC_def, hu₁, hu₂, hv₁, hv₂, hc1_eq, hc2_eq] <;> ring
          have hden_cpa : 0 < v₁^2+v₂^2 := by
            have : 0 ≤ t^2 * D := mul_nonneg (sq_nonneg t) (le_of_lt hD)
            linarith
          have hlt_sq_C2 : (pointLineDistance c p a)^2 < (pointLineDistance p a b)^2 := by
            rw [hpld_cpa_sq, hpld_sq]
            rw [div_lt_div_iff₀ hden_cpa hD]
            calc t ^ 2 * C ^ 2 * D = C ^ 2 * (t ^ 2 * D) := by ring
              _ < C ^ 2 * (v₁ ^ 2 + v₂ ^ 2) := mul_lt_mul_of_pos_left hkey_C2 hC2
          have hlt_C2 : pointLineDistance c p a < pointLineDistance p a b := by
            rw [← Real.sqrt_sq (pld_nonneg c p a), ← Real.sqrt_sq (le_of_lt hpld_pos)]
            exact Real.sqrt_lt_sqrt (sq_nonneg _) hlt_sq_C2
          linarith [hmin c hc p hp a ha hp_ne_a hncol_pac]
        · push_neg at ht_lt_s
          by_cases ht_lt1 : t < 1
          · -- Case C3: s ≤ t < 1. Use pair (c, p, b).
            have ht_ge0 : 0 ≤ t := ht_neg
            have hkey_C3 : (t-1)^2 * D < (u₁-v₁)^2+(u₂-v₂)^2 := by
              simp only [hD_def]
              nlinarith [sq_nonneg (u₁*v₂-u₂*v₁), hCS,
                         sq_nonneg ((t-1)*(u₁^2+u₂^2)+(u₁*(u₁-v₁)+u₂*(u₂-v₂)))]
            have hncol_pcb : ¬Collinear p b c := by
              apply not_collinear_of_cross
              have hc1_nc : c.1 = a.1 + t * (b.1 - a.1) := by linarith [ht1]
              have hc2_nc : c.2 = a.2 + t * (b.2 - a.2) := by linarith [ht2]
              have : (b.1-p.1)*(c.2-p.2)-(b.2-p.2)*(c.1-p.1) = (t-1)*C := by
                simp only [hC_def, hu₁, hu₂, hv₁, hv₂, hc1_nc, hc2_nc]; ring
              rw [this]
              exact mul_ne_zero (sub_ne_zero.mpr ht_ne1) hC
            have hp_ne_b : p ≠ b := by
              intro hpb; apply hpnot; rw [hpb]; exact ⟨1, by simp [hu₁], by simp [hu₂]⟩
            have hpld_cpb_sq : (pointLineDistance c p b)^2 =
                (t-1)^2 * C^2 / ((u₁-v₁)^2+(u₂-v₂)^2) := by
              have hc1_eq : c.1 = a.1 + t * (b.1 - a.1) := by linarith [ht1]
              have hc2_eq : c.2 = a.2 + t * (b.2 - a.2) := by linarith [ht2]
              show (|(b.1-p.1)*(c.2-p.2)-(b.2-p.2)*(c.1-p.1)| /
                   Real.sqrt ((b.1-p.1)^2+(b.2-p.2)^2))^2 =
                   (t-1)^2*C^2/((u₁-v₁)^2+(u₂-v₂)^2)
              rw [div_pow, sq_abs, Real.sq_sqrt (by positivity)]
              congr 1 <;> simp only [hC_def, hu₁, hu₂, hv₁, hv₂, hc1_eq, hc2_eq] <;> ring
            have hden_cpb : 0 < (u₁-v₁)^2+(u₂-v₂)^2 := by
              have : 0 ≤ (t-1)^2 * D := mul_nonneg (sq_nonneg _) (le_of_lt hD)
              linarith
            have hlt_sq_C3 : (pointLineDistance c p b)^2 < (pointLineDistance p a b)^2 := by
              rw [hpld_cpb_sq, hpld_sq]
              rw [div_lt_div_iff₀ hden_cpb hD]
              calc (t - 1) ^ 2 * C ^ 2 * D = C ^ 2 * ((t - 1) ^ 2 * D) := by ring
                _ < C ^ 2 * ((u₁ - v₁) ^ 2 + (u₂ - v₂) ^ 2) :=
                    mul_lt_mul_of_pos_left hkey_C3 hC2
            have hlt_C3 : pointLineDistance c p b < pointLineDistance p a b := by
              rw [← Real.sqrt_sq (pld_nonneg c p b), ← Real.sqrt_sq (le_of_lt hpld_pos)]
              exact Real.sqrt_lt_sqrt (sq_nonneg _) hlt_sq_C3
            linarith [hmin c hc p hp b hb hp_ne_b hncol_pcb]
          · -- Case C4: t > 1. Use pair (b, p, c).
            push_neg at ht_lt1
            have ht_gt1 : t > 1 := lt_of_le_of_ne ht_lt1 (Ne.symm ht_ne1)
            have hkey_C4 : (1-t)^2 * D < (t*u₁-v₁)^2+(t*u₂-v₂)^2 := by
              simp only [hD_def]
              nlinarith [sq_nonneg (u₁*v₂-u₂*v₁), hCS,
                         sq_nonneg ((1-t)*(u₁^2+u₂^2)+(u₁*(t*u₁-v₁)+u₂*(t*u₂-v₂)))]
            have hncol_pbc : ¬Collinear p c b := by
              apply not_collinear_of_cross
              have hc1_nc : c.1 = a.1 + t * (b.1 - a.1) := by linarith [ht1]
              have hc2_nc : c.2 = a.2 + t * (b.2 - a.2) := by linarith [ht2]
              have : (c.1-p.1)*(b.2-p.2)-(c.2-p.2)*(b.1-p.1) = (1-t)*C := by
                simp only [hC_def, hu₁, hu₂, hv₁, hv₂, hc1_nc, hc2_nc]; ring
              rw [this]
              exact mul_ne_zero (sub_ne_zero.mpr (by linarith)) hC
            have hp_ne_c : p ≠ c := by
              intro hpc; apply hpnot; rw [hpc]; exact ⟨t, ht1, ht2⟩
            have hpld_bpc_sq : (pointLineDistance b p c)^2 =
                (1-t)^2 * C^2 / ((t*u₁-v₁)^2+(t*u₂-v₂)^2) := by
              have hc1_eq : c.1 = a.1 + t * (b.1 - a.1) := by linarith [ht1]
              have hc2_eq : c.2 = a.2 + t * (b.2 - a.2) := by linarith [ht2]
              show (|(c.1-p.1)*(b.2-p.2)-(c.2-p.2)*(b.1-p.1)| /
                   Real.sqrt ((c.1-p.1)^2+(c.2-p.2)^2))^2 =
                   (1-t)^2*C^2/((t*u₁-v₁)^2+(t*u₂-v₂)^2)
              rw [div_pow, sq_abs, Real.sq_sqrt (by positivity)]
              congr 1 <;> simp only [hC_def, hu₁, hu₂, hv₁, hv₂, hc1_eq, hc2_eq] <;> ring
            have hden_bpc : 0 < (t*u₁-v₁)^2+(t*u₂-v₂)^2 := by
              have : 0 ≤ (1-t)^2 * D := mul_nonneg (sq_nonneg _) (le_of_lt hD)
              linarith
            have hlt_sq_C4 : (pointLineDistance b p c)^2 < (pointLineDistance p a b)^2 := by
              rw [hpld_bpc_sq, hpld_sq]
              rw [div_lt_div_iff₀ hden_bpc hD]
              calc (1 - t) ^ 2 * C ^ 2 * D = C ^ 2 * ((1 - t) ^ 2 * D) := by ring
                _ < C ^ 2 * ((t * u₁ - v₁) ^ 2 + (t * u₂ - v₂) ^ 2) :=
                    mul_lt_mul_of_pos_left hkey_C4 hC2
            have hlt_C4 : pointLineDistance b p c < pointLineDistance p a b := by
              rw [← Real.sqrt_sq (pld_nonneg b p c), ← Real.sqrt_sq (le_of_lt hpld_pos)]
              exact Real.sqrt_lt_sqrt (sq_nonneg _) hlt_sq_C4
            linarith [hmin b hb p hp c hc hp_ne_c hncol_pbc]

-- ============================================================
-- Part IV: The Main Theorem
-- ============================================================

/-- **The Sylvester-Gallai Theorem** (Kelly's proof, 1948):

    For any finite set of ≥ 3 points in ℝ², not all collinear,
    there exists a line through exactly 2 of the points.

    Proof (from Kelly's key lemma):
    1. Since S is not all-collinear but has ≥ 3 points, there
       exist lines through ≥ 2 points and non-incident points.
    2. Choose (p₀, ℓ₀) minimizing point-to-line distance.
    3. If ℓ₀ has ≥ 3 points, Kelly's lemma gives a contradiction.
    4. So ℓ₀ has exactly 2 points — it's an ordinary line. -/
theorem sylvester_gallai (S : Finset Point)
    (hcard : 3 ≤ S.card) (hnot : ¬AllCollinear S) :
    HasOrdinaryLine S := by
  -- Kelly's proof by contradiction via minimal distance pair
  by_contra hno
  -- Step 1: Every line through 2 points of S has ≥ 3 points of S on it
  -- (otherwise that line would be ordinary)
  rw [HasOrdinaryLine] at hno; push_neg at hno
  -- hno : ∀ a b, ¬IsOrdinaryLine S a b
  have hall3 : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∃ c ∈ S, c ≠ a ∧ c ≠ b ∧ Collinear a b c := by
    intro a haS b hbS hab
    have hni := hno a b
    simp only [IsOrdinaryLine] at hni
    push_neg at hni
    obtain ⟨c, hcS, hcol, hca, hcb⟩ := hni haS hbS hab
    exact ⟨c, hcS, hca, hcb, hcol⟩
  -- Step 2: Find initial non-collinear triple (p₀, a₀, b₀) with ¬Collinear a₀ b₀ p₀
  have ⟨a₀, ha₀S, b₀, hb₀S, hab₀, p₀, hp₀S, hnc₀⟩ :
      ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧ ∃ p ∈ S, ¬Collinear a b p := by
    rw [AllCollinear] at hnot; push_neg at hnot
    -- From S.card ≥ 3 > 1, get distinct a, b ∈ S
    have ⟨a, haS, b, hbS, hab⟩ : ∃ a ∈ S, ∃ b ∈ S, a ≠ b :=
      Finset.one_lt_card.mp (by omega)
    -- `push_neg` turns `¬AllCollinear` into
    -- `∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∃ c ∈ S, ¬Collinear a b c`; discharge `a ≠ b` with `hab`.
    obtain ⟨c, hcS, hnc⟩ := hnot a haS b hbS hab
    exact ⟨a, haS, b, hbS, hab, c, hcS, hnc⟩
  -- Step 3: Take the minimum-distance non-incident pair (p, a, b) in S³
  -- Use Classical decidability for the Finset filter
  classical
  let F : Finset (Point × Point × Point) :=
    (S ×ˢ (S ×ˢ S)).filter fun pab => pab.2.1 ≠ pab.2.2 ∧ ¬Collinear pab.2.1 pab.2.2 pab.1
  have hFne : F.Nonempty :=
    ⟨⟨p₀, a₀, b₀⟩, Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hp₀S, Finset.mem_product.mpr ⟨ha₀S, hb₀S⟩⟩, hab₀, hnc₀⟩⟩
  obtain ⟨⟨p, a, b⟩, hmem, hmin⟩ :=
    F.exists_min_image (fun pab => pointLineDistance pab.1 pab.2.1 pab.2.2) hFne
  simp only [F, Finset.mem_filter, Finset.mem_product] at hmem
  obtain ⟨⟨hpS, haS, hbS⟩, hab, hncp⟩ := hmem
  -- Step 4: Get third collinear point c on line(a, b) (since no ordinary line)
  obtain ⟨c, hcS, hca, hcb, hcol⟩ := hall3 a haS b hbS hab
  -- Step 5: Apply Kelly's lemma — contradiction with minimality
  apply kelly_distance_lemma p a b c S hpS haS hbS hcS hab (Ne.symm hca) (Ne.symm hcb)
    hcol hncp
  intro q hqS u huS v hvS huv hnquv
  have hmem_quv : (q, u, v) ∈ F :=
    Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr ⟨hqS, Finset.mem_product.mpr ⟨huS, hvS⟩⟩, huv, hnquv⟩
  exact hmin ⟨q, u, v⟩ hmem_quv

/-
## Summary

### Axioms (0)
All axioms eliminated. kelly_distance_lemma proved directly.

### Proved
- `collinear_self_left` - Collinearity is reflexive
- `collinear_comm` - Collinearity is symmetric in a sense
- `kelly_distance_lemma` - Kelly's geometric key lemma (6-case proof)
- `sylvester_gallai` - The main Sylvester-Gallai theorem

### Proof of kelly_distance_lemma
6-case analysis based on sign of foot parameter s = (u·v)/D:
- s ≤ 0: pair (a, p, b), condition D < (u₁-v₁)²+(u₂-v₂)²
- s ≥ 1: pair (b, p, a), condition D < v₁²+v₂²
- 0 < s < 1, t < 0: pair (a, p, c), condition t²D < (tu₁-v₁)²+(tu₂-v₂)²
- 0 < s < 1, 0 ≤ t < s: pair (c, p, a), condition t²D < v₁²+v₂²
- 0 < s < 1, s ≤ t < 1: pair (c, p, b), condition (t-1)²D < (u₁-v₁)²+(u₂-v₂)²
- 0 < s < 1, t > 1: pair (b, p, c), condition (1-t)²D < (tu₁-v₁)²+(tu₂-v₂)²
-/

#check @sylvester_gallai
#check @kelly_distance_lemma

end SylvesterGallai
