/-
# Pick's Theorem OQ-02: GCD Boundary Formula for Lattice Points on a Segment

Open Question from picks-theorem-oq-01 (triangulation approach to Pick's theorem):
"Can the GCD boundary formula (lattice points on a segment = gcd(Δx, Δy) + 1)
be formalized and used to give a constructive boundary count for Pick's theorem?"

## The GCD Boundary Formula

For a line segment from (0, 0) to (a, b) with a, b : ℕ, the number of integer
lattice points on the segment (including both endpoints) is exactly:

  gcd(a, b) + 1

The points are {(k·(a/g), k·(b/g)) : k = 0, 1, ..., g} where g = gcd(a,b).

## Why This Matters

Pick's theorem: A = I + B/2 - 1 (area = interior points + boundary/2 - 1).
The boundary count B = Σ gcd(|Δxᵢ|, |Δyᵢ|) over edges, since each edge from
(x₁,y₁) to (x₂,y₂) contributes gcd(|Δx|,|Δy|) non-endpoint interior boundary
points, and the total over all edges with shared endpoints gives B = Σ gcd values.

## Status: Verified (0 axioms, 0 sorries)
-/

import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Tactic

namespace PicksTheoremOQ02

open Nat Finset

/-
══════════════════════════════════════════════════════════════
PART I: DEFINITIONS
══════════════════════════════════════════════════════════════ -/

/-- A natural lattice point (x,y) lies on the segment from (0,0) to (a,b)
    when collinear (x·b = y·a) and within bounds (x ≤ a and y ≤ b). -/
def onSegment (a b x y : ℕ) : Prop :=
  x * b = y * a ∧ x ≤ a ∧ y ≤ b

/-- The lattice points on segment (0,0)→(a,b): parameterized by k ∈ {0,...,g}
    where g = gcd(a,b), mapping k to the k-th point (k·(a/g), k·(b/g)). -/
def segmentPoints (a b : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (Nat.gcd a b + 1)).image (fun k => (k * (a / Nat.gcd a b), k * (b / Nat.gcd a b)))

/-
══════════════════════════════════════════════════════════════
PART II: THE PARAMETERIZATION IS CORRECT
══════════════════════════════════════════════════════════════ -/

/-- Each parameterized point (k·(a/g), k·(b/g)) lies on the segment from (0,0) to (a,b). -/
theorem segmentPoint_on_segment (a b k : ℕ) (hk : k ≤ Nat.gcd a b) :
    onSegment a b (k * (a / Nat.gcd a b)) (k * (b / Nat.gcd a b)) := by
  have ha : Nat.gcd a b * (a / Nat.gcd a b) = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have hb : Nat.gcd a b * (b / Nat.gcd a b) = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  refine ⟨?_, ?_, ?_⟩
  · -- Collinearity: both sides equal k · (a/g) · (b/g) · g
    calc k * (a / Nat.gcd a b) * b
        = k * (a / Nat.gcd a b) * (Nat.gcd a b * (b / Nat.gcd a b)) := by rw [hb]
      _ = k * (b / Nat.gcd a b) * (Nat.gcd a b * (a / Nat.gcd a b)) := by ring
      _ = k * (b / Nat.gcd a b) * a := by rw [ha]
  · -- x ≤ a: k·(a/g) ≤ g·(a/g) = a
    calc k * (a / Nat.gcd a b) ≤ Nat.gcd a b * (a / Nat.gcd a b) :=
            Nat.mul_le_mul_right _ hk
      _ = a := ha
  · -- y ≤ b similarly
    calc k * (b / Nat.gcd a b) ≤ Nat.gcd a b * (b / Nat.gcd a b) :=
            Nat.mul_le_mul_right _ hk
      _ = b := hb

/-- All elements of segmentPoints lie on the segment. -/
theorem mem_segmentPoints_on_segment {a b : ℕ} {p : ℕ × ℕ} (h : p ∈ segmentPoints a b) :
    onSegment a b p.1 p.2 := by
  simp only [segmentPoints, Finset.mem_image, Finset.mem_range] at h
  obtain ⟨k, hk, rfl⟩ := h
  exact segmentPoint_on_segment a b k (Nat.lt_succ_iff.mp hk)

/-
══════════════════════════════════════════════════════════════
PART III: INJECTIVITY OF THE PARAMETRIZATION
══════════════════════════════════════════════════════════════ -/

/-- The map k ↦ (k·(a/g), k·(b/g)) is injective when gcd(a,b) > 0.
    At least one of a/g or b/g is nonzero, forcing k₁ = k₂. -/
theorem segmentMap_injective (a b : ℕ) (hg : 0 < Nat.gcd a b) :
    Function.Injective (fun k : ℕ => (k * (a / Nat.gcd a b), k * (b / Nat.gcd a b))) := by
  intro k₁ k₂ heq
  simp only [Prod.mk.injEq] at heq
  rcases Nat.eq_zero_or_pos (a / Nat.gcd a b) with hap | hap
  · -- a/g = 0: then a = 0, so gcd(0,b) = b, and b/b = 1
    have ha : a = 0 := by
      have h := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
      rw [hap, mul_zero] at h; exact h.symm
    rw [ha, Nat.gcd_zero_left] at heq hg
    simp only [Nat.zero_div, mul_zero, true_and] at heq
    rw [Nat.div_self hg, mul_one] at heq
    exact heq
  · -- a/g > 0: use first component
    exact Nat.eq_of_mul_eq_mul_right hap heq.1

/-
══════════════════════════════════════════════════════════════
PART IV: MAIN THEOREM — GCD BOUNDARY FORMULA
══════════════════════════════════════════════════════════════ -/

/-- **GCD Boundary Formula**: The segment from (0,0) to (a,b) has exactly
    gcd(a,b) + 1 integer lattice points. -/
theorem card_segmentPoints (a b : ℕ) : (segmentPoints a b).card = Nat.gcd a b + 1 := by
  unfold segmentPoints
  rcases Nat.eq_zero_or_pos (Nat.gcd a b) with hg | hg
  · -- gcd = 0 iff a = b = 0: the segment is a single point (0,0)
    rw [hg, zero_add, Finset.range_one, Finset.image_singleton]
    obtain ⟨rfl, rfl⟩ := Nat.gcd_eq_zero_iff.mp hg
    simp
  · -- gcd > 0: the parameterization is injective so image has gcd+1 elements
    rw [Finset.card_image_of_injective _ (segmentMap_injective a b hg), Finset.card_range]

/-
══════════════════════════════════════════════════════════════
PART V: COMPLETENESS
══════════════════════════════════════════════════════════════ -/

/-- **Completeness**: Every lattice point on the segment from (0,0) to (a,b)
    is parameterized by some k ∈ {0,...,gcd(a,b)}.

    Key step: from x·b = y·a with a = g·p, b = g·q (gcd(p,q)=1),
    coprimality gives p | x, so x = k·p and y = k·q for some k ≤ g. -/
theorem onSegment_mem_segmentPoints {a b x y : ℕ} (h : onSegment a b x y) :
    (x, y) ∈ segmentPoints a b := by
  simp only [segmentPoints, Finset.mem_image, Finset.mem_range]
  obtain ⟨hcol, hxa, hyb⟩ := h
  rcases Nat.eq_zero_or_pos (Nat.gcd a b) with hg0 | hg
  · -- gcd = 0: a = b = 0, so x = y = 0
    obtain ⟨rfl, rfl⟩ := Nat.gcd_eq_zero_iff.mp hg0
    exact ⟨0, by norm_num, Nat.le_zero.mp hxa, Nat.le_zero.mp hyb⟩
  · -- gcd > 0: split on whether a = 0
    set g := Nat.gcd a b
    rcases Nat.eq_zero_or_pos a with ha | ha
    · -- a = 0: g = b, and x ≤ 0, so x = 0; use k = y
      rw [ha, Nat.gcd_zero_left] at *
      have hx0 : x = 0 := Nat.le_zero.mp hxa
      refine ⟨y, by omega, ?_, ?_⟩
      · rw [ha, Nat.gcd_zero_left, Nat.zero_div, mul_zero]; exact hx0.symm
      · simp [Nat.div_self hg]
    · -- a > 0: use coprimality to find k with x = k·(a/g)
      set p := a / g
      set q := b / g
      have hgp : g * p = a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
      have hgq : g * q = b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
      have hcop : Nat.Coprime p q := Nat.coprime_div_gcd_div_gcd hg
      have hp : 0 < p := Nat.div_pos (Nat.le_of_dvd ha (Nat.gcd_dvd_left a b)) hg
      -- From x·b = y·a, derive x·q = y·p (cancel the factor g)
      have heq : x * q = y * p := by
        have h2 : g * (x * q) = g * (y * p) := by
          calc g * (x * q) = x * (g * q) := by ring
            _ = y * (g * p) := by rw [hgq, hgp]; exact hcol
            _ = g * (y * p) := by ring
        exact Nat.eq_of_mul_eq_mul_left hg h2
      -- p | x·q and gcd(p,q)=1, so by coprimality p | x
      -- (p coprime to q, which is the right factor in x*q, so p | x)
      have hpdvdx : p ∣ x :=
        hcop.dvd_of_dvd_mul_right ⟨y, heq.trans (mul_comm y p)⟩
      -- Write x = k·p; then y = k·q from x·q = y·p
      obtain ⟨k, hkp⟩ := hpdvdx
      have hkq : k * q = y := by
        apply Nat.eq_of_mul_eq_mul_right hp
        calc k * q * p = k * p * q := by ring
          _ = x * q := by rw [← hkp]
          _ = y * p := heq
      -- k ≤ g from k·p = x ≤ a = g·p
      have hkg : k ≤ g := by
        have hkp_le : k * p ≤ g * p :=
          calc k * p = x := hkp.symm
            _ ≤ a := hxa
            _ = g * p := hgp.symm
        exact Nat.le_of_mul_le_mul_right hkp_le hp
      exact ⟨k, by omega, by rw [hkp], by rw [hkq]⟩

/-
══════════════════════════════════════════════════════════════
PART VI: MEMBERSHIP CHARACTERIZATION
══════════════════════════════════════════════════════════════ -/

/-- (x,y) is a lattice point on segment (0,0)→(a,b) iff it is in segmentPoints(a,b). -/
theorem onSegment_iff_mem {a b x y : ℕ} :
    onSegment a b x y ↔ (x, y) ∈ segmentPoints a b :=
  ⟨onSegment_mem_segmentPoints,
   fun hmem => by
     simp only [segmentPoints, Finset.mem_image, Finset.mem_range] at hmem
     obtain ⟨k, hk, rfl, rfl⟩ := hmem
     exact segmentPoint_on_segment a b k (Nat.lt_succ_iff.mp hk)⟩

/-
══════════════════════════════════════════════════════════════
PART VII: SPECIAL CASES
══════════════════════════════════════════════════════════════ -/

/-- For coprime a and b, only the two endpoints are lattice points on the segment. -/
theorem segment_coprime {a b : ℕ} (hab : Nat.Coprime a b) :
    (segmentPoints a b).card = 2 := by
  rw [card_segmentPoints, hab]

/-- The diagonal segment (0,0)→(a,a) has a+1 lattice points: (0,0),(1,1),...,(a,a). -/
theorem segment_diagonal (a : ℕ) : (segmentPoints a a).card = a + 1 := by
  rw [card_segmentPoints, Nat.gcd_self]

/-- Concrete: segment to (4,6) has gcd(4,6)+1 = 3 lattice points. -/
theorem segment_4_6 : (segmentPoints 4 6).card = 3 := by
  have h : Nat.gcd 4 6 = 2 := by native_decide
  rw [card_segmentPoints, h]

/-- Concrete: segment to (3,5) has gcd(3,5)+1 = 2 lattice points (just endpoints). -/
theorem segment_3_5 : (segmentPoints 3 5).card = 2 := by
  have h : Nat.gcd 3 5 = 1 := by native_decide
  rw [card_segmentPoints, h]

/-- Concrete: segment to (6,9) has gcd(6,9)+1 = 4 lattice points. -/
theorem segment_6_9 : (segmentPoints 6 9).card = 4 := by
  have h : Nat.gcd 6 9 = 3 := by native_decide
  rw [card_segmentPoints, h]

/-
══════════════════════════════════════════════════════════════
PART VIII: PICK'S BOUNDARY FORMULA
══════════════════════════════════════════════════════════════ -/

/-- **Pick's edge contribution**: each edge contributes gcd(|Δx|,|Δy|) to Pick's
    boundary count B = Σ gcd values.  The count equals card(segmentPoints) - 1
    (one endpoint is shared with the next edge in the polygon). -/
theorem pick_edge_contribution (a b : ℕ) :
    (segmentPoints a b).card - 1 = Nat.gcd a b := by
  rw [card_segmentPoints]; omega

/-- Interior segment lattice points (excluding both endpoints) number gcd(a,b) - 1. -/
theorem interior_segment_count (a b : ℕ) (h : 0 < Nat.gcd a b) :
    (segmentPoints a b).card - 2 = Nat.gcd a b - 1 := by
  rw [card_segmentPoints]; omega

end PicksTheoremOQ02
