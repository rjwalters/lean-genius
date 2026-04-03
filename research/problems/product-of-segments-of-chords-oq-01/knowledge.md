# Knowledge Base: product-of-segments-of-chords-oq-01

**Problem**: Generalize the power of a point theorem to 3D spheres.
**Phase**: COMPLETED

---

## Problem Understanding

From Wiedijk #55 (product of segments of chords in 2D circles), OQ-01 asks:
> Does the invariance PA·PB = |d² - r²| hold for spheres in 3D?

**Answer: YES — and the proof works in any real inner product space (any dimension).**

---

## Session 2026-04-02 (Session 1) - Full Proof

**Mode**: FRESH
**Outcome**: COMPLETE — 0 sorries, answered OQ-01 affirmatively

### What I Did

1. Recognized the 2D algebraic proof is purely inner-product-based
2. Created `proofs/Proofs/ProductOfSegmentsOfChordsOQ01.lean` with:
   - `chord_quadratic_sphere`: The chord intersection quadratic t²+2t⟨P,dir⟩+(‖P‖²-r²)=0 holds in any IPS
   - `chord_roots_product_sphere`: Vieta product t₁·t₂ = ‖P‖²-r²
   - `chord_roots_opp_signs_sphere`: Interior P ⟹ t₁t₂ < 0
   - `sphere_power_invariant`: |t₁|·|t₂| = r²-‖P-O‖² in any InnerProductSpace ℝ E
   - `sphere_chord_products_equal`: Two chords through P give equal products (general)
   - `sphere3d_chord_products_equal`: Explicit 3D corollary with Sphere3D structure

### Key Findings

- **Dimension independence**: The chord quadratic uses only:
  - Inner product expansion: ⟨P+t·dir, P+t·dir⟩ = ‖P‖²+2t⟨P,dir⟩+t²‖dir‖²
  - Vieta's formula for monic quadratics
  - ‖v‖² = ⟨v,v⟩
  None of these depend on dimension.

- **Key Mathlib lemmas**:
  - `real_inner_self_eq_norm_mul_norm`: `⟪x,x⟫_ℝ = ‖x‖ * ‖x‖`
  - `inner_add_left`, `inner_add_right`, `inner_smul_left`, `inner_smul_right`
  - `real_inner_comm`: commutativity
  - `norm_smul`, `Real.norm_eq_abs`: for ‖s·dir‖ = |s| when ‖dir‖=1

- **3D distance formula**: For A = P + s·dir, ‖A-P‖ = |s|:
  ```lean
  rw [hA_eq, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hdir, mul_one]
  ```

### Files Modified

- Created: `proofs/Proofs/ProductOfSegmentsOfChordsOQ01.lean` (229 lines, 0 sorries)

---

## Insights

- The 2D power-of-a-point proof is a special case of an inner-product-space theorem
- Working in a general IPS is no harder than 2D; the API is essentially identical
- For a general proof, translate to Q = P-O, apply quadratic, use Vieta

## Dead Ends

- None; the approach worked immediately because the 2D proof already used inner-product algebra
