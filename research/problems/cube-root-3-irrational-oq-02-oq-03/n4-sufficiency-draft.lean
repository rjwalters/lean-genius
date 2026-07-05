/-
# DRAFT (UNVERIFIED): n = 4 sufficiency plumbing for the Vahlen–Capelli criterion

Session 2026-07-04 (researcher-6, s05). **Both verifiers were down this session**
(local Docker: containerd content-store I/O corruption, no Lean image buildable;
Aristotle MCP: "Resource not found" on every submission, 3rd session running). So the
proof below is written from careful reasoning but **NOT machine-checked**. It is a
ready-to-verify scaffold: the next session with a working verifier should (a) build this,
(b) fix any Mathlib API-name mismatches (flagged with `-- API?` comments), then (c) move
the two new theorems into `proofs/Proofs/CubeRoot3IrrationalOQ02OQ03.lean` and rewire the
`n = 4` branch of `vahlen_capelli` (see the bottom of this file).

This is intentionally OUTSIDE `proofs/Proofs/` so the lakefile glob does not build it and
the currently-compiling main file is not put at risk.

The two mathematical ingredients are already PROVED and Docker-verified on main:
  * `no_root_of_not_square_even` — linear-factor regime (a root ⟹ a is a square)
  * `capelli_four_coeff_contra` — the (2,2)-split coefficient contradiction
Only the polynomial glue below is new.
-/

import Mathlib.FieldTheory.KummerExtension
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

open Polynomial

namespace CubeRoot3IrrationalOQ02OQ03Draft

-- ------------------------------------------------------------------
-- Copies of the two PROVED helper lemmas (already on main), so this
-- draft is self-contained for verification.
-- ------------------------------------------------------------------

theorem no_root_of_not_square_even {K : Type*} [Field K] {n : ℕ} (hn : Even n)
    {a : K} (h1 : ∀ b : K, b ^ 2 ≠ a) (r : K) :
    (X ^ n - C a : K[X]).eval r ≠ 0 := by
  simp only [eval_sub, eval_pow, eval_X, eval_C]
  intro h
  obtain ⟨m, hm⟩ := hn
  have hrn : r ^ n = a := sub_eq_zero.mp h
  exact h1 (r ^ m) (by rw [← hrn, hm]; ring)

theorem capelli_four_coeff_contra {K : Type*} [Field K] {a p q s t : K}
    (h1 : p + s = 0) (h2 : q + t + p * s = 0) (h3 : p * t + q * s = 0)
    (h4 : q * t = -a)
    (hsq : ∀ b : K, b ^ 2 ≠ a) (hcap : ∀ b : K, a ≠ -(4 * b ^ 4)) : False := by
  have hs : s = -p := by linear_combination h1
  subst hs
  by_cases hp : p = 0
  · subst hp
    have ht : t = -q := by linear_combination h2
    subst ht
    have hqa : q ^ 2 = a := by linear_combination -h4
    exact hsq q hqa
  · have htq : t = q := by
      have hp3 : p * (t - q) = 0 := by linear_combination h3
      rcases mul_eq_zero.mp hp3 with h | h
      · exact absurd h hp
      · linear_combination h
    subst htq
    have hp2 : p ^ 2 = 2 * q := by linear_combination -h2
    have hq2 : q ^ 2 = -a := by linear_combination h4
    have h2ne : (2 : K) ≠ 0 := by
      intro h20
      apply hp
      have hpp : p ^ 2 = 0 := by rw [hp2, h20]; ring
      exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hpp
    obtain ⟨b, hb⟩ : ∃ b : K, p = 2 * b := ⟨p / 2, by field_simp⟩
    apply hcap b
    rw [hb] at hp2
    have hqb : q = 2 * b ^ 2 := by
      apply mul_left_cancel₀ h2ne
      linear_combination -hp2
    rw [hqb] at hq2
    linear_combination hq2

-- ------------------------------------------------------------------
-- NEW (this session): the polynomial plumbing.
-- ------------------------------------------------------------------

/-- **Bridge lemma.** If the monic quartic `X⁴ − C a` equals a product of two monic
quadratics `(X² + C p·X + C q)(X² + C s·X + C t)`, then the four coefficient relations
feeding `capelli_four_coeff_contra` hold.

Proof: expand the RHS (distributing `C` through `map_add`/`map_mul`, then `ring`) to
`X⁴ + C(p+s)·X³ + C(q+t+ps)·X² + C(pt+qs)·X + C(qt)`, and read off coefficients at
degrees 3,2,1,0. -/
theorem quartic_two_two_coeffs {K : Type*} [Field K] {a p q s t : K}
    (hfac : (X ^ 4 - C a : K[X]) =
      (X ^ 2 + C p * X + C q) * (X ^ 2 + C s * X + C t)) :
    p + s = 0 ∧ q + t + p * s = 0 ∧ p * t + q * s = 0 ∧ q * t = -a := by
  have hexp : (X ^ 2 + C p * X + C q) * (X ^ 2 + C s * X + C t)
      = X ^ 4 + C (p + s) * X ^ 3 + C (q + t + p * s) * X ^ 2
        + C (p * t + q * s) * X + C (q * t) := by
    simp only [map_add, map_mul]
    ring
  rw [hexp] at hfac
  -- Read off each coefficient. LHS: (X⁴ − C a).coeff k. RHS: the C(·)·X^k sum.
  have e3 := congrArg (fun r : K[X] => r.coeff 3) hfac
  have e2 := congrArg (fun r : K[X] => r.coeff 2) hfac
  have e1 := congrArg (fun r : K[X] => r.coeff 1) hfac
  have e0 := congrArg (fun r : K[X] => r.coeff 0) hfac
  simp only [coeff_add, coeff_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_C,
    coeff_ofNat, mul_ite, mul_one, mul_zero] at e3 e2 e1 e0
  -- After simp the `if`s on distinct literals collapse; `norm_num` finishes the arithmetic
  -- guards. Each eK becomes a scalar equation (LHS side is 0 for k=1,2,3 and −a for k=0).
  norm_num at e3 e2 e1 e0
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination e3      -- API? sign may need flipping to `-e3`
  · linear_combination e2      -- API?
  · linear_combination e1      -- API?
  · linear_combination e0      -- API?

/-- Over a field, a nonzero non-unit polynomial has positive `natDegree`. -/
theorem natDegree_pos_of_ne_zero_of_not_isUnit {K : Type*} [Field K] {u : K[X]}
    (hu0 : u ≠ 0) (huu : ¬ IsUnit u) : 0 < u.natDegree := by
  rcases Nat.eq_zero_or_pos u.natDegree with h0 | h0
  · exfalso
    obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp h0   -- hc : C c = u   -- API?
    have hcne : c ≠ 0 := by
      rintro rfl; rw [map_zero] at hc; exact hu0 hc.symm
    exact huu (hc ▸ isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcne))
  · exact h0

/-- A degree-1 factor of `X⁴ − C a` produces a root, contradicting the no-root lemma. -/
theorem no_linear_factor {K : Type*} [Field K] {a : K}
    (hsq : ∀ b : K, b ^ 2 ≠ a) {u v : K[X]}
    (huv : (X ^ 4 - C a : K[X]) = u * v) (hu1 : u.natDegree = 1) : False := by
  -- Explicit form of a degree-≤1 polynomial.
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu1
  have hform : u = C (u.coeff 1) * X + C (u.coeff 0) := by
    have : u.natDegree ≤ 1 := le_of_eq hu1
    exact Polynomial.eq_X_add_C_of_natDegree_le_one this   -- API? name/shape
  have hlead : u.coeff 1 ≠ 0 := by
    -- coeff at natDegree = leadingCoeff ≠ 0
    have := Polynomial.leadingCoeff_ne_zero.mpr hu0
    rwa [Polynomial.leadingCoeff, hu1] at this
  -- Root r = −(coeff 0)/(coeff 1).
  set r : K := -(u.coeff 0) / (u.coeff 1) with hr
  have hroot : u.eval r = 0 := by
    rw [hform]
    simp only [eval_add, eval_mul, eval_C, eval_X]
    field_simp [hr]
    ring
  have hfroot : (X ^ 4 - C a : K[X]).eval r = 0 := by
    rw [huv, eval_mul, hroot, zero_mul]
  exact no_root_of_not_square_even (by norm_num : Even 4) hsq r hfroot

/-- **n = 4 sufficiency (the genuine open target).** If `a` is not a square and
`a ∉ −4·K⁴`, then `X⁴ − C a` is irreducible over the field `K`. -/
theorem vahlen_capelli_four_suff {K : Type*} [Field K] {a : K}
    (hsq : ∀ b : K, b ^ 2 ≠ a) (hcap : ∀ b : K, a ≠ -(4 * b ^ 4)) :
    Irreducible (X ^ 4 - C a : K[X]) := by
  have hmon : (X ^ 4 - C a : K[X]).Monic := monic_X_pow_sub_C a (by norm_num)  -- API?
  have hdeg : (X ^ 4 - C a : K[X]).natDegree = 4 := natDegree_X_pow_sub_C
  have hne : (X ^ 4 - C a : K[X]) ≠ 0 := hmon.ne_zero
  refine ⟨?_, ?_⟩
  · -- not a unit (degree 4 > 0)
    intro hu
    have h0 := natDegree_eq_zero_of_isUnit hu
    rw [hdeg] at h0
    exact absurd h0 (by norm_num)
  · intro g h hgh
    by_contra hcon
    push_neg at hcon
    obtain ⟨hgu, hhu⟩ := hcon
    have hg0 : g ≠ 0 := by rintro rfl; rw [zero_mul] at hgh; exact hne hgh
    have hh0 : h ≠ 0 := by rintro rfl; rw [mul_zero] at hgh; exact hne hgh
    have dgpos := natDegree_pos_of_ne_zero_of_not_isUnit hg0 hgu
    have dhpos := natDegree_pos_of_ne_zero_of_not_isUnit hh0 hhu
    have hsum : g.natDegree + h.natDegree = 4 := by
      rw [← natDegree_mul hg0 hh0, ← hgh, hdeg]
    -- degrees are in {1,2,3} with sum 4
    have hg_le : g.natDegree ≤ 3 := by omega
    interval_cases hgd : g.natDegree
    · -- g linear (1,3): root of g ⟹ root of X⁴ − C a
      exact no_linear_factor hsq hgh hgd
    · -- g quadratic (2,2): h is also quadratic
      have hhd : h.natDegree = 2 := by omega
      -- normalise g,h to monic quadratics, then extract coefficients
      -- G := C (g.leadingCoeff)⁻¹ * g  is monic of degree 2, similarly H.
      -- Leading coeffs multiply to 1 (monic product), so C cg⁻¹ * C ch⁻¹ * (g*h) = g*h.
      set cg := g.leadingCoeff with hcg
      set ch := h.leadingCoeff with hch
      have hcg0 : cg ≠ 0 := leadingCoeff_ne_zero.mpr hg0
      have hch0 : ch ≠ 0 := leadingCoeff_ne_zero.mpr hh0
      have hlead1 : cg * ch = 1 := by
        have := hmon
        rw [Monic, hgh, leadingCoeff_mul] at this   -- API? Monic unfold + leadingCoeff_mul
        simpa [hcg, hch] using this
      set G : K[X] := C cg⁻¹ * g with hG
      set H : K[X] := C ch⁻¹ * h with hH
      have hGmon : G.Monic := by
        rw [hG]
        -- monic of C c * g when c * leadingCoeff g = 1
        sorry  -- API? use `Polynomial.monic_C_mul_...` / leadingCoeff computation
      have hHmon : H.Monic := by
        rw [hH]; sorry  -- API? symmetric
      have hGdeg : G.natDegree = 2 := by
        rw [hG, natDegree_C_mul (by simpa using inv_ne_zero hcg0)]; exact hgd  -- API? name
      have hHdeg : H.natDegree = 2 := by
        rw [hH, natDegree_C_mul (by simpa using inv_ne_zero hch0)]; exact hhd
      have hGH : (X ^ 4 - C a : K[X]) = G * H := by
        rw [hG, hH, hgh]
        rw [show C cg⁻¹ * g * (C ch⁻¹ * h) = C (cg⁻¹ * ch⁻¹) * (g * h) by ring, ← map_mul]
        have : cg⁻¹ * ch⁻¹ = 1 := by
          field_simp; linear_combination hlead1   -- API? cg⁻¹*ch⁻¹ = (cg*ch)⁻¹ = 1
        rw [this, map_one, one_mul]
      -- monic quadratic normal form: G = X² + C(G.coeff 1)·X + C(G.coeff 0)
      have hGform : G = X ^ 2 + C (G.coeff 1) * X + C (G.coeff 0) := by
        sorry  -- API? monic deg-2 normal form (via eq_X_pow_add_... or ext on coeffs)
      have hHform : H = X ^ 2 + C (H.coeff 1) * X + C (H.coeff 0) := by
        sorry  -- API? symmetric
      have hfacQ : (X ^ 4 - C a : K[X]) =
          (X ^ 2 + C (G.coeff 1) * X + C (G.coeff 0)) *
            (X ^ 2 + C (H.coeff 1) * X + C (H.coeff 0)) := by
        rw [hGH, hGform, hHform]
      obtain ⟨r1, r2, r3, r4⟩ := quartic_two_two_coeffs hfacQ
      exact capelli_four_coeff_contra r1 r2 r3 r4 hsq hcap
    · -- g cubic (3,1): h is linear; symmetric to the (1,3) case
      have hhd : h.natDegree = 1 := by omega
      exact no_linear_factor hsq (by rw [hgh, mul_comm]) hhd

end CubeRoot3IrrationalOQ02OQ03Draft

/-
# How this wires into the main file `CubeRoot3IrrationalOQ02OQ03.lean`

Add `quartic_two_two_coeffs` and `vahlen_capelli_four_suff` (and their helpers) after
`capelli_four_coeff_contra` in PART 5b, then replace the `n = 4` branch of `vahlen_capelli`
(currently a bare `sorry` inside `by_cases h2 : n = 2 → else`) with a nested split:

```
      · by_cases h4 : n = 4
        · subst h4
          exact vahlen_capelli_four_suff
            (hcond.1 2 Nat.prime_two (by norm_num))
            (hcond.2 (by norm_num))
        · sorry   -- even n ≥ 6 : still open (2-power tower + coprime multiplicativity)
```

Net effect once verified: the sole `sorry` shrinks from "even n ≥ 4" to "even n ≥ 6", and
`n = 4` (the first genuinely-new even case, where condition (2) is active in sufficiency)
becomes a complete, self-contained theorem over EVERY field — the first fragment of the
Mathlib TODO (KummerExtension.lean, Lang VI §9) discharged.

## Remaining verification risks (flagged `-- API?` / `sorry` above)
1. `quartic_two_two_coeffs`: exact simp normal form of the coeff equations; the four
   `linear_combination eK` finishers may need sign flips (`-eK`). HIGH confidence in the
   math, MEDIUM in the exact tactic incantation.
2. `Polynomial.eq_X_add_C_of_natDegree_le_one` — verify exact name/shape (degree vs
   natDegree variant).
3. `natDegree_pos_of_ne_zero_of_not_isUnit`: `Polynomial.natDegree_eq_zero` shape
   (`∃ x, C x = u` direction).
4. Monic normalisation block (two `sorry`s): the monic-of-`C c * g` lemma and the
   monic-degree-2 normal form `G = X² + C(G.coeff 1)X + C(G.coeff 0)`. These are the
   fiddliest; candidates: `Polynomial.Monic.def`, `leadingCoeff_C_mul`, and for the normal
   form either `ext` on `coeff` with `interval_cases` on the index, or subtract `X²` and
   apply the degree-≤1 form. This is the natural Aristotle delegation target.
5. `monic_X_pow_sub_C`, `natDegree_C_mul`, `leadingCoeff_mul` name/signature checks.
-/
