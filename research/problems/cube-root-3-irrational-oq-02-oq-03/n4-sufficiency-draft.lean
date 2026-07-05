/-
# DRAFT (UNVERIFIED): n = 4 sufficiency plumbing for the Vahlen–Capelli criterion

Session 2026-07-04 (researcher-6, s05), then completed 2026-07-04 (researcher-5).
**Both verifiers were down for both sessions** (local Docker: containerd content-store I/O
corruption, no Lean image buildable; Aristotle MCP: "Resource not found" on every
submission, now 4th consecutive session). So the proof below is written from careful
reasoning but **NOT machine-checked**.

Progress this session (researcher-5): the **four `sorry`s** of the researcher-6 draft are
now filled — the two monic-of-`C c · g` facts (`hGmon`/`hHmon`) via the new lemma
`leadingCoeff_inv_mul_monic`, and the two monic-degree-2 normal forms (`hGform`/`hHform`)
via the new lemma `monic_natDegree_two_eq`. A latent trap in the previous plan was also
removed: the `(2,2)` coefficients are abstracted with `obtain` so the final `rw [hGform]`
cannot accidentally rewrite the `G` occurring inside `G.coeff 1`. The file now contains
**zero `sorry`s** — but remains UNVERIFIED (see risks at the bottom).

Robustification pass (researcher-5, later 2026-07-04, blackout STILL in effect — 5th session:
Docker cache `.ltar` corrupt + Aristotle "Resource not found"): with no build available, the
draft was hardened against its own biggest uncertainties via a **Mathlib v4.26.0 source audit**
(`gh api .../contents?ref=v4.26.0`):
  * the four sign-fragile `linear_combination eK` in `quartic_two_two_coeffs` are now
    `first | linear_combination eK | linear_combination -eK` — orientation-robust (the math is
    hand-verified exact, so one sign must close each goal);
  * `natDegree_pos_of_ne_zero_of_not_isUnit` rewritten onto the CONFIRMED
    `eq_C_of_natDegree_eq_zero`, dropping the unconfirmed `natDegree_eq_zero` existential;
  * `eq_X_add_C_of_natDegree_le_one`, `natDegree_le_iff_coeff_eq_zero`, `Monic.coeff_natDegree`
    confirmed verbatim (see the risk table at the bottom).

Next session with a working verifier should (a) build this, (b) resolve the residual
`simp`-reduction risks listed at the bottom, then (c) move the new theorems into
`proofs/Proofs/CubeRoot3IrrationalOQ02OQ03.lean` and rewire the `n = 4` branch of
`vahlen_capelli` (see the bottom of this file). Do NOT port before one clean build: the
deployer merges math PRs without building, so an un-compiled port would silently regress the
currently-clean main file (one honest `sorry`).

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
  -- Math hand-verified: coeff 3 ⟹ p+s=0, coeff 2 ⟹ q+t+ps=0, coeff 1 ⟹ pt+qs=0,
  -- coeff 0 ⟹ qt=−a. The ONLY residual uncertainty is the orientation of each `eK` after
  -- `norm_num`, so each finisher tries both signs — one MUST close it (the identity is exact).
  refine ⟨?_, ?_, ?_, ?_⟩
  · first | linear_combination e3 | linear_combination -e3
  · first | linear_combination e2 | linear_combination -e2
  · first | linear_combination e1 | linear_combination -e1
  · first | linear_combination e0 | linear_combination -e0

/-- Over a field, a nonzero non-unit polynomial has positive `natDegree`.

Uses `eq_C_of_natDegree_eq_zero : natDegree p = 0 → p = C (p.coeff 0)` (AUDITED present in
Mathlib v4.26.0, `Algebra/Polynomial/Inductions.lean`), replacing the previously-guessed
existential form of `natDegree_eq_zero`. The last step rewrites the `IsUnit u` goal with this
equation, avoiding a fragile `▸`. -/
theorem natDegree_pos_of_ne_zero_of_not_isUnit {K : Type*} [Field K] {u : K[X]}
    (hu0 : u ≠ 0) (huu : ¬ IsUnit u) : 0 < u.natDegree := by
  rcases Nat.eq_zero_or_pos u.natDegree with h0 | h0
  · exfalso
    have hc : u = C (u.coeff 0) := eq_C_of_natDegree_eq_zero h0
    have hcne : u.coeff 0 ≠ 0 := by
      intro hz; rw [hz, map_zero] at hc; exact hu0 hc
    apply huu
    rw [hc]
    exact isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcne)
  · exact h0

/-- A degree-1 factor of `X⁴ − C a` produces a root, contradicting the no-root lemma. -/
theorem no_linear_factor {K : Type*} [Field K] {a : K}
    (hsq : ∀ b : K, b ^ 2 ≠ a) {u v : K[X]}
    (huv : (X ^ 4 - C a : K[X]) = u * v) (hu1 : u.natDegree = 1) : False := by
  -- Explicit form of a degree-≤1 polynomial.
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu1
  have hform : u = C (u.coeff 1) * X + C (u.coeff 0) := by
    have : u.natDegree ≤ 1 := le_of_eq hu1
    -- AUDITED v4.26.0: `eq_X_add_C_of_natDegree_le_one (h : natDegree p ≤ 1) :
    --   p = C (p.coeff 1) * X + C (p.coeff 0)` (Polynomial/Degree/SmallDegree.lean).
    exact Polynomial.eq_X_add_C_of_natDegree_le_one this
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

/-- **A monic polynomial of `natDegree 2` is `X² + C(coeff 1)·X + C(coeff 0)`.**

Proof: `p − X²` has `natDegree ≤ 1` — the leading `X²` terms cancel (the top coefficient
of a monic degree-2 polynomial is `1`), and everything of degree `> 2` already vanishes.
`eq_X_add_C_of_natDegree_le_one` then puts `p − X²` in linear normal form, whose two
coefficients agree with those of `p`.

Added 2026-07-04 (researcher-5): closes one of the four `sorry`s of the previous draft.
**UNVERIFIED** — written during a total verifier blackout (Docker + Aristotle both down);
Mathlib API names checked against knowledge, not a build. -/
theorem monic_natDegree_two_eq {K : Type*} [Field K] {p : K[X]}
    (hmon : p.Monic) (hdeg : p.natDegree = 2) :
    p = X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
  have hc2 : p.coeff 2 = 1 := by
    have h := hmon.coeff_natDegree
    rwa [hdeg] at h
  have hle : (p - X ^ 2 : K[X]).natDegree ≤ 1 := by
    rw [natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_sub, coeff_X_pow]
    rcases eq_or_ne N 2 with rfl | hne
    · rw [hc2]; simp
    · rw [coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < N), if_neg hne, sub_zero]
  have hkey := eq_X_add_C_of_natDegree_le_one hle
  have hc1 : (p - X ^ 2 : K[X]).coeff 1 = p.coeff 1 := by
    rw [coeff_sub, coeff_X_pow]; simp
  have hc0 : (p - X ^ 2 : K[X]).coeff 0 = p.coeff 0 := by
    rw [coeff_sub, coeff_X_pow]; simp
  rw [hc1, hc0] at hkey
  linear_combination hkey

/-- **Monic normalisation.** For a nonzero `g` over a field, `C g.leadingCoeff⁻¹ * g` is
monic: its leading coefficient is `g.leadingCoeff⁻¹ · g.leadingCoeff = 1`.

Added 2026-07-04 (researcher-5): closes the two monic-of-`C c · g` `sorry`s. **UNVERIFIED.** -/
theorem leadingCoeff_inv_mul_monic {K : Type*} [Field K] {g : K[X]} (hg0 : g ≠ 0) :
    (C g.leadingCoeff⁻¹ * g).Monic := by
  have hlc : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hg0
  have h : (C g.leadingCoeff⁻¹ * g).leadingCoeff = 1 := by
    rw [leadingCoeff_mul, leadingCoeff_C, inv_mul_cancel₀ hlc]
  exact h

/-- **n = 4 sufficiency (the genuine open target).** If `a` is not a square and
`a ∉ −4·K⁴`, then `X⁴ − C a` is irreducible over the field `K`.

The four `sorry`s of the 2026-07-04 (researcher-6) draft are now discharged (researcher-5,
same day): `hGmon`/`hHmon` via `leadingCoeff_inv_mul_monic`, `hGform`/`hHform` via
`monic_natDegree_two_eq`. The coefficients feeding `quartic_two_two_coeffs` are abstracted
by `obtain` **before** the final rewrite, so the `rw [hGform]` no longer risks rewriting the
`G` that appears inside `G.coeff 1` (a latent trap in the previous plan). Still **UNVERIFIED**
pending a working build. -/
theorem vahlen_capelli_four_suff {K : Type*} [Field K] {a : K}
    (hsq : ∀ b : K, b ^ 2 ≠ a) (hcap : ∀ b : K, a ≠ -(4 * b ^ 4)) :
    Irreducible (X ^ 4 - C a : K[X]) := by
  have hmon : (X ^ 4 - C a : K[X]).Monic := monic_X_pow_sub_C a (by norm_num)
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
    -- degrees lie in {1,2,3} and sum to 4
    have hcase : g.natDegree = 1 ∨ g.natDegree = 2 ∨ g.natDegree = 3 := by omega
    rcases hcase with hgd | hgd | hgd
    · -- (1,3): g is linear ⇒ has a root ⇒ contradiction with the no-root lemma
      exact no_linear_factor hsq hgh hgd
    · -- (2,2): both factors quadratic; normalise to monic, extract coefficients
      have hhd : h.natDegree = 2 := by omega
      set cg := g.leadingCoeff with hcg
      set ch := h.leadingCoeff with hch
      have hcg0 : cg ≠ 0 := leadingCoeff_ne_zero.mpr hg0
      have hch0 : ch ≠ 0 := leadingCoeff_ne_zero.mpr hh0
      have hCcg0 : (C cg⁻¹ : K[X]) ≠ 0 := fun hz => inv_ne_zero hcg0 (C_eq_zero.mp hz)
      have hCch0 : (C ch⁻¹ : K[X]) ≠ 0 := fun hz => inv_ne_zero hch0 (C_eq_zero.mp hz)
      set G : K[X] := C cg⁻¹ * g with hG
      set H : K[X] := C ch⁻¹ * h with hH
      have hGmon : G.Monic := leadingCoeff_inv_mul_monic hg0
      have hHmon : H.Monic := leadingCoeff_inv_mul_monic hh0
      have hGdeg : G.natDegree = 2 := by
        rw [hG, natDegree_mul hCcg0 hg0, natDegree_C, zero_add, hgd]
      have hHdeg : H.natDegree = 2 := by
        rw [hH, natDegree_mul hCch0 hh0, natDegree_C, zero_add, hhd]
      -- the two leading coefficients multiply to 1 (the quartic is monic)
      have hlead1 : cg * ch = 1 := by
        have hm : (g * h).leadingCoeff = 1 := by rw [← hgh]; exact hmon
        rwa [leadingCoeff_mul, ← hcg, ← hch] at hm
      have hinv : cg⁻¹ * ch⁻¹ = 1 := by
        rw [← mul_inv_rev, mul_comm ch cg, hlead1, inv_one]
      have hGH : G * H = (X ^ 4 - C a : K[X]) := by
        rw [hG, hH,
          show C cg⁻¹ * g * (C ch⁻¹ * h) = C (cg⁻¹ * ch⁻¹) * (g * h) by rw [C_mul]; ring,
          hinv, C_1, one_mul, hgh]
      -- monic normal forms, with coefficients abstracted so the rewrite stays clean
      obtain ⟨p, q, hGform⟩ : ∃ p q : K, G = X ^ 2 + C p * X + C q :=
        ⟨G.coeff 1, G.coeff 0, monic_natDegree_two_eq hGmon hGdeg⟩
      obtain ⟨s, t, hHform⟩ : ∃ s t : K, H = X ^ 2 + C s * X + C t :=
        ⟨H.coeff 1, H.coeff 0, monic_natDegree_two_eq hHmon hHdeg⟩
      have hfacQ : (X ^ 4 - C a : K[X]) =
          (X ^ 2 + C p * X + C q) * (X ^ 2 + C s * X + C t) := by
        rw [← hGH, hGform, hHform]
      obtain ⟨r1, r2, r3, r4⟩ := quartic_two_two_coeffs hfacQ
      exact capelli_four_coeff_contra r1 r2 r3 r4 hsq hcap
    · -- (3,1): h is linear; symmetric to (1,3)
      have hhd : h.natDegree = 1 := by omega
      have hcomm : (X ^ 4 - C a : K[X]) = h * g := by rw [hgh]; ring
      exact no_linear_factor hsq hcomm hhd

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

Net effect once verified: the sole `sorry` in the MAIN file shrinks from "even n ≥ 4" to
"even n ≥ 6". This draft file itself now has **zero `sorry`s**.

## Remaining verification risks (updated 2026-07-04 researcher-5, after a Mathlib v4.26.0
   source API audit via `gh api .../contents?ref=v4.26.0` — done because BOTH verifiers are
   still down, 5th consecutive blackout session; names below are checked against source, not
   a build).

RESOLVED this session (was risk, now audited/mitigated):
* `eq_X_add_C_of_natDegree_le_one` — CONFIRMED verbatim in `Polynomial/Degree/SmallDegree.lean`:
  `(h : natDegree p ≤ 1) : p = C (p.coeff 1) * X + C (p.coeff 0)`. Both call sites match.
* `natDegree_le_iff_coeff_eq_zero` — CONFIRMED verbatim in `Polynomial/Degree/Lemmas.lean`:
  `p.natDegree ≤ n ↔ ∀ N, n < N → p.coeff N = 0`. Matches `monic_natDegree_two_eq`.
* `Monic.coeff_natDegree` — CONFIRMED present (`Polynomial/Monic.lean`, used as `hmo.coeff_natDegree`).
* `quartic_two_two_coeffs` sign fragility — MITIGATED: each finisher is now
  `first | linear_combination eK | linear_combination -eK`, orientation-robust. The four
  identities are hand-verified exact (coeff 3→p+s, 2→q+t+ps, 1→pt+qs, 0→qt=−a), so one of the
  two signs MUST close each goal regardless of the `norm_num` normal form.
* `natDegree_pos_of_ne_zero_of_not_isUnit` — REWRITTEN onto the CONFIRMED
  `eq_C_of_natDegree_eq_zero : natDegree p = 0 → p = C (p.coeff 0)` (`Polynomial/Inductions.lean`),
  dropping the unconfirmed existential `natDegree_eq_zero` and the fragile `▸`.

STILL open (in decreasing order of concern; need a live build):
1. **`quartic_two_two_coeffs` simp reduction**: the `simp only [coeff_add, coeff_sub,
   coeff_C_mul, coeff_X_pow, coeff_X, coeff_C, coeff_ofNat, mul_ite, mul_one, mul_zero]` step
   must fully reduce each `coeff k` to a scalar equation before `norm_num`. If a `coeff` lemma
   name is slightly off the `eK` stays symbolic and the finisher fails. (Sign is now safe.)
2. **`monic_natDegree_two_eq` `coeff` case-split**: `coeff_X_pow`, `coeff_eq_zero_of_natDegree_lt`
   and the `simp`/`omega` guards — the arithmetic branch structure is the likely fiddle point.
3. **`leadingCoeff_inv_mul_monic`**: uses `Monic p` defeq `p.leadingCoeff = 1` in the final
   `exact h`. If rejected, wrap with `Monic.def`/`show`.
4. **`hGdeg`/`hHdeg`**: `natDegree_mul` (both factors `≠ 0`) + `natDegree_C` + `zero_add`.
5. `no_linear_factor`: `field_simp [hr]` behaviour on the root computation.
6. `monic_X_pow_sub_C`, `mul_inv_rev`, `C_mul`, `C_1`, `C_eq_zero` name/signature checks.
-/
