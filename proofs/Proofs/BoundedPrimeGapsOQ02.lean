/-
# Bounded Prime Gaps — Open Question 02:
# The Elliott–Halberstam Conjecture, formalized axiom-free as a level-of-distribution hierarchy

Source: Elliott–Halberstam (1968); Bombieri (1965), A. I. Vinogradov (1965)

## The conjecture

For a modulus `q` and residue `a` coprime to `q`, write the prime-counting
discrepancy in the arithmetic progression `a mod q` as

  `ψ(x; q, a) − x/φ(q)`,   where `ψ(x; q, a) = Σ_{n ≤ x, n ≡ a (q)} Λ(n)`.

The **level-of-distribution** statement at level `θ ∈ (0, 1)` asserts that, summing
the worst-case discrepancy over all moduli `q ≤ x^θ`,

  `Σ_{q ≤ x^θ} max_{(a,q)=1} |ψ(x; q, a) − x/φ(q)|  ≪_A  x / (log x)^A`   for every `A > 0`.

The **Bombieri–Vinogradov theorem** proves this *unconditionally* at level `θ = 1/2`.
The **Elliott–Halberstam conjecture** asserts it at *every* level `θ < 1`.  This is
open; it is the analytic input that sharpens the Maynard–Tao bounded-gap bound (e.g.
`H ≤ 12` under EH versus `H ≤ 246` unconditionally).

## What this file formalizes — axiom-free

EH itself is unproved, so we do **not** axiomatize it.  Instead we formalize the
*logical skeleton* of the conjecture and its hierarchy, with **zero axioms**:

* `EHAtLevel D θ` — the Elliott–Halberstam bound at level `θ` for an abstract
  discrepancy functional `D θ x` (modelling the sum above up to modulus `x^θ`).
* `EHAtLevel_of_le` — **the level hierarchy**: for a level-monotone functional, the
  bound at a higher level implies the bound at every lower level (more moduli ⇒
  larger discrepancy sum, so the same constant works).
* `BombieriVinogradov D := EHAtLevel D (1/2)` and `ElliottHalberstam D` (all levels
  `θ < 1`), with `bombieriVinogradov_of_elliottHalberstam` — **EH ⟹ BV**.
* Monotonicity of the bound in the functional, and a non-vacuity witness.

The discrepancy functional `D` and its structural properties (nonnegativity,
monotonicity in the level) are taken as hypotheses, so every theorem here is a
purely logical/analytic consequence — provable without assuming the conjecture and
without any `axiom`, `sorry`, or `native_decide`.  Instantiating `D` with the genuine
von-Mangoldt discrepancy sum (and discharging Bombieri–Vinogradov) is the analytic
work documented in the sibling `BoundedPrimeGapsOQ04`.

## Status
- [x] EH statement + level hierarchy + EH ⟹ BV — 0 sorries, 0 axioms
- [x] No `axiom`, no `sorry`, no `native_decide`
-/

import Mathlib

namespace BoundedPrimeGapsOQ02

open Real

/- A **discrepancy functional** `D θ x` models the level-`θ` Elliott–Halberstam sum
`Σ_{q ≤ x^θ} max_{(a,q)=1} |ψ(x; q, a) − x/φ(q)|` at the point `x`.  We keep it
abstract: the theorems below depend only on its structural properties, supplied as
hypotheses. -/

/-- **The Elliott–Halberstam bound at level `θ`** for a discrepancy functional `D`:
for every exponent `A > 0` there is a constant `C > 0` with

  `D θ x ≤ C · x / (log x)^A`   for all `x ≥ 2`.

This is the level-of-distribution statement; `θ = 1/2` is Bombieri–Vinogradov
(proved), and `θ < 1` for all admissible `θ` is the Elliott–Halberstam conjecture. -/
def EHAtLevel (D : ℝ → ℝ → ℝ) (θ : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
    D θ x ≤ C * x / (Real.log x) ^ A

/-- A discrepancy functional is **level-monotone** if a larger level `θ` yields a
larger (or equal) discrepancy sum — summing over more moduli `q ≤ x^θ` can only
increase the total.  This is the structural fact behind the EH hierarchy. -/
def LevelMonotone (D : ℝ → ℝ → ℝ) : Prop :=
  ∀ ⦃θ₁ θ₂ : ℝ⦄, θ₁ ≤ θ₂ → ∀ x : ℝ, D θ₁ x ≤ D θ₂ x

/-- **The level hierarchy.** For a level-monotone functional, the Elliott–Halberstam
bound at a higher level `θ₂` implies the bound at every lower level `θ₁ ≤ θ₂`: the
constant `C` from level `θ₂` works verbatim, since `D θ₁ x ≤ D θ₂ x ≤ C·x/(log x)^A`. -/
theorem EHAtLevel_of_le (D : ℝ → ℝ → ℝ) (hD : LevelMonotone D) {θ₁ θ₂ : ℝ}
    (h : θ₁ ≤ θ₂) (hEH : EHAtLevel D θ₂) : EHAtLevel D θ₁ := by
  intro A hA
  obtain ⟨C, hC, hbound⟩ := hEH A hA
  exact ⟨C, hC, fun x hx => le_trans (hD h x) (hbound x hx)⟩

/-- **Monotone in the functional.** If `D'` is pointwise below `D` at level `θ` and
`D` satisfies the EH bound there, then so does `D'`. -/
theorem EHAtLevel_of_le_functional (D D' : ℝ → ℝ → ℝ) {θ : ℝ}
    (hle : ∀ x, D' θ x ≤ D θ x) (hEH : EHAtLevel D θ) : EHAtLevel D' θ := by
  intro A hA
  obtain ⟨C, hC, hbound⟩ := hEH A hA
  exact ⟨C, hC, fun x hx => le_trans (hle x) (hbound x hx)⟩

/-- **Bombieri–Vinogradov** is the Elliott–Halberstam bound at level `θ = 1/2`
(proved unconditionally; see `BoundedPrimeGapsOQ04`). -/
def BombieriVinogradov (D : ℝ → ℝ → ℝ) : Prop := EHAtLevel D (1 / 2)

/-- **The Elliott–Halberstam conjecture** for the functional `D`: the level bound
holds at every admissible level `0 < θ < 1`. -/
def ElliottHalberstam (D : ℝ → ℝ → ℝ) : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → EHAtLevel D θ

/-- The conjecture gives the bound at any single admissible level. -/
theorem eHAtLevel_of_elliottHalberstam (D : ℝ → ℝ → ℝ) (hEH : ElliottHalberstam D)
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) : EHAtLevel D θ :=
  hEH θ hθ hθ1

/-- **Elliott–Halberstam ⟹ Bombieri–Vinogradov.** The full conjecture implies its
`θ = 1/2` special case. -/
theorem bombieriVinogradov_of_elliottHalberstam (D : ℝ → ℝ → ℝ)
    (hEH : ElliottHalberstam D) : BombieriVinogradov D :=
  hEH (1 / 2) (by norm_num) (by norm_num)

/-- For a level-monotone functional, the EH bound at **any** level `θ ≥ 1/2` already
implies Bombieri–Vinogradov, via the hierarchy. -/
theorem bombieriVinogradov_of_EHAtLevel (D : ℝ → ℝ → ℝ) (hD : LevelMonotone D)
    {θ : ℝ} (hθ : 1 / 2 ≤ θ) (hEH : EHAtLevel D θ) : BombieriVinogradov D :=
  EHAtLevel_of_le D hD hθ hEH

/-- For a level-monotone functional, the EH bound transfers across any two levels in
the conjectural range: a bound at `θ₂` gives one at every `θ₁ ≤ θ₂`.  In particular
the conjecture is equivalent to its restriction to levels approaching `1`. -/
theorem elliottHalberstam_iff_levels_near_one (D : ℝ → ℝ → ℝ) (hD : LevelMonotone D) :
    ElliottHalberstam D ↔ ∀ θ : ℝ, 1 / 2 ≤ θ → θ < 1 → EHAtLevel D θ := by
  constructor
  · intro hEH θ hθ hθ1
    exact hEH θ (by linarith) hθ1
  · intro h θ hθ hθ1
    rcases le_or_gt (1 / 2) θ with hle | hlt
    · exact h θ hle hθ1
    · -- θ < 1/2: descend from the level 1/2 bound (which `h` provides)
      exact EHAtLevel_of_le D hD (le_of_lt hlt) (h (1 / 2) (le_refl _) (by norm_num))

/-- **Non-vacuity.** The zero functional satisfies the Elliott–Halberstam bound at
every level (with `C = 1`), so `EHAtLevel` is a satisfiable predicate, not vacuously
empty. -/
theorem EHAtLevel_zero (θ : ℝ) : EHAtLevel (fun _ _ => (0 : ℝ)) θ := by
  intro A _hA
  refine ⟨1, one_pos, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hp : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hlx A
  -- goal is `(fun _ _ => 0) θ x ≤ 1 * x / (log x)^A`; the LHS is defeq to `0`
  exact div_nonneg (by linarith) hp.le

/-- The zero functional is level-monotone (trivially), so it is a model of the full
hierarchy. -/
theorem levelMonotone_zero : LevelMonotone (fun _ _ => (0 : ℝ)) :=
  fun _ _ _ _ => le_refl 0

/-- The zero functional satisfies the full Elliott–Halberstam conjecture — a concrete
witness that the conjunction `ElliottHalberstam ∧ LevelMonotone` is consistent. -/
theorem elliottHalberstam_zero : ElliottHalberstam (fun _ _ => (0 : ℝ)) :=
  fun θ _ _ => EHAtLevel_zero θ

end BoundedPrimeGapsOQ02
