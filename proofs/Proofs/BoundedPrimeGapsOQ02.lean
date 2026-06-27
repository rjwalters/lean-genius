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
- [x] Canonical concrete discrepancy functional `Σ_{q ≤ x^θ} f(q,x)` with
      level-monotonicity *proved* (not assumed) — a generally nonzero model of the
      hierarchy, upgrading the `LevelMonotone` hypothesis to a theorem for the
      functional that actually arises in analytic number theory
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

/-! ## A canonical concrete discrepancy functional

The theorems above treat the discrepancy `D` abstractly, with `LevelMonotone` supplied
as a hypothesis.  Here we exhibit the **canonical shape** of the Elliott–Halberstam
sum — a sum of nonnegative per-modulus terms over the moduli `q ≤ x^θ` — and *prove*
that level-monotonicity, far from being an extra assumption, is an automatic property
of this functional.  This upgrades the hierarchy's structural hypothesis to a theorem
for the model that actually arises in analytic number theory, and supplies a generally
*nonzero* witness for the hierarchy (the zero-functional witness above is degenerate). -/

/-- The **canonical discrepancy functional**: the sum of nonnegative per-modulus
discrepancy weights `f q x` over all moduli `1 ≤ q ≤ x^θ`.  Instantiating
`f q x := max_{(a,q)=1} |ψ(x; q, a) − x/φ(q)|` recovers the genuine Elliott–Halberstam
sum; the structural lemmas below hold for any nonnegative weight `f`. -/
noncomputable def discrepancySum (f : ℕ → ℝ → ℝ) (θ x : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 ⌊x ^ θ⌋₊, f q x

/-- **Level-monotonicity of the canonical functional** on the analytically relevant
range `x ≥ 1`.  A larger level `θ₂` admits more moduli `q ≤ x^θ` (since `x ≥ 1` makes
`x ^ ·` monotone), and the extra terms are nonnegative, so the discrepancy sum can only
grow.  This is the structural fact that the abstract `LevelMonotone` hypothesis
abstracts — here proved outright. -/
theorem discrepancySum_mono_level (f : ℕ → ℝ → ℝ) (hf : ∀ q x, 0 ≤ f q x)
    {θ₁ θ₂ x : ℝ} (hx : 1 ≤ x) (hθ : θ₁ ≤ θ₂) :
    discrepancySum f θ₁ x ≤ discrepancySum f θ₂ x := by
  unfold discrepancySum
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun q _ _ => hf q x)
  exact Finset.Icc_subset_Icc_right
    (Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hx hθ))

/-- The **clamped** canonical functional, with base `max 1 x ≥ 1`.  On the entire
Elliott–Halberstam regime `x ≥ 1` it coincides with `discrepancySum f`, but the clamp
forces level-monotonicity to hold for *every* real `x`, so it is a model of the global
`LevelMonotone` predicate. -/
noncomputable def discrepancySumClamped (f : ℕ → ℝ → ℝ) (θ x : ℝ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 ⌊max 1 x ^ θ⌋₊, f q x

/-- On `x ≥ 1` the clamp is inert: the clamped functional equals the canonical one. -/
theorem discrepancySumClamped_eq (f : ℕ → ℝ → ℝ) {θ x : ℝ} (hx : 1 ≤ x) :
    discrepancySumClamped f θ x = discrepancySum f θ x := by
  unfold discrepancySumClamped discrepancySum
  rw [max_eq_right hx]

/-- **The clamped canonical functional is level-monotone** — for *every* `x`, with no
domain restriction.  Hence, for any nonnegative weight `f`, `discrepancySumClamped f`
is a (generally nonzero) model of `LevelMonotone`, so the level hierarchy
`EHAtLevel_of_le` applies to it non-vacuously. -/
theorem levelMonotone_discrepancySumClamped (f : ℕ → ℝ → ℝ) (hf : ∀ q x, 0 ≤ f q x) :
    LevelMonotone (discrepancySumClamped f) := by
  intro θ₁ θ₂ hθ x
  unfold discrepancySumClamped
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun q _ _ => hf q x)
  exact Finset.Icc_subset_Icc_right
    (Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le (le_max_left 1 x) hθ))

/-- **Capstone for the concrete model.**  For any nonnegative per-modulus weight `f`,
if the clamped canonical discrepancy functional satisfies the Elliott–Halberstam bound
at some level `θ₂`, then it satisfies it at every lower level `θ₁ ≤ θ₂`.  This is the
level hierarchy `EHAtLevel_of_le` instantiated at a genuine, generally nonzero model —
witnessing that the hierarchy is not an empty formalism. -/
theorem EHAtLevel_of_le_discrepancySumClamped (f : ℕ → ℝ → ℝ) (hf : ∀ q x, 0 ≤ f q x)
    {θ₁ θ₂ : ℝ} (h : θ₁ ≤ θ₂) (hEH : EHAtLevel (discrepancySumClamped f) θ₂) :
    EHAtLevel (discrepancySumClamped f) θ₁ :=
  EHAtLevel_of_le _ (levelMonotone_discrepancySumClamped f hf) h hEH

end BoundedPrimeGapsOQ02
