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
- [x] Exact additive decomposition across levels: `discrepancySum f θ₂ = discrepancySum f θ₁
      + discrepancyBand f θ₁ θ₂`, sharpening monotonicity from inequality to identity and
      localizing the inter-level growth to the band of new moduli `⌊x^θ₁⌋ < q ≤ ⌊x^θ₂⌋`
- [x] The EH-bound functional class at a fixed level is a **convex cone** (closed under
      addition `EHAtLevel_add` and nonnegative scaling `EHAtLevel_smul`)
- [x] Quantitative converse `EHAtLevel_discrepancySum_up`: EH at level `θ₁` plus an
      EH-type bound on the new-moduli band ⟹ EH at the higher level `θ₂` — pinning the
      band as exactly the extra analytic input needed to raise the level of distribution
- [x] Band cocycle (Chasles) identity `discrepancyBand_add_consecutive`: the new-moduli
      band subdivides at any intermediate level, `band θ₁ θ₃ = band θ₁ θ₂ + band θ₂ θ₃`,
      with `discrepancyBand_self` the empty-band base case — the moduli-range analogue of
      the level decomposition that licenses dyadic decomposition of the modulus range
- [x] Subdivided ascent `EHAtLevel_discrepancySum_up_split`: raising the level only needs
      EH-type bounds on each consecutive sub-band, recombined via the convex-cone closure
- [x] Finite-chain ascent `EHAtLevel_discrepancySum_up_chain` (and its genuine specialization
      `EHAtLevel_vonMangoldt_up_chain`): iterating the single-band ascent along an arbitrary
      monotone level chain `L 0 ≤ L 1 ≤ ⋯`, EH at the base plus an EH-type bound on every
      consecutive band lifts EH to every level `L n` — the arbitrarily-many-blocks form of
      dyadic decomposition of the modulus range (the `n = 2` case is the split lemma above)
- [x] Genuine von-Mangoldt instantiation: the concrete weight
      `vonMangoldtWeight q x = max_{(a,q)=1} |ψ(x;q,a) − x/φ(q)|` (built from Mathlib's
      `ArithmeticFunction.vonMangoldt` and `Nat.totient`) is *proved* nonnegative, so the
      entire hierarchy — level monotonicity, exact band decomposition, EH ⟹ BV, and dyadic
      ascent — specializes with no further hypotheses to the **actual** Elliott–Halberstam
      sum `vonMangoldtDiscrepancySum θ x = Σ_{q ≤ x^θ} max_{(a,q)=1} |ψ(x;q,a) − x/φ(q)|`
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

/-! ## Sharpening the hierarchy: the exact level increment

The monotonicity lemma `discrepancySum_mono_level` is an *inequality* — the sum can only
grow with the level.  Here we make it an *equality with explicit defect*: the gain in
passing from level `θ₁` to a higher level `θ₂` is exactly the discrepancy contributed by
the **band of new moduli** `⌊x^θ₁⌋ < q ≤ ⌊x^θ₂⌋` that the larger level admits.  This
localizes precisely where the growth between levels comes from, and turns the qualitative
hierarchy into a quantitative one. -/

/-- The **level-increment band**: the discrepancy contributed by the moduli
`⌊x^θ₁⌋ < q ≤ ⌊x^θ₂⌋` — exactly the new moduli that level `θ₂` admits over level `θ₁`. -/
noncomputable def discrepancyBand (f : ℕ → ℝ → ℝ) (θ₁ θ₂ x : ℝ) : ℝ :=
  ∑ q ∈ Finset.Ioc ⌊x ^ θ₁⌋₊ ⌊x ^ θ₂⌋₊, f q x

/-- **Exact additive decomposition of the discrepancy sum across levels.**  On the
analytic regime `x ≥ 1`, for `θ₁ ≤ θ₂`,
`discrepancySum f θ₂ x = discrepancySum f θ₁ x + discrepancyBand f θ₁ θ₂ x`.
The level-`θ₂` sum is the level-`θ₁` sum plus exactly the contribution of the new moduli
band — sharpening `discrepancySum_mono_level` from an inequality to an identity. -/
theorem discrepancySum_eq_add_band (f : ℕ → ℝ → ℝ) {θ₁ θ₂ x : ℝ}
    (hx : 1 ≤ x) (hθ : θ₁ ≤ θ₂) :
    discrepancySum f θ₂ x = discrepancySum f θ₁ x + discrepancyBand f θ₁ θ₂ x := by
  have hfloor : ⌊x ^ θ₁⌋₊ ≤ ⌊x ^ θ₂⌋₊ :=
    Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hx hθ)
  have hconv : ∀ m : ℕ, Finset.Icc 1 m = Finset.Ioc 0 m :=
    fun m => Finset.ext fun k => by simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  unfold discrepancySum discrepancyBand
  simp only [hconv]
  exact (Finset.sum_Ioc_consecutive (fun q => f q x) (Nat.zero_le _) hfloor).symm

/-- The level-increment band is nonnegative for a nonnegative weight `f`. -/
theorem discrepancyBand_nonneg (f : ℕ → ℝ → ℝ) (hf : ∀ q x, 0 ≤ f q x) (θ₁ θ₂ x : ℝ) :
    0 ≤ discrepancyBand f θ₁ θ₂ x :=
  Finset.sum_nonneg fun q _ => hf q x

/-- Monotonicity re-derived as a corollary of the exact decomposition: the level-`θ₂` sum
exceeds the level-`θ₁` sum by the nonnegative band contribution. -/
theorem discrepancySum_mono_level_of_band (f : ℕ → ℝ → ℝ) (hf : ∀ q x, 0 ≤ f q x)
    {θ₁ θ₂ x : ℝ} (hx : 1 ≤ x) (hθ : θ₁ ≤ θ₂) :
    discrepancySum f θ₁ x ≤ discrepancySum f θ₂ x := by
  rw [discrepancySum_eq_add_band f hx hθ]
  linarith [discrepancyBand_nonneg f hf θ₁ θ₂ x]

/-! ## The EH-bound class is a convex cone

For a fixed level `θ`, the functionals satisfying the Elliott–Halberstam bound are closed
under addition and nonnegative scaling — they form a convex cone.  This matters for the
analytic program: the genuine von-Mangoldt discrepancy is naturally decomposed into pieces
(major/minor arcs, dyadic ranges of moduli), and these closure lemmas say that bounding
each piece suffices to bound the whole. -/

/-- **Closed under addition.**  If `D₁` and `D₂` each satisfy the EH bound at level `θ`,
so does their sum, with constant `C₁ + C₂`. -/
theorem EHAtLevel_add {D₁ D₂ : ℝ → ℝ → ℝ} {θ : ℝ}
    (h₁ : EHAtLevel D₁ θ) (h₂ : EHAtLevel D₂ θ) :
    EHAtLevel (fun θ' x => D₁ θ' x + D₂ θ' x) θ := by
  intro A hA
  obtain ⟨C₁, hC₁, hb₁⟩ := h₁ A hA
  obtain ⟨C₂, hC₂, hb₂⟩ := h₂ A hA
  refine ⟨C₁ + C₂, by linarith, fun x hx => ?_⟩
  show D₁ θ x + D₂ θ x ≤ (C₁ + C₂) * x / (Real.log x) ^ A
  calc D₁ θ x + D₂ θ x
      ≤ C₁ * x / (Real.log x) ^ A + C₂ * x / (Real.log x) ^ A := by
        linarith [hb₁ x hx, hb₂ x hx]
    _ = (C₁ + C₂) * x / (Real.log x) ^ A := by ring

/-- **Closed under nonnegative scaling.**  If `D` satisfies the EH bound at level `θ` and
`0 ≤ c`, then `c · D` does too (the EH-bound class is a cone, not merely a subspace). -/
theorem EHAtLevel_smul {D : ℝ → ℝ → ℝ} {θ c : ℝ} (hc : 0 ≤ c)
    (hD : EHAtLevel D θ) : EHAtLevel (fun θ' x => c * D θ' x) θ := by
  intro A hA
  obtain ⟨C, hC, hb⟩ := hD A hA
  refine ⟨c * C + 1, by have := mul_nonneg hc hC.le; linarith, fun x hx => ?_⟩
  show c * D θ x ≤ (c * C + 1) * x / (Real.log x) ^ A
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hpow : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hlog A
  have hquot : 0 ≤ x / (Real.log x) ^ A := div_nonneg (by linarith) hpow.le
  have hsplit : (c * C + 1) * x / (Real.log x) ^ A
      = c * C * x / (Real.log x) ^ A + x / (Real.log x) ^ A := by ring
  calc c * D θ x
      ≤ c * (C * x / (Real.log x) ^ A) := mul_le_mul_of_nonneg_left (hb x hx) hc
    _ = c * C * x / (Real.log x) ^ A := by ring
    _ ≤ (c * C + 1) * x / (Real.log x) ^ A := by rw [hsplit]; linarith

/-- **Convex-cone closure.**  Any nonnegative linear combination of two functionals each
satisfying the EH bound at level `θ` again satisfies it — the defining property of a
convex cone.  Specializing `c₁ = c₂ = 1` recovers `EHAtLevel_add`; `c₂ = 0` recovers
`EHAtLevel_smul`. -/
theorem EHAtLevel_nonneg_linear {D₁ D₂ : ℝ → ℝ → ℝ} {θ c₁ c₂ : ℝ}
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (h₁ : EHAtLevel D₁ θ) (h₂ : EHAtLevel D₂ θ) :
    EHAtLevel (fun θ' x => c₁ * D₁ θ' x + c₂ * D₂ θ' x) θ :=
  EHAtLevel_add (EHAtLevel_smul hc₁ h₁) (EHAtLevel_smul hc₂ h₂)

/-- **Quantitative converse: raising the level.**  The hierarchy `EHAtLevel_of_le`
*descends* a bound (level `θ₂` ⟹ level `θ₁ ≤ θ₂`).  Here is the *ascent*: if the
discrepancy sum satisfies EH at level `θ₁` **and** the new-moduli band
`⌊x^θ₁⌋ < q ≤ ⌊x^θ₂⌋` independently satisfies an EH-type bound, then EH holds at the higher
level `θ₂`.  Combined with descent this pins the band down as *exactly* the extra analytic
input needed to raise the level — the structural reason EH beyond Bombieri–Vinogradov
(`θ = 1/2`) is hard: one must control the discrepancy over ever-larger ranges of moduli. -/
theorem EHAtLevel_discrepancySum_up (f : ℕ → ℝ → ℝ) {θ₁ θ₂ : ℝ} (hθ : θ₁ ≤ θ₂)
    (hlow : EHAtLevel (discrepancySum f) θ₁)
    (hband : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
        discrepancyBand f θ₁ θ₂ x ≤ C * x / (Real.log x) ^ A) :
    EHAtLevel (discrepancySum f) θ₂ := by
  intro A hA
  obtain ⟨C₁, hC₁, hb₁⟩ := hlow A hA
  obtain ⟨C₂, hC₂, hb₂⟩ := hband A hA
  refine ⟨C₁ + C₂, by linarith, fun x hx => ?_⟩
  rw [discrepancySum_eq_add_band f (by linarith) hθ]
  calc discrepancySum f θ₁ x + discrepancyBand f θ₁ θ₂ x
      ≤ C₁ * x / (Real.log x) ^ A + C₂ * x / (Real.log x) ^ A := by
        linarith [hb₁ x hx, hb₂ x hx]
    _ = (C₁ + C₂) * x / (Real.log x) ^ A := by ring

/-! ## Subdividing the level-increment band

The exact decomposition `discrepancySum_eq_add_band` localizes the inter-level growth to
the new-moduli band `⌊x^θ₁⌋ < q ≤ ⌊x^θ₂⌋`.  That band is itself additive: at any
intermediate level `θ₂` it splits into two consecutive sub-bands.  This is the additive
cocycle (Chasles) identity for the band — the moduli-range analogue of the level
decomposition — and it is exactly what licenses the *dyadic decomposition of the modulus
range* used in the analytic treatment of Elliott–Halberstam: control the discrepancy on
each dyadic block of moduli separately and recombine. -/

/-- The **empty band**: from a level to itself there are no new moduli, so the band
discrepancy vanishes. -/
theorem discrepancyBand_self (f : ℕ → ℝ → ℝ) (θ x : ℝ) :
    discrepancyBand f θ θ x = 0 := by
  unfold discrepancyBand
  rw [Finset.Ioc_self, Finset.sum_empty]

/-- **Cocycle / Chasles identity for the band.**  For `θ₁ ≤ θ₂ ≤ θ₃` on the analytic
regime `x ≥ 1`, the new-moduli band from level `θ₁` to `θ₃` is the disjoint union of the
`θ₁ → θ₂` and `θ₂ → θ₃` sub-bands, so its discrepancy is the sum of theirs:
`discrepancyBand f θ₁ θ₃ x = discrepancyBand f θ₁ θ₂ x + discrepancyBand f θ₂ θ₃ x`.
This subdivides the level increment at any intermediate level. -/
theorem discrepancyBand_add_consecutive (f : ℕ → ℝ → ℝ) {θ₁ θ₂ θ₃ x : ℝ}
    (hx : 1 ≤ x) (h₁₂ : θ₁ ≤ θ₂) (h₂₃ : θ₂ ≤ θ₃) :
    discrepancyBand f θ₁ θ₃ x
      = discrepancyBand f θ₁ θ₂ x + discrepancyBand f θ₂ θ₃ x := by
  have hf12 : ⌊x ^ θ₁⌋₊ ≤ ⌊x ^ θ₂⌋₊ :=
    Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hx h₁₂)
  have hf23 : ⌊x ^ θ₂⌋₊ ≤ ⌊x ^ θ₃⌋₊ :=
    Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hx h₂₃)
  unfold discrepancyBand
  exact (Finset.sum_Ioc_consecutive (fun q => f q x) hf12 hf23).symm

/-- **Subdivided ascent.**  Strengthening `EHAtLevel_discrepancySum_up`: to raise the
level of distribution from `θ₁` to `θ₃` it suffices to bound the discrepancy on each of
the two consecutive sub-bands `θ₁ → θ₂` and `θ₂ → θ₃` separately.  The band cocycle
identity splits the full `θ₁ → θ₃` band into these pieces, and the EH-bound class being a
convex cone (`EHAtLevel_add`) recombines the two sub-band bounds into one.  This is the
formal statement that the modulus range may be attacked dyadically — the standard
analytic strategy for Elliott–Halberstam. -/
theorem EHAtLevel_discrepancySum_up_split (f : ℕ → ℝ → ℝ) {θ₁ θ₂ θ₃ : ℝ}
    (h₁₂ : θ₁ ≤ θ₂) (h₂₃ : θ₂ ≤ θ₃)
    (hlow : EHAtLevel (discrepancySum f) θ₁)
    (hband₁ : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
        discrepancyBand f θ₁ θ₂ x ≤ C * x / (Real.log x) ^ A)
    (hband₂ : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
        discrepancyBand f θ₂ θ₃ x ≤ C * x / (Real.log x) ^ A) :
    EHAtLevel (discrepancySum f) θ₃ := by
  refine EHAtLevel_discrepancySum_up f (le_trans h₁₂ h₂₃) hlow ?_
  intro A hA
  obtain ⟨C₁, hC₁, hb₁⟩ := hband₁ A hA
  obtain ⟨C₂, hC₂, hb₂⟩ := hband₂ A hA
  refine ⟨C₁ + C₂, by linarith, fun x hx => ?_⟩
  rw [discrepancyBand_add_consecutive f (by linarith) h₁₂ h₂₃]
  calc discrepancyBand f θ₁ θ₂ x + discrepancyBand f θ₂ θ₃ x
      ≤ C₁ * x / (Real.log x) ^ A + C₂ * x / (Real.log x) ^ A := by
        linarith [hb₁ x hx, hb₂ x hx]
    _ = (C₁ + C₂) * x / (Real.log x) ^ A := by ring

/-! ## Finite dyadic chain: ascent over arbitrarily many sub-bands

`EHAtLevel_discrepancySum_up_split` raises the level of distribution across *two*
consecutive sub-bands.  But the genuine analytic dyadic decomposition splits the modulus
range `q ≤ x^θ` into `≍ log x` dyadic blocks, not two — so the two-band statement is only
the first nontrivial instance of the real strategy.  Here we iterate the single-band ascent
along an arbitrary finite increasing chain of levels `L 0 ≤ L 1 ≤ ⋯ ≤ L n`: an EH bound at
the base level together with an EH-type bound on every consecutive band raises the level of
distribution all the way to the top `L n`.  This is the full-strength formal statement that
Elliott–Halberstam may be attacked by dyadic decomposition of the modulus range into any
number of blocks. -/

/-- **Finite-chain ascent.**  For a monotone level sequence `L : ℕ → ℝ`, if the canonical
discrepancy sum satisfies the Elliott–Halberstam bound at the base level `L 0` and each
consecutive band `L k → L (k+1)` independently satisfies an EH-type bound, then EH holds at
*every* level `L n` of the chain.  The proof iterates `EHAtLevel_discrepancySum_up` along the
chain; `n = 1` is exactly the single-band ascent and the `n = 2` case recovers
`EHAtLevel_discrepancySum_up_split`.  This is the arbitrarily-many-blocks form of dyadic
decomposition. -/
theorem EHAtLevel_discrepancySum_up_chain (f : ℕ → ℝ → ℝ) {L : ℕ → ℝ}
    (hmono : Monotone L)
    (hlow : EHAtLevel (discrepancySum f) (L 0))
    (hband : ∀ k : ℕ, ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
        discrepancyBand f (L k) (L (k + 1)) x ≤ C * x / (Real.log x) ^ A) :
    ∀ n : ℕ, EHAtLevel (discrepancySum f) (L n) := by
  intro n
  induction n with
  | zero => exact hlow
  | succ k ih =>
      exact EHAtLevel_discrepancySum_up f (hmono (Nat.le_succ k)) ih (hband k)

/-- **Equally-spaced (arithmetic) chain ascent.**  The explicit instantiation of
`EHAtLevel_discrepancySum_up_chain` at the arithmetic level sequence `L k = θ₀ + k·δ`
(`δ ≥ 0`): from an EH bound at the base `θ₀` together with an EH-type bound on every equal
step `θ₀ + k·δ → θ₀ + (k+1)·δ`, EH holds at `θ₀ + n·δ` for all `n`.  This is the concrete,
equipartition form of the dyadic ascent — by taking `δ := (θ - θ₀)/n` it reaches any
prescribed target level `θ ≥ θ₀` in `n` equal blocks, with the abstract `Monotone L`
hypothesis discharged outright from `δ ≥ 0`. -/
theorem EHAtLevel_discrepancySum_up_arith (f : ℕ → ℝ → ℝ) {θ₀ δ : ℝ} (hδ : 0 ≤ δ)
    (hlow : EHAtLevel (discrepancySum f) θ₀)
    (hband : ∀ k : ℕ, ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
        discrepancyBand f (θ₀ + k * δ) (θ₀ + (k + 1) * δ) x ≤ C * x / (Real.log x) ^ A) :
    ∀ n : ℕ, EHAtLevel (discrepancySum f) (θ₀ + n * δ) := by
  have hmono : Monotone (fun k : ℕ => θ₀ + (k : ℝ) * δ) := by
    intro a b hab
    have hc : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    have := mul_le_mul_of_nonneg_right hc hδ
    simp only []
    linarith
  have hlow' : EHAtLevel (discrepancySum f) ((fun k : ℕ => θ₀ + (k : ℝ) * δ) 0) := by
    simpa using hlow
  refine EHAtLevel_discrepancySum_up_chain f hmono hlow' (fun k A hA => ?_)
  simpa only [Nat.cast_succ] using hband k A hA

/-! ## Grounding the hierarchy in the genuine von-Mangoldt discrepancy

Everything above treats the per-modulus weight `f` abstractly, requiring only
nonnegativity.  Here we instantiate `f` with the **genuine** Elliott–Halberstam weight

  `f q x = max_{(a,q)=1} |ψ(x; q, a) − x/φ(q)|`,   `ψ(x; q, a) = Σ_{n ≤ x, n ≡ a (q)} Λ(n)`,

built from Mathlib's von-Mangoldt function `ArithmeticFunction.vonMangoldt` and Euler
totient `Nat.totient`.  The maximum of absolute values is automatically nonnegative, so
the single structural hypothesis the whole framework needs is discharged outright — and
the level hierarchy, the exact band decomposition, the convex-cone closure and the dyadic
ascent all specialize, with no further work, to the *actual* Elliott–Halberstam sum.  This
converts the abstract skeleton into statements about the genuine object of the conjecture. -/

open scoped ArithmeticFunction in
/-- The **Chebyshev ψ in an arithmetic progression** at a real cutoff `x`:
`ψ(x; q, a) = Σ_{1 ≤ n ≤ ⌊x⌋, n ≡ a (q)} Λ(n)`, with `Λ` the von-Mangoldt function. -/
noncomputable def psiAP (q a : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n => n % q = a % q),
    ArithmeticFunction.vonMangoldt n

/-- The **per-residue discrepancy** `|ψ(x; q, a) − x/φ(q)|` of the progression `a mod q`
against its expected main term `x/φ(q)`.  Nonnegative by construction (an absolute value). -/
noncomputable def apDiscrepancy (q a : ℕ) (x : ℝ) : ℝ :=
  |psiAP q a x - x / (Nat.totient q : ℝ)|

/-- The **genuine Elliott–Halberstam per-modulus weight**: the worst-case discrepancy
`max_{(a,q)=1} |ψ(x; q, a) − x/φ(q)|` over residues `a` coprime to `q` (and `0` for the
degenerate empty range `q = 0`).  This is exactly the summand of the real EH sum. -/
noncomputable def vonMangoldtWeight (q : ℕ) (x : ℝ) : ℝ :=
  if h : ((Finset.range q).filter (fun a => Nat.Coprime a q)).Nonempty then
    ((Finset.range q).filter (fun a => Nat.Coprime a q)).sup' h
      (fun a => apDiscrepancy q a x)
  else 0

/-- The genuine weight is nonnegative — the sole structural hypothesis the abstract
hierarchy requires — because it is a maximum (or `0`) of absolute values. -/
theorem vonMangoldtWeight_nonneg (q : ℕ) (x : ℝ) : 0 ≤ vonMangoldtWeight q x := by
  unfold vonMangoldtWeight
  split
  · next h =>
    obtain ⟨a, ha⟩ := h
    have h0 : 0 ≤ apDiscrepancy q a x := abs_nonneg _
    exact le_trans h0 (Finset.le_sup' (fun a => apDiscrepancy q a x) ha)
  · exact le_refl 0

/-- The **genuine Elliott–Halberstam discrepancy sum** at level `θ`:
`Σ_{q ≤ x^θ} max_{(a,q)=1} |ψ(x; q, a) − x/φ(q)|`, the object whose `≪_A x/(log x)^A`
bound *is* the level-of-distribution statement. -/
noncomputable def vonMangoldtDiscrepancySum (θ x : ℝ) : ℝ :=
  discrepancySum vonMangoldtWeight θ x

/-- The clamped genuine sum (base `max 1 x`), level-monotone for *every* real `x`. -/
noncomputable def vonMangoldtDiscrepancySumClamped (θ x : ℝ) : ℝ :=
  discrepancySumClamped vonMangoldtWeight θ x

/-- On the analytic regime `x ≥ 1` the clamp is inert. -/
theorem vonMangoldtDiscrepancySumClamped_eq {θ x : ℝ} (hx : 1 ≤ x) :
    vonMangoldtDiscrepancySumClamped θ x = vonMangoldtDiscrepancySum θ x :=
  discrepancySumClamped_eq vonMangoldtWeight hx

/-- **The genuine EH sum is level-monotone on `x ≥ 1`** — proved, not assumed.  Larger
levels admit more moduli `q ≤ x^θ`, and each new worst-case discrepancy is nonnegative. -/
theorem vonMangoldtDiscrepancySum_mono_level {θ₁ θ₂ x : ℝ} (hx : 1 ≤ x) (hθ : θ₁ ≤ θ₂) :
    vonMangoldtDiscrepancySum θ₁ x ≤ vonMangoldtDiscrepancySum θ₂ x :=
  discrepancySum_mono_level vonMangoldtWeight vonMangoldtWeight_nonneg hx hθ

/-- The clamped genuine functional is globally level-monotone, hence a genuine (generally
nonzero) model of `LevelMonotone` to which the level hierarchy `EHAtLevel_of_le` applies. -/
theorem levelMonotone_vonMangoldtDiscrepancySumClamped :
    LevelMonotone vonMangoldtDiscrepancySumClamped :=
  levelMonotone_discrepancySumClamped vonMangoldtWeight vonMangoldtWeight_nonneg

/-- **The level hierarchy for the genuine EH sum.**  If the real von-Mangoldt discrepancy
sum satisfies the Elliott–Halberstam bound at some level `θ₂`, it satisfies it at every
lower level `θ₁ ≤ θ₂`.  This is `EHAtLevel_of_le` at the actual object of the conjecture. -/
theorem EHAtLevel_of_le_vonMangoldt {θ₁ θ₂ : ℝ} (h : θ₁ ≤ θ₂)
    (hEH : EHAtLevel vonMangoldtDiscrepancySumClamped θ₂) :
    EHAtLevel vonMangoldtDiscrepancySumClamped θ₁ :=
  EHAtLevel_of_le _ levelMonotone_vonMangoldtDiscrepancySumClamped h hEH

/-- **Elliott–Halberstam ⟹ Bombieri–Vinogradov, for the genuine functional.**  The full
conjecture for the real von-Mangoldt discrepancy sum implies its proved `θ = 1/2` case. -/
theorem bombieriVinogradov_of_EH_vonMangoldt
    (hEH : ElliottHalberstam vonMangoldtDiscrepancySumClamped) :
    BombieriVinogradov vonMangoldtDiscrepancySumClamped :=
  bombieriVinogradov_of_elliottHalberstam _ hEH

/-- For the genuine functional, the EH bound at **any** level `θ ≥ 1/2` already yields
Bombieri–Vinogradov, via the hierarchy. -/
theorem bombieriVinogradov_of_EHAtLevel_vonMangoldt {θ : ℝ} (hθ : 1 / 2 ≤ θ)
    (hEH : EHAtLevel vonMangoldtDiscrepancySumClamped θ) :
    BombieriVinogradov vonMangoldtDiscrepancySumClamped :=
  bombieriVinogradov_of_EHAtLevel _ levelMonotone_vonMangoldtDiscrepancySumClamped hθ hEH

/-- **Exact level increment for the genuine sum.**  On `x ≥ 1`, the real EH sum at level
`θ₂` is its level-`θ₁` value plus exactly the worst-case discrepancy of the new moduli
`⌊x^θ₁⌋ < q ≤ ⌊x^θ₂⌋` — the genuine instance of `discrepancySum_eq_add_band`. -/
theorem vonMangoldtDiscrepancySum_eq_add_band {θ₁ θ₂ x : ℝ} (hx : 1 ≤ x) (hθ : θ₁ ≤ θ₂) :
    vonMangoldtDiscrepancySum θ₂ x
      = vonMangoldtDiscrepancySum θ₁ x + discrepancyBand vonMangoldtWeight θ₁ θ₂ x :=
  discrepancySum_eq_add_band vonMangoldtWeight hx hθ

/-- **Dyadic ascent for the genuine sum.**  To raise the genuine level of distribution
from `θ₁` to `θ₃` it suffices to bound the real worst-case discrepancy on each consecutive
sub-band of moduli `θ₁ → θ₂` and `θ₂ → θ₃` — the formal license for the dyadic attack on
Elliott–Halberstam, now stated for the actual von-Mangoldt weight. -/
theorem EHAtLevel_vonMangoldt_up_split {θ₁ θ₂ θ₃ : ℝ} (h₁₂ : θ₁ ≤ θ₂) (h₂₃ : θ₂ ≤ θ₃)
    (hlow : EHAtLevel vonMangoldtDiscrepancySum θ₁)
    (hband₁ : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
        discrepancyBand vonMangoldtWeight θ₁ θ₂ x ≤ C * x / (Real.log x) ^ A)
    (hband₂ : ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
        discrepancyBand vonMangoldtWeight θ₂ θ₃ x ≤ C * x / (Real.log x) ^ A) :
    EHAtLevel vonMangoldtDiscrepancySum θ₃ :=
  EHAtLevel_discrepancySum_up_split vonMangoldtWeight h₁₂ h₂₃ hlow hband₁ hband₂

/-- **Finite dyadic chain for the genuine sum.**  To raise the genuine level of
distribution from the base of a monotone level chain `L` all the way to any level `L n`, it
suffices to bound the real worst-case von-Mangoldt discrepancy on each consecutive sub-band
`L k → L (k+1)`.  This is `EHAtLevel_discrepancySum_up_chain` specialized to the actual
Elliott–Halberstam weight — the arbitrarily-many-blocks dyadic attack on the genuine
object, of which `EHAtLevel_vonMangoldt_up_split` is the two-block case. -/
theorem EHAtLevel_vonMangoldt_up_chain {L : ℕ → ℝ} (hmono : Monotone L)
    (hlow : EHAtLevel vonMangoldtDiscrepancySum (L 0))
    (hband : ∀ k : ℕ, ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
        discrepancyBand vonMangoldtWeight (L k) (L (k + 1)) x ≤ C * x / (Real.log x) ^ A) :
    ∀ n : ℕ, EHAtLevel vonMangoldtDiscrepancySum (L n) :=
  EHAtLevel_discrepancySum_up_chain vonMangoldtWeight hmono hlow hband

/-- **Equally-spaced chain ascent for the genuine sum.**  The explicit arithmetic
instantiation `L k = θ₀ + k·δ` (`δ ≥ 0`) of `EHAtLevel_vonMangoldt_up_chain`: bounding the
real worst-case von-Mangoldt discrepancy on each equal step `θ₀ + k·δ → θ₀ + (k+1)·δ`
raises the genuine level of distribution to `θ₀ + n·δ` for every `n`.  With `δ := (θ-θ₀)/n`
this is the formal license to reach any target level `θ ≥ θ₀` in `n` equal modulus blocks —
the equipartition form of the dyadic attack on Elliott–Halberstam, for the actual
von-Mangoldt weight. -/
theorem EHAtLevel_vonMangoldt_up_arith {θ₀ δ : ℝ} (hδ : 0 ≤ δ)
    (hlow : EHAtLevel vonMangoldtDiscrepancySum θ₀)
    (hband : ∀ k : ℕ, ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
        discrepancyBand vonMangoldtWeight (θ₀ + k * δ) (θ₀ + (k + 1) * δ) x
          ≤ C * x / (Real.log x) ^ A) :
    ∀ n : ℕ, EHAtLevel vonMangoldtDiscrepancySum (θ₀ + n * δ) :=
  EHAtLevel_discrepancySum_up_arith vonMangoldtWeight hδ hlow hband

end BoundedPrimeGapsOQ02
