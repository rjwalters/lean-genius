# Navier-Stokes Regularity Proof - Version History

This document tracks the evolution of our analysis of the Navier-Stokes regularity proof.

---

## v5 - OpenAI Forced Blowup + Enstrophy Erratum (2026-09-08)

**Status:** CONDITIONAL (Step 3 withdrawn); external result recorded

**Summary:** OpenAI announced a Lean-certified finite-time blowup for 3D Navier-Stokes with
a smooth, compactly supported force and zero initial velocity, for every ν > 0, on ℝ³ and 𝕋³,
with bounded kinetic energy — Clay alternatives (C)/(D). The unforced alternatives (A)/(B)
remain open. We evaluated the construction against our enstrophy framework.

### Key Findings

1. **Dictionary** (τ = T*−t, 0 < h < 1/100): Ω ≍ τ^{−1−h} (α = 1+h, barely Type II),
   E ≍ τ^{−1/2−3h}, P ≍ S ≍ τ^{−3/2−3h}, R_diff ≍ τ^{1/2+h/2}, core radius ℓ_r ≍ τ^{1/2},
   ℓ_r/R_diff = Re_θ^{1/2} → ∞, β = S/(ΩE) ≍ τ^{h} = (T−t)^{α−1} → 0.
2. **NSAxioms test:** four of five fields hold (theta_bound exactly saturated); only
   `spectral_gap` (νP ≥ cΩE — bounded local Reynolds number at the diffusion scale) fails.
   "Eventual stability" S ≤ νP never arrives because νP/(ΩE) decays at the same rate as β.
3. **Forcing is invisible in the enstrophy budget:** |∫ω·curl f| ≲ E^{1/2} ≪ E′. Scalar
   enstrophy inequalities cannot distinguish forced from unforced; f = 0 must enter through
   the momentum equation.
4. **ERRATUM:** v3 read dE/dt ≤ CE³ as an upper bound E ≲ τ^{−1/2}. It is Leray's lower
   bound E ≥ cτ^{−1/2}. Step 3 of the conditional theorem (B′ ⇒ Type I) is withdrawn; the
   OpenAI flow satisfies B′ and is Type II.
5. **Not a stability result**, not peer reviewed, statement alignment under human review,
   credit disputed (Córdoba–Martínez-Zoroa, Alpöge–Buckmaster). Recorded, not adjudicated.

### Files

- `analysis/openai-forced-blowup-2026.md` - Main analysis (new)
- `analysis/conditional-regularity-theorem.md` - Erratum header, Step 3 withdrawn
- `analysis/enstrophy-type-ii-exclusion.md` - Erratum header, marked refuted
- `papers/INDEX.md` - OpenAI paper + lineage added
- `meta.json`, `annotations.source.json` - v5 status, NSAxioms annotation corrected

---

## v3 - Conditional Regularity Theorem (2025-12-22, Session 6)

**Status:** CONDITIONAL THEOREM FORMULATED

**Summary:** Identified that anti-escape is the missing heart of the problem.
Formulated a clean conditional theorem with honest attribution of proven vs.
assumed components. CKN + enstrophy ODE cannot give θ ≥ c without anti-escape.

### Key Findings

1. **The Scale Mismatch Problem**
   - Barker-Prange smoothing lemma works at parabolic scale √(T*-t)
   - For Type I: diffusion scale R_diff ≈ √(T*-t) (scales match)
   - For Type II: R_diff << √(T*-t) (scales don't match)
   - Smoothing lemma cannot be directly applied at diffusion scale for Type II

2. **CKN + Enstrophy Cannot Give θ ≥ c**
   - CKN gives: local concentration ≥ ε₀ at singular points (ABSOLUTE bound)
   - Enstrophy ODE: dE/dt ≤ CE³ limits E ~ (T*-t)^{-1/2} (GLOBAL timing)
     **[ERROR — corrected in v5: this is Leray's LOWER bound, not a ceiling]**
   - Neither prevents enstrophy from "escaping" to other regions
   - θ = E_loc/E_total is NOT bounded by these alone

3. **Anti-Escape is the Missing Heart**
   - Proving anti-escape unconditionally would rule out cascade/escape mechanisms
   - This is exactly the obstruction Tao identifies as the core difficulty
   - Anti-escape is logically STRONGER than what basic inequalities can force

4. **Conditional Theorem Formulated**
   - Hypothesis: "Bubble Persistence" - concentration at R_diff propagates to √(T*-t)
   - Conclusion: Blowup must be Type I → ESŠ backward uniqueness → regularity
   - All steps proven EXCEPT the anti-escape hypothesis

### Hierarchy of Anti-Escape Hypotheses

| Hypothesis | Statement | Strength |
|------------|-----------|----------|
| A | Critical norm concentration at √(T*-t) | Weakest (proven for Type I) |
| B | Bounded bubble count at √(T*-t) | Medium |
| B′ | Bubble persistence across [R_diff, √(T*-t)] | Medium (recommended) |
| C | Fraction θ₀ of enstrophy at R_diff | Strongest (our original) |

### Literature Integration

- **Seregin 2507.08733:** Uses Euler scaling + generalized LPS to exclude Type II
  - LPS plays the anti-escape role
  - Shows that SOME hypothesis beyond CKN is needed

- **Barker-Prange:** Proves concentration at √(T*-t) for Type I
  - The mechanism is local smoothing + contrapositive
  - Type I is exactly when this matches diffusion scale

- **CKN 1982:** Correct source for ε-regularity (not arXiv:2503.02575)

### Files Created

- `analysis/enstrophy-type-ii-exclusion.md` - Enstrophy constraint analysis
- `analysis/ckn-critical-concentration.md` - CKN + correct formulation
- `analysis/conditional-regularity-theorem.md` - **Main theorem statement**

### Resolution Paths

1. **Accept anti-escape as axiom** - reasonable for physics applications
2. **Prove in restricted classes** - axisymmetric, periodic, etc.
3. **Seregin-style** - minimal LPS-like condition
4. **Weaker sufficient condition** - bubble persistence (B′)

---

## v2 - θₖ Refactor + Literature Analysis + Tropical Dynamics (2025-12-22)

**Status:** Conditional

**Summary:** Replaced single-ball concentration with weaker K-ball finite-bubble conjecture. Added comprehensive literature analysis. Analyzed tropical crossing dynamics and identified new β → θ hypothesis.

### Update (Dec 22, 2025 - Session 2)

**Tropical Crossing Analysis:**
- L(t) = exp(1/τ)·(1+θ²) grows superexponentially
- L_max(t) ~ 1/τ grows linearly
- **Crossing MUST occur** as τ → 0, but may happen at τ > 0.1 (missing rigidity trigger)
- See `analysis/tropical-crossing-analysis.md`

**β → θ Hypothesis - RULED OUT:**
- Initial hypothesis: β → 0 (alignment) implies θ → 1 (concentration)
- **Finding:** β and θ are INDEPENDENT properties
  - β: pointwise vorticity-strain alignment
  - θ: spatial distribution of enstrophy
- Constantin-Fefferman coherence ≠ our β
- Tube structures can have β ≈ 0 but θ ≈ 0 if elongated
- See `analysis/beta-theta-investigation.md`

**New Promising Directions Identified:**
1. **Diffusion-scale matching:** If concentration scale r(t) ~ R(t), then θ ~ O(1)
2. **Carleman lower bounds:** Tao's methods might give lower bounds on local enstrophy
3. **Type II timescale separation:** β·R ~ (T-t)^{3α/2-1} → 0 might force concentration

### Changes from v1

1. **Hypothesis Weakening**
   - Replaced `concentration_near_blowup` (θ ≥ 0.5 in single ball)
   - With `finite_bubble_concentration` (θₖ ≥ c in K disjoint balls)
   - Key insight: Faber-Krahn is *additive* over disjoint balls

2. **New Mathematical Content**
   - Faber-Krahn additivity for K-ball configurations
   - Averaging lemma: θ ≥ θₖ/K via pigeonhole
   - K-threshold analysis: proof works if θₖ ≥ 0.203·K

3. **Literature Analysis**
   - Lei-Ren 2022: N(r) covering count can → ∞ (bad news)
   - Barker 2025: K=1 consistent, but θ ≥ e^{-M^{1813}} (exponentially small)
   - Barker-Prange 2022 Survey: Type I only, doesn't address Type II

4. **Refined Gap Identification**
   - Original gap: "Single-ball concentration doesn't hold"
   - Refined gap: "θ is exponentially small, not uniform"
   - The question shifts from "is K bounded?" to "is θ uniform?"

### Promising Directions Identified

1. **Tropical crossing inevitability** (PROMISING)
   - If crossings are unavoidable for Type II, proof closes
   - Bypasses θ uniformity question entirely

2. **Type II-specific concentration** (UNEXPLORED)
   - Type II has α > 1, so β → 0 faster
   - May force better concentration than Type I estimates

### Files

- `versions/v2.json` - Full analysis snapshot
- `papers/INDEX.md` - Literature analysis details

---

## v1 - Original Analysis (2025-12-20)

**Status:** Disputed (flawed)

**Summary:** Initial analysis of David Budden's Twitter proof (@davidmbudden). Identified the core flaw: 6 unproven axioms that essentially assume the conclusion.

### Key Findings

1. **Critical Flaw Identified**
   - The axiom `concentration_near_blowup` assumes θ ≥ 0.5 near blowup
   - This is precisely what would need to be proven for NS regularity
   - CKN partial regularity (dim ≤ 1) doesn't force this concentration

2. **Axiom Inventory**
   - `concentration_near_blowup` (HIGH severity)
   - `faber_krahn_on_ball` (MEDIUM severity)
   - `stretching_beta_bound` (MEDIUM severity)
   - `poincare_dissipation_bound` (MEDIUM severity)
   - `E_loc_le_E` (LOW severity)
   - `E_loc_nonneg` (LOW severity)

3. **What Was Genuinely Proven**
   - Numerical inequality κ·c_FK > 2
   - Logical structure: IF axioms hold, THEN no blowup
   - Type II dynamics (β → 0)

### Verdict

The proof is **logically sound but conditional on unproven axioms**. The hard work is assumed away. This is NOT a valid proof of NS regularity.

### Files

- `versions/v1.json` - Full analysis snapshot

---

## Version Numbering

We use simple versioning (v1, v2, v3, ...) where each version represents a significant change in:
- The hypothesis being assumed
- The analysis of what's proven vs. assumed
- Literature context or promising directions

Minor corrections and clarifications don't warrant new versions.

---

## Source

Original proof by David Budden (@davidmbudden)
- Tweet: https://x.com/davidmbudden/status/2002627726877069805
- Date: 2025-12-20
