# Navier-Stokes Regularity - Reference Papers

This directory contains key papers relevant to the θₖ refactor of the Navier-Stokes
regularity proof. The central question we're investigating:

> **Is the bubble count K bounded independent of scale near Type II blowup?**

---

## Paper Index

### 1. Lei & Ren 2022 - Quantitative Partial Regularity
**File:** `lei-ren-2022-quantitative-partial-regularity.pdf`
**arXiv:** [2210.01783](https://arxiv.org/abs/2210.01783)
**Published:** Advances in Mathematics (2024)

**Summary:** Proves a logarithmic improvement of the Caffarelli-Kohn-Nirenberg (CKN)
partial regularity theorem. Uses pigeonhole principle to find quantitative counterpart
for absolute continuity of dissipation energy.

**Key Results:**
- Logarithmic improvement of CKN covering bounds
- Existence of regularity intervals in one spatial direction
- Quantitative regularity criterion for axisymmetric solutions with small swirl

**Relevance to θₖ:** ⭐⭐⭐⭐⭐ CRITICAL
- This paper gives the most relevant covering number bounds N(r)
- Need to extract: does N(r) → ∞ as r → 0, or is it bounded?
- If N(r) = O(1), then finite bubble count is automatic
- The "pigeonhole principle" approach mirrors our averaging lemma

**Key Question to Answer:**
What is the explicit form of N(r) in their covering bounds?

**ANSWER (from reading the paper):**
The paper bounds Σ r_k(w) ≲ o(1/(k ln k)), the SUM of radii, NOT the COUNT.
Since r_k(w) can be as small as c|ln R_k|^{-2β} R_k, the covering number could be:
  N_k ≲ (bound) / (min radius) ~ |ln R_k|^{2β} / R_k → ∞ as R_k → 0

**CONCLUSION: N(r) is NOT bounded.** The paper does not give finite bubble count.
This is BAD NEWS for our θₖ approach - quantitative CKN alone is insufficient.

---

### 2. Barker 2025 - Quantitative Classification of Singularities
**File:** `barker-2025-quantitative-classification.pdf`
**arXiv:** [2510.20757](https://arxiv.org/abs/2510.20757)
**Submitted:** October 2025

**Summary:** Motivated by Hou's numerical blowup candidate, gives first quantitative
classification of potentially singular solutions near potential blowup times.
Implements Barker-Prange strategy (physical space analogue of Tao's approach).

**Key Results:**
- Quantitative bounds in vicinity of any potential blowup time
- "Improved quantitative regions of vorticity concentration"
- Double exponential lower bounds via Carleman inequalities

**Relevance to θₖ:** ⭐⭐⭐⭐
- Contains "vorticity concentration" results that may give ratio bounds
- Builds on Tao's quantitative estimates
- The concentration regions may inform bubble count estimates

**Key Question to Answer:**
Do the concentration regions have bounded multiplicity?

**ANSWER (from detailed analysis):**
- **Theorem 1 (eq 1.10):** Concentration in ONE ANNULUS at scale T^{1/2}
- **Proposition 13 (eq 3.7):** Vorticity in SINGLE BALL of radius M^{708}√t
- **Critical:** K=1 at each scale, but θ ≥ e^{-M^{1813}} (exponentially small)
- Type I ruled out for axisymmetric (any blowup must be Type II)

**CONCLUSION: K=1 consistent, but θ not uniform.** Does NOT close the gap.

---

### 3. Barker & Prange 2022 - Survey: From Concentration to Quantitative Regularity
**File:** `barker-prange-2022-survey.pdf`
**arXiv:** [2211.16215](https://arxiv.org/abs/2211.16215)
**Published:** Vietnam Journal of Mathematics (2023)

**Summary:** Short survey of recent developments in NS regularity, focusing on the
connection between concentration phenomena and quantitative regularity estimates.

**Key Questions Addressed:**
1. Are certain norms concentrating on small scales near potential blowup?
2. At what speed do scale-invariant norms blow up?
3. Can one prove explicit quantitative regularity estimates?
4. Can one break the criticality barrier?

**Relevance to θₖ:** ⭐⭐⭐⭐
- Excellent overview connecting concentration to regularity
- May clarify what "concentration" means in the literature vs our θₖ
- Links to dispersive PDE methods that may be applicable

**Key Question to Answer:**
Does their notion of "concentration" imply finite bubble count?

**ANSWER (from detailed analysis):**
- **Type I uses K=1:** Single ball captures γ_univ fraction (Kang-Miura-Tsai)
- **Multiple scales are NESTED annuli**, not disjoint balls at same scale
- **Type II NOT analyzed** - survey focuses on Type I only
- **Absolute bounds dominate:** E_loc ≥ f(t), not ratio bounds

**CONCLUSION: Does NOT address bubble count for Type II.**

---

### 4. Barker & Prange 2020 - Quantitative Regularity via Spatial Concentration
**File:** `barker-prange-2020-spatial-concentration.pdf`
**arXiv:** [2003.06717](https://arxiv.org/abs/2003.06717)

**Summary:** Proves quantitative regularity for NS via spatial concentration arguments.
This is the foundational paper for the Barker-Prange strategy used in later works.

**Key Results:**
- Spatial concentration implies regularity estimates
- Local-in-space smoothing arguments
- Contraposition: singular points induce localized vorticity concentration

**Relevance to θₖ:** ⭐⭐⭐⭐⭐ CRITICAL
- "Localized vorticity concentration" is exactly what we need!
- If singularity → concentration in bounded number of regions, we're done
- The contrapositive argument may give explicit bounds

**Key Question to Answer:**
How many concentration regions are forced by a singularity?

---

### 5. Hou 2024 - Nearly Self-Similar Blowup of Generalized NS
**File:** `hou-2024-generalized-blowup.pdf`
**arXiv:** [2405.10916](https://arxiv.org/abs/2405.10916)

**Summary:** Studies nearly self-similar blowup for generalized axisymmetric NS.
Develops novel two-scale dynamic rescaling using dimension as extra degree of freedom.

**Key Results:**
- Derives axisymmetric NS in arbitrary dimensions (first time for d > 3)
- Self-similar blowup with SOLUTION-DEPENDENT viscosity
- Effective dimension ≈ 3.188, converging to 3 as viscosity diminishes
- Maximum vorticity growth O(10^30) in rescaled model

**Relevance to θₖ:** ⭐⭐⭐
- Shows blowup requires DEGENERATE viscosity in his scenarios
- Standard NS with constant ν prevents blowup in his constructions
- Provides physical intuition but not direct bounds for our setting

**Key Insight:**
Hou's scenarios are NOT counterexamples to our proof approach because they
require modified NS. Standard constant-viscosity NS regularizes his solutions.

---

### 6. Hou 2021 - Potentially Singular Behavior of 3D NS
**File:** `hou-2021-potentially-singular.pdf`
**arXiv:** [2107.06509](https://arxiv.org/abs/2107.06509)

**Summary:** Earlier work presenting compelling numerical evidence for potential
singularity formation in 3D NS. Establishes the scenarios later refined in 2024 paper.

**Key Results:**
- Numerical candidate for NS singularity
- Two-scale solution structure analysis
- Shows constant viscosity "regularizes" the structure

**Relevance to θₖ:** ⭐⭐⭐
- Background for understanding Hou's program
- Key quote: constant ν "regularizes the two-scale solution structure and
  does not develop a finite-time singularity"
- Suggests structural constraints on any potential counterexample

---

## Reading Priority

For the θₖ refactor, read in this order:

1. **Lei & Ren 2022** - Extract explicit covering bounds N(r)
2. **Barker & Prange 2020** - Understand "localized concentration" structure
3. **Barker & Prange 2022 Survey** - Get overview of field
4. **Barker 2025** - Latest quantitative results
5. **Hou 2021 & 2024** - Understand what blowup would look like (background)

---

## Key Questions to Resolve

### Q1: Covering Number Bounds
From Lei-Ren 2022, what is the explicit dependence of covering number N(r) on
scale r as r → 0? Is it:
- N(r) = O(1) → Finite bubble count automatic!
- N(r) = O(log(1/r)) → Logarithmic growth, may still work
- N(r) = O(r^{-α}) → Power law growth, problematic

### Q2: Concentration Region Multiplicity
From Barker-Prange 2020, when a singularity forces "localized concentration,"
how many regions are involved? Is the count bounded?

### Q3: Ratio vs Absolute Bounds
Do any papers give RATIO bounds (E_loc/E ≥ c) or only ABSOLUTE bounds
(E_loc ≥ f(t))? The ratio is what we need.

### Q4: Type II Structure
Do the papers address Type II blowup specifically? What additional constraints
does α > 1 impose on concentration structure?

---

## Papers NOT Yet Downloaded (for reference)

- **Caffarelli-Kohn-Nirenberg 1982** - Original CKN theorem
  - Available at: https://doi.org/10.1002/cpa.3160350604
  - Classic result, establishes dim(singular set) ≤ 1

- **Tao 2019** - Quantitative bounds for critically bounded solutions
  - Blog post: https://terrytao.wordpress.com/2019/08/15/quantitative-bounds-for-critically-bounded-solutions-to-the-navier-stokes-equations/

---

## V3 Synthesis: Scale-Bridging Concentration (Dec 2025)

### Core Literature for Conditional Theorem

| Paper | What It Proves | Role in Chain |
|-------|---------------|---------------|
| CKN 1982 | ε-regularity: A(r)+C(r)+D(r) ≥ ε₀ at singular points | Step 1 |
| Standard | Enstrophy ODE: dE/dt ≤ CE³ | Step 2 |
| Barker-Prange 2020 | Type I concentration at √(T*-t) | Step 4 |
| ESŠ 2003 | Backward uniqueness excludes Type I | Step 5 |
| Seregin 2025 | Type II exclusion via LPS condition | Comparison |

### The Scale Mismatch Problem (V3 Key Finding)

**For Type I blowup:**
- Diffusion scale R_diff = √(ν/Ω) ≈ √(T*-t)
- Barker-Prange concentration works at this scale
- ESŠ backward uniqueness applies → no Type I blowup

**For Type II blowup:**
- R_diff << √(T*-t) (scales don't match)
- Barker-Prange only gives concentration at √(T*-t)
- Smoothing lemma cannot reach R_diff → GAP

### Bubble Persistence (B′) — The Minimal Hypothesis

**B′:** Concentration A(r) ≥ ε persists for all dyadic r ∈ [R_diff, c√(T*-t)]

This is:
- **Strictly weaker** than Seregin's LPS condition
- **Exactly what bridges** the scale gap for Type II
- **Rules out** cascade/escape mechanisms (Tao's core obstruction)

### Comparison of Anti-Escape Hypotheses

| Hypothesis | Strength | Applies to |
|------------|----------|------------|
| B′ (Bubble Persistence) | Weakest | All blowup |
| Seregin LPS | Medium | Type II |
| Type I bound | Strongest | Type I only |

### Important Reference Correction

⚠️ **CKN ε-regularity source:** CKN 1982, Comm. Pure Appl. Math. 35, 771-831
(NOT arXiv:2503.02575 which is Maria Esteban's 2025 expository paper)

---

## Notes

Last updated: 2025-12-22
Version: v3 (Conditional Regularity Theorem)
Main theorem: analysis/conditional-regularity-theorem.md
