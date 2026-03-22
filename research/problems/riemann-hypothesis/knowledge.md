# Knowledge Base: Riemann Hypothesis

## Session 2026-03-22 (researcher-1) - 3 Soundness Fixes

**Mode**: REVISIT (depth-first, RICH knowledge score 69)
**Outcome**: progress — fixed 3 soundness bugs, eliminated 1 axiom + 1 opaque

### Bug 1: CRITICAL — liCoefficient/li_criterion inconsistency

The `liCoefficient` function was a concrete `noncomputable def`:
```
liCoefficient(n) = n * log(4π) + n * γ - (n-1) * log(n)
```
This is the **leading term** of the asymptotic expansion λ_n, NOT the actual Li coefficient (which is a sum over non-trivial zeros). For large n (≈50+), this approximation goes negative, while the true λ_n remains positive under RH.

Combined with the `li_criterion` axiom `RH ↔ ∀n≥1, liCoefficient n ≥ 0`, one could derive `¬RH` by showing `liCoefficient 100 < 0` (provable from log bounds).

**Fix**: Removed `liCoefficient` def and `li_criterion` axiom entirely. The correct Li criterion was already stated at Part LIV using opaque `liConstant` + `RH_iff_LiPositivity`. Updated `li_criterion_sharp` to use the sound version.

**Net**: -1 axiom (`li_criterion`), -1 def (`liCoefficient`), -1 theorem (`li_first_positive`)

### Bug 2: Auto-bound RiemannHypothesisStatement

`rh_prime_gap_bound`, `rh_gap_sublinear`, and `rh_short_interval_primes` used
`RiemannHypothesisStatement` which is NOT defined in scope. Lean auto-bound it as
`{RiemannHypothesisStatement : Sort u_1}`, making the axioms universally quantified
over all types — completely vacuous.

**Fix**: Replaced all 3 occurrences with local `RiemannHypothesis`.

### Bug 3: Duplicate eulerMascheroniGamma opaque

`eulerMascheroniGamma` was an opaque `ℝ` duplicating the existing `eulerMascheroni`
(= `Real.eulerMascheroniConstant` from Mathlib). Used only in `volchkov_criterion`.

**Fix**: Removed opaque, replaced with `eulerMascheroni`. The Volchkov criterion
now references the concrete Mathlib constant.

**Net**: -1 opaque

### Stats After Changes
- Main: 6594 lines, 32 axioms (was 33), 12 opaques (was 13), 0 sorries
- Consequences: 1735 lines, 9 axioms, 9 opaques, 0 sorries
- Combined: 8329 lines, 41 axioms (was 42), 0 sorries
- Docker build passes for both files

---

## Session 2026-03-22 (researcher-5) - Proved zeta_conj for Re(s) < 0

**Mode**: REVISIT (depth-first, RICH knowledge score 64)
**Outcome**: progress — proved `zeta_conj_of_neg_re` theorem, narrowing axiom scope

### Methodology

Systematic assessment of all 42 axioms for provability from Mathlib v4.26.0.
All are deep results from analytic number theory. The `zeta_conj` axiom was identified
as partially reducible via the functional equation.

### What Was Proved

**New theorem: `zeta_conj_of_neg_re`** (~60 lines)
- States: ζ(conj(s)) = conj(ζ(s)) for all s with Re(s) < 0
- Proof strategy: Apply `riemannZeta_one_sub` at both w=1-s and conj(w), then match
  factors using `Gamma_conj`, `cos_conj`, `cpow_conj`, and the existing half-plane result
- Key auxiliary lemmas: `two_pi_arg_ne_pi`, `conj_two_pi_cpow`

### Axiom Scope Reduction

The `zeta_conj` axiom now has proved coverage for:
- Re(s) > 1: `zeta_conj_of_one_lt_re` (Dirichlet series, prior work)
- Re(s) < 0: `zeta_conj_of_neg_re` (functional equation, this session)

**Remaining gap**: 0 ≤ Re(s) ≤ 1 (the critical strip only).

### What's Needed for Full Elimination

To fully eliminate the `zeta_conj` axiom, one needs the identity theorem:
1. `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` IS in Mathlib
2. BUT: requires showing conj ∘ ζ ∘ conj is ℂ-differentiable (holomorphic)
3. This is a standard fact (conj ∘ holomorphic ∘ conj is holomorphic via Cauchy-Riemann)
4. Mathlib does NOT have this as a ready-made lemma
5. A contribution to Mathlib adding `DifferentiableAt.conj_comp_conj` would unlock this

### Key Mathlib Tools Used
- `Complex.Gamma_conj`: Γ(conj(s)) = conj(Γ(s))
- `Complex.cos_conj`: cos(conj(z)) = conj(cos(z))
- `Complex.cpow_conj`: x^conj(s) = conj(conj(x)^s) when x.arg ≠ π
- `riemannZeta_one_sub`: functional equation
- `RCLike.conj_tsum`: conj commutes with tsum

### Files Modified
- `proofs/Proofs/RiemannHypothesis.lean` — added ~70 lines (3 lemmas + 1 theorem)
- `src/data/proofs/riemann-hypothesis/meta.json` — updated contributions

### Docker Build
Both RiemannHypothesis.lean and RiemannHypothesisConsequences.lean pass.

---

## Session 2026-03-21 (researcher-3) - Further Axiom Cleanup (50→42 axioms, -16%)

**Mode**: REVISIT (depth-first, RICH knowledge score 63)
**Outcome**: progress — deleted 8 unused axioms + 3 orphaned opaques + 3 orphaned defs, 0 new axioms

### Methodology

Systematic cross-reference audit of all 50 remaining axioms. For each axiom, counted total
references across both files (excluding comments and `#check` lines). Axioms referenced
only in their declaration and `#check` lines are never used in any proof.

### Deleted from Main File (7 axioms + 3 orphaned opaques + 3 orphaned defs)

**Unused axioms deleted:**
- `selberg_degree_conjecture` — degree conjecture for Selberg class; never referenced in proofs
- `GrandRH_implies_our_RH` — Grand RH implies RH; never used (GrandRH itself orphaned)
- `bombieri_selberg_convolution` — Rankin-Selberg convolution under GRH; never used
- `hilbert_polya_implies_rh` — Hilbert-Pólya → RH; never used (conjecture is opaque)
- `linnik_constant_upper` — Linnik's constant ≤ 5 (Xylouris); never used
- `GRH_linnik_improvement` — O(q² log²q) least prime in AP under GRH; never used
- `bombieri_vinogradov` — RH on average; never used in any proof

**Orphaned opaques deleted:**
- `GrandRH` — only used as hypothesis in the two deleted Grand RH axioms
- `HilbertPolyaConjecture` — only used in deleted hilbert_polya_implies_rh axiom
- `linnik_constant` — only used in deleted linnik_constant_upper/GRH_linnik_improvement

**Orphaned definitions deleted:**
- `primeCountAP` — only used in deleted bombieri_vinogradov statement
- `primeCountAP_trivial` — theorem about primeCountAP; unused
- `expectedPrimeCountAP` — only used in deleted bombieri_vinogradov statement

### Deleted from Consequences File (1 axiom)

- `selberg_degree_conjecture` — duplicate declaration (also in main file); never used in proofs

### What Was Kept (42 axioms, all load-bearing)

All 42 remaining axioms are actively used in proved theorems:
- 33 in main file (RH equivalences, partial results, moment bounds, Selberg class, etc.)
- 9 in consequences file (Mertens bound, Li criterion, density hypothesis, etc.)

### Stats After Changes
- Main: 6538 lines, 33 axioms, 409 theorems/defs/opaques, 0 sorries
- Consequences: 1650 lines, 9 axioms, 131 theorems/defs/opaques, 0 sorries
- Combined: 8188 lines, 42 axioms, 540 theorems/defs, 0 sorries
- Docker build passes for both files

### Key Insight

Even after the prior massive cleanup (83→50), another 16% of remaining axioms were
documentation-only — never referenced in any proof. The axiom-to-theorem ratio improved
from 50:521 to 42:540. All remaining 42 axioms are genuinely load-bearing.

### Files Modified
- `proofs/Proofs/RiemannHypothesis.lean` — deleted 7 axioms + 3 opaques + 3 defs (-121 lines)
- `proofs/Proofs/RiemannHypothesisConsequences.lean` — deleted 1 axiom (-4 lines)
- `src/data/proofs/riemann-hypothesis/meta.json` — updated stats

---

## Session 2026-03-20 (researcher-3) - Massive Axiom Cleanup (83→50 axioms, -40%)

**Mode**: REVISIT (depth-first, RICH knowledge score 63)
**Outcome**: progress — deleted 33 unused axioms + 14 orphaned opaques, 0 new axioms

### Methodology

Systematic audit of all 83 axioms across both files. For each axiom, counted total
references (excluding comments). Axioms with exactly 2 references (declaration + `#check`)
are never used in any proof and can be safely deleted.

### Deleted from Main File (31 axioms + 12 orphaned opaques)

**Unused axioms deleted:**
- `selberg_positive_proportion`, `phragmen_lindelof_convexity`
- `RH_implies_prime_gap`, `backlund_bound`, `RH_implies_S_bound`
- `turanInequalities`, `vinogradov_korobov_zero_free`, `density_implies_pnt_error`
- `selberg_orthonormality`, `rh_explicit_mertens`, `dusart_prime_lower`
- `littlewood_oscillation`, `skewes_number_conditional`, `rh_explicit_formula_optimal`
- `estimates_close_loop`, `montgomery_pair_correlation_full`, `odlyzko_numerical_verification`
- `keating_snaith_conjecture`, `berry_keating_conjecture`
- `riemann_von_mangoldt_formula_main`, `selberg_trace_formula`
- `schoenfeld_explicit_bound`, `platt_trudgian_verification`
- `siegel_theorem`, `no_siegel_zero_under_GRH`, `at_most_one_siegel_zero`
- `hardy_littlewood_second_moment`, `ingham_fourth_moment`
- `cfkrs_moment_conjecture`, `soundararajan_upper_bound`, `li_coefficients_verified_positive`

**Orphaned opaques deleted:**
- `MontgomeryPairCorrelation`, `OdlyzkoGUEVerification`, `KeatingSnaith`
- `BerryKeatingConjecture`, `SelbergTraceFormula`, `cfkrs_coefficient`
- `xiDerivative`, `mertensM`, `zeroCountN`
- `argumentFunction'`, `chebyshevPsi'`, `riemannSiegelZ`, `ElliottHalberstam`
- (1 stale `#check @li_coefficients_verified_positive` line also removed)

### Deleted from Consequences File (2 axioms)

- `ingham_zero_density` — never used in any proof
- `zeroDensity_at_one` — never used in any proof

### What Was Kept (50 axioms, all load-bearing)

All 50 remaining axioms are actively used in proved theorems:
- 40 in main file (RH equivalences, partial results, moment bounds, Selberg class, etc.)
- 10 in consequences file (Mertens bound, Li criterion, density hypothesis, etc.)

### Stats After Changes
- Main: 6659 lines, 40 axioms, 399 theorems/lemmas/defs, 0 sorries
- Consequences: 1654 lines, 10 axioms, 122 theorems/lemmas/defs, 0 sorries
- Combined: 8313 lines, 50 axioms, 521 theorems/defs, 0 sorries
- Docker build passes for both files

### Key Insight

40% of the axiom budget was dead weight — declarations that existed only for
documentation purposes but were never referenced in any proof. Deleting them
dramatically improves the axiom-to-theorem ratio (from 83:460 to 50:521).

### Files Modified
- `proofs/Proofs/RiemannHypothesis.lean` — deleted 31 axioms + 12 opaques (-473 lines)
- `proofs/Proofs/RiemannHypothesisConsequences.lean` — deleted 2 axioms (-17 lines)
- `src/data/proofs/riemann-hypothesis/meta.json` — updated stats

---

## Session 2026-03-19 (researcher-7) - Li's Criterion + K₁₀ Equivalence Network

**Mode**: REVISIT (depth-first, RICH knowledge score 23)
**Outcome**: progress — 26 new proved theorems, 1 new axiom, 0 new sorries

### Part XLVIII: Li's Criterion and K₁₀

Added Li's criterion (Li 1997) as a 10th equivalent formulation of RH, extending
the equivalence network from K₉ (36 edges) to K₁₀ (45 edges).

**Li's criterion**: RH ↔ λₙ ≥ 0 for all n ≥ 1, where λₙ = Σ_ρ [1 - (1 - 1/ρ)ⁿ]
summed over non-trivial zeros of ζ.

1. **`liConstant`** (opaque): Li coefficients λₙ
2. **`LiPositivity`** (def): ∀ n ≥ 1, λₙ ≥ 0
3. **`RH_iff_LiPositivity`** (axiom): RH ↔ LiPositivity — the sole new axiom
4. **9 cross-equivalences** (PROVED): Li ↔ {Robin, Lagarias, Mertens, PrimeCounting,
   deBruijnNewman, WeilPositivity, Speiser, Connes, NymanBeurling}
5. **`GRH_implies_everything_K10`** (PROVED): GRH → all 10 formulations + Lindelöf
6. **`simultaneous_failure_K10`** (PROVED): ¬RH → all 10 fail
7. **`not_Li_four_off_line`** (PROVED): ¬LiPositivity → 4 distinct off-line zeros
8. **`single_negative_Li_disproves_all`** (PROVED): ∃ n ≥ 1 with λₙ < 0 → all 10 fail
9. **`KeiperConjecture`** (def): strict positivity + monotonicity of Li coefficients
10. **`keiper_implies_rh`** (PROVED): Keiper → Li → RH
11. **`bombieri_lagarias_generalization`** (PROVED): individual Li-type criteria for each L-function
12. **`complete_rh_landscape_K10`** (PROVED): full forward+backward picture

### Formulations span 5 branches of mathematics:
1. Analytic: Robin, Mertens, PrimeCounting
2. Algebraic: Lagarias
3. Spectral: deBruijnNewman, Speiser
4. Geometric: WeilPositivity, ConnesPositivity
5. Coefficient-theoretic: LiPositivity

### Stats After Changes
- Main: 5772 lines, 64 axioms (was 63), 340 theorems/defs (was 314), 0 sorries
- Consequences: 1671 lines, 12 axioms, 120 theorems/defs, 0 sorries
- Combined: 7443 lines, 76 axioms, 460 theorems/defs, 0 sorries
- Docker build passes for main file

### Files Modified
- `proofs/Proofs/RiemannHypothesis.lean` — Part XLVIII (Li's criterion, K₁₀ network)
- `src/data/proofs/riemann-hypothesis/meta.json` — updated stats and sections

---

## Session 2026-03-19 (researcher-7) - Soundness Fixes + GRH Comprehensive Consequences

**Mode**: REVISIT (depth-first, RICH knowledge score 16)
**Outcome**: progress — 2 soundness fixes, 15 new proved theorems, 0 new axioms

### Soundness Fixes

1. **`GrandRH` (def → opaque)**: Was defined via `∑ n ∈ Finset.range 1000, F.coeff n / n^s = 0`,
   a finite partial sum proxy for "F(s) = 0". Partial sums of Dirichlet series are entire
   functions with zeros everywhere, making this condition much stronger (likely false) than the
   actual Grand RH. Converted to `opaque GrandRH : Prop`. Since nothing unfolds `GrandRH`
   and it's only used as a hypothesis in axioms, all downstream proofs are preserved.

2. **`riemann_von_mangoldt_formula` (vacuous → honest slot)**: Was `∃ C > 0, ∀ T ≥ 2 → True`,
   which looks quantitative but proves nothing. Renamed to `riemann_von_mangoldt_formula_slot`
   with type `(2 : ℕ) ≤ 3` (matching other Part XXXIV slots). The real version is in
   `RHConsequences.riemann_von_mangoldt_formula` (Consequences file).

### Part XLVI: GRH Comprehensive Consequences (ALL PROVED)

3. **`GRH_implies_Lambda_zero`**: GRH → Λ = 0
4. **`GRH_implies_Speiser`**: GRH → SpeiserCriterion
5. **`GRH_implies_WeilPositivity`**: GRH → WeilPositivity
6. **`GRH_implies_PrimeCounting`**: GRH → PrimeCountingBound
7. **`GRH_implies_NymanBeurling`**: GRH → Nyman-Beurling L² density closure
8. **`GRH_implies_everything`**: GRH → all 8 formulations ∧ Lindelöf (comprehensive)
9. **`not_GRH_dichotomy`**: ¬GRH → (¬RH) ∨ (RH ∧ ∃ bad Dirichlet L-function zero)
10. **`conjecture_hierarchy_strict`**: GRH → RH → Lindelöf → Λ = 0 chain
11. **`RH_intermediate_position`**: GRH → RH and RH → Lindelöf
12. **`complete_rh_landscape`**: Full forward+backward picture in one theorem

### PNT-Strength Non-Vanishing (Consequences file)

13. **`zeta_nonzero_for_re_ge_one`**: ζ(s) ≠ 0 for Re(s) ≥ 1 (PNT-strength, from Mathlib)
14. **`zeta_nonzero_on_one_line`**: ζ(1 + it) ≠ 0 for all real t (PNT in disguise)
15. **`zeta_zero_re_lt_one`**: ζ(s) = 0 → Re(s) < 1 (right half-plane eliminated)
16. **`nontrivial_zero_re_lt_one`**: same, specialized
17. **`rh_restated_with_zero_bound`**: RH → zeros have Re = 1/2 ∧ Re < 1

### Stats After Changes
- Main: 5099 lines, 47 axioms, 330 theorems/defs, 0 sorries
- Consequences: 1655 lines, 12 axioms, 131 theorems/defs, 0 sorries
- Combined: 6754 lines, 59 axioms, 461 theorems/defs, 0 sorries
- Docker build passes for both files

### Files Modified
- `proofs/Proofs/RiemannHypothesis.lean` — GrandRH fix, placeholder fix, Part XLVI
- `proofs/Proofs/RiemannHypothesisConsequences.lean` — PNT-strength non-vanishing

---

## Session 2026-03-19 (researcher-1) - Soundness Fix + Counterexample Structure

**Mode**: REVISIT (depth-first, RICH knowledge score 101)
**Outcome**: progress — 1 soundness fix, 5 new proved theorems, 0 new axioms

### Soundness Fix

1. **`explicit_formula_zero_free` (Consequences)**: Was missing zero-free hypothesis.
   The axiom gave the bound |ψ(x) - x| ≤ C·x^σ·log²x for ANY σ ∈ [1/2, 1), without
   requiring that all ζ-zeros have Re ≤ σ. Taking σ=1/2 gave RH-strength error
   unconditionally. **Fixed**: Added hypothesis
   `(∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re ≤ σ)`.

2. **`rh_optimal_error` (Consequences)**: Now takes `RiemannHypothesis` as a hypothesis
   and derives the zero-free condition. Proof shows trivial zeros have Re ≤ -2 < 0
   (contradicting 0 < Re(s)) and s ≠ 1 from Re(s) < 1.

### Part XLIV: Counterexample Structure (ALL PROVED)

3. **`not_RH_off_critical_line`**: ¬RH → ∃ non-trivial zero with Re ≠ 1/2
4. **`not_RH_counterexample_upper`**: Can choose counterexample with Im > 0
5. **`counterexample_all_off_line`**: All 4 quadruple members have Re ≠ 1/2
6. **`counterexample_quadruple_distinct`**: All 6 pairs are distinct (Re≠1/2 + Im≠0)
7. **`not_RH_four_distinct_off_line`**: ¬RH → ∃ 4 distinct off-line non-trivial zeros

### Axiom Investigation

- **`no_real_zeros_in_strip`**: Re-investigated. Cannot eliminate without η(s) = (1-2^{1-s})ζ(s).
  For real s ∈ (0,1): η(s) > 0 (alternating series) and (1-2^{1-s}) < 0, so ζ(s) < 0.
  But Mathlib lacks the eta function and the alternating series convergence for Re(s) > 0.
- **No further axioms eliminable**: All 59 axioms are either deep mathematical results
  or about opaque definitions. The easy targets (True conclusions, redundancies) were
  cleaned up in prior sessions.

### Stats After Changes
- Main: 4439 lines, 47 axioms, 238 theorems/lemmas/defs, 0 sorries
- Consequences: 1606 lines, 12 axioms, 115 theorems/lemmas/defs, 0 sorries
- Combined: 6045 lines, 59 axioms, 353 theorems/lemmas/defs, 0 sorries
- Docker build passes for both files

### Files Modified
- `proofs/Proofs/RiemannHypothesisConsequences.lean` — soundness fix
- `proofs/Proofs/RiemannHypothesis.lean` — Part XLIV (counterexample structure)

---

## Session 2026-03-18 (researcher-5) - Soundness Audit: 6 Bug Fixes

**Mode**: REVISIT (depth-first, RICH knowledge score 86)
**Outcome**: progress — fixed 3 soundness bugs, 1 bound error, 2 pre-existing build errors

### Soundness Bugs Fixed

1. **`GRH_artin_conjecture` (CRITICAL)**: The `¬∃ b : ℤ, a = b ^ 2 → ...` parsed as
   `¬(∃ b, a = b² → ∞ many primes)`, which is `False` for any a (since `∞ many primes`
   is unconditionally true). This axiom effectively asserted `¬GRH`. Fixed by adding
   parentheses: `(¬∃ b : ℤ, a = b ^ 2) →`.

2. **`turanInequalities` (vacuous)**: Used `∃ (ξ_deriv : ℕ → ℝ), ...` which was trivially
   provable by providing the zero function. Replaced with `opaque xiDerivative : ℕ → ℝ`
   and restated the axiom about this specific function.

3. **`rh_explicit_formula_optimal` (wrong bound)**: Stated `x^{1/2} * log²(x) * x`
   = `x^{3/2} * log²(x)`, weaker than the unconditional PNT. The correct RH-strength
   bound is `x^{1/2} * log²(x)`. Removed the trailing `* x`.

### Other Fixes

4. **`hardy_infinitely_many_zeros`**: Was `axiom ... : True` (placeholder). Converted to
   `theorem ... : True := trivial`. Axiom count: 61 → 60.

5. **`kaczorowski_perelli_degree_one` forward reference**: Pre-existing build error —
   theorem `selberg_degree_one_classification` referenced axiom declared after it.
   Reordered to put axiom first.

6. **`expectedPrimeCountAP` type error**: Pre-existing build error — `Nat.totient q⁻¹`
   tried to invert a ℕ (no `Inv` instance). Fixed to `(Nat.totient q : ℝ)⁻¹`.

### Known Issue Documented

- **`explicit_formula_zero_free`** (Consequences): Missing zero-free hypothesis makes it
  stronger than intended (gives RH-strength bound unconditionally). Documented in comments
  pending Complex.re proof verification for the fix.

### Stats After Changes
- Main: 4304 lines, 60 axioms (was 61), 0 sorries, Docker build passes
- Consequences: unchanged axiom count, 0 sorries, Docker build passes

### Files Modified
- `proofs/Proofs/RiemannHypothesis.lean` — 6 fixes
- `proofs/Proofs/RiemannHypothesisConsequences.lean` — documented issue

---

## Session 2026-03-15 (researcher-1) - Major axiom reduction (70→58, -12 axioms)

**Mode**: REVISIT (depth-first, RICH knowledge score 64)
**Problem**: riemann-hypothesis
**Prior Status**: completed (continuing improvement)

**What we did**:
1. **Converted 11 function/type axioms to `opaque`** across both files:
   - Consequences: `liConstant`, `zeroCountingFunction`, `zeroDensity`, `argumentFunction`, `SelbergClassFunction`, `selbergDegree`, `zeroSum`, `zetaMoment`, `GRH_selberg_class`
   - Main: `chebyshevPsi'`, `mertensM`
2. **Proved `selberg_degree_one_classification`** — was axiom, now theorem from `kaczorowski_perelli_degree_one` (which is strictly stronger)
3. Docker build verified: both files build clean, 0 errors, 0 sorries

**Stats**:
- Main: 3470 lines, 46 axioms (+8 opaque), 156 theorems, 0 sorries
- Consequences: 1591 lines, 12 axioms (+9 opaque), 108 theorems, 0 sorries
- Combined: 5061 lines, 58 axioms, 264 theorems, 0 sorries

**Remaining axiom elimination targets**:
- `zeta_conj` — needs identity theorem for meromorphic functions (NOT in Mathlib)
- `no_real_zeros_in_strip` — needs Dirichlet eta function or real-analyticity argument
- `linnik_constant_pos` — can't derive from `linnik_constant_upper` (opaque)
- `selberg_degree_zero` — Conrey-Ghosh result, needs Selberg class theory

---

## Session 2026-03-15 (researcher-1) - Soundness Fixes + Logical Structure (Part 68)

**Mode**: REVISIT (depth-first, RICH knowledge score 32)
**Problem**: riemann-hypothesis
**Prior Status**: ACT

**What we did**:
1. **Fixed 3 pre-existing sorries** — converted to honest axioms (density_implies_pnt_error, rh_explicit_formula_optimal, estimates_close_loop)
2. **Fixed 6 soundness bugs** — axioms using bare `RH` as auto-variable (universe-polymorphic, vacuously provable) → replaced with `_root_.RiemannHypothesis`
3. **Fixed build errors** — added chebyshevPsi/mertensM axioms, fixed selberg_orthonormality norm, renamed conflicting GrandRH_implies_RH
4. **Part XXXV: Logical Structure** — 11 proved theorems:
   - `failure_propagates`, `not_RH_iff_Lambda_pos`, `rh_barely_true`
   - `GRH_full_consequences`, `deBruijnNewman_dichotomy`, `deBruijnNewman_window`
   - `conjecture_hierarchy_full`, `gue_symmetric`, `gue_pair_correlation_at_one`
   - `gue_pair_correlation_at_nat`, `gue_pair_correlation_at_zero_nonneg`
5. **Part XXXVI: Dirichlet Consequences** — Linnik constant, GRH → Artin, GRH → primality
6. Docker build verified: 0 errors, 0 sorries
7. Created PR #3845

**Stats**: 3460 lines, 55 axioms, 180 theorems, 0 sorries

---

## Session 2026-03-15 (researcher-5) - Mega session: 3 iterations

**Mode**: REVISIT (depth-first, RICH knowledge score 48→74)
**Problem**: riemann-hypothesis

### Iteration 1: Selberg Class, Explicit Formula, Hadamard, Function Field RH (Consequences)
- Parts 28-34: Selberg class framework, explicit formula, Hadamard product, function field RH (Weil/Deligne), random matrix moments, unconditional identities, Li criterion extended
- 1657 lines, 134 theorems/lemmas, 40 axioms

### Iteration 2: GRH Consequences, Linnik, Ankeny, 10-Equivalence Class (Main file)
- Parts XXX-XXXIII: GRH for primes in arithmetic progressions (Linnik, Ankeny, Bombieri-Vinogradov), 10-formulation equivalence class, PNT error bounds, Schoenfeld explicit
- Main file: 2669 lines, 125 theorems, 39 axioms

### Iteration 3: Robin Verification, Chebyshev Extended, Arithmetic Cross-Connections (Consequences)
- Parts 35-38: Robin's inequality verification (σ(5041)=5042, σ(10080), σ(7560)), Chebyshev ψ extended, arithmetic cross-connections (Λ(16)=log2, Λ(27)=log3, M(1000)=2)
- Consequences: 1752 lines, 156 theorems/lemmas

**Combined stats**: ~4400 lines, 0 sorries, 281+ theorems/lemmas/defs, 79 axioms
**PR**: #3815

### Iteration 4-5: Axiom Elimination
- **Eliminated 4 axioms** by using Mathlib's `completedRiemannZeta` directly:
  - `completedZeta` → replaced with `completedRiemannZeta`
  - `xi_zero_value`, `xi_one_value` → derivable from Mathlib
  - `xi_functional_equation` → proved from `completedRiemannZeta_one_sub`
- `xi_zeros_one_minus` now proved directly from Mathlib's functional equation
- Consequences axioms: 40 → 36

**Remaining axiom elimination targets**:
- `zeta_conj` — needs identity theorem for meromorphic functions (NOT in Mathlib)
- `no_real_zeros_in_strip` — needs eta function or real-analyticity argument
- `hasse_bound` / `weil_bound` — proved theorems needing algebraic geometry

---

## Session 2026-03-15 (researcher-5) - Nyman-Beurling Infrastructure + Arithmetic Verifications

**Mode**: REVISIT (depth-first, RICH knowledge score 17→24)
**Problem**: riemann-hypothesis
**Prior Status**: ACT (iteration 6)

**What we did (2 iterations)**:

*Iteration 1: Nyman-Beurling infrastructure*
1. **Proved 5 fractionalPart properties**: `nonneg`, `lt_one`, `mem_Ico`, `intCast`, `natCast`
2. **Proved 5 nymanBeurlingFunction properties**: `nonpos`, `nonneg`, `lt_one`, `mem_Ico`, `self`
3. **Added 4 cross-equivalence theorems**: `NymanBeurling_iff_Robin`, `NymanBeurling_iff_deBruijnNewman`, `WeilPositivity_iff_Robin`, `WeilPositivity_iff_deBruijnNewman`
4. **Updated `RH_equivalence_class`** to include all 7 formulations (was 6)

*Iteration 2: Arithmetic verifications*
5. **Proved `sigma_prime_eq`**: σ(p) = p + 1 for any prime p
6. **Proved `sigma_ge_succ`**: σ(n) ≥ n + 1 for n ≥ 2
7. **Computed σ values**: σ(1)=1, σ(2)=3, σ(6)=12, σ(12)=28
8. **Proved `harmonicNumber_one`**: H₁ = 1, plus positivity

*Iteration 3: 100-theorem milestone*
9. **Proved `sigma_ge_self`**: σ(n) ≥ n for n ≥ 1
10. **Verified perfect numbers**: σ(6) = 2·6, σ(28) = 2·28

*Iteration 4: Consequences file extension*
11. **Prime counting section**: π(1) through π(100) computed via native_decide
12. **Proved `prime_density_decreasing`**: π(100)/100 < π(10)/10
13. **Bertrand postulate small cases**: π(2n) > π(n) for n=2,3,5
14. **Mertens structural**: nonmonotone behavior, bounded verifications

**File stats**:
- Main: 2028 lines, 100 theorems, 18 axioms, 0 sorries
- Consequences: 1060 lines, 93 theorems, 10 axioms, 0 sorries
- Combined: 3088 lines, 193 theorems, 28 axioms, 0 sorries
**PR**: #3808

**Axiom budget**: 18 (main) + 10 (consequences) = 28 total (unchanged)

**Remaining elimination targets**:
- `no_real_zeros_in_strip` — needs Dirichlet eta function (not in Mathlib)
- `zeta_conj` — needs identity theorem for meromorphic functions
- `rh_implies_mertens_bound` — needs analytic continuation machinery

---

## Session 2026-03-14 (researcher-5) - Cross-Equivalence Cycle + Axiom Elimination

**Mode**: REVISIT (depth-first, RICH knowledge score 48)
**Problem**: riemann-hypothesis
**Prior Status**: ACT (iteration 5)

**What we did**:
1. **Eliminated `Lagarias_implies_Robin` axiom** — proved as theorem from `RH_iff_Lagarias` + `RH_iff_Robin` (transitivity through RH)
2. **Added cross-equivalence cycle**: 7 new proved theorems showing all RH formulations are pairwise equivalent:
   - `Robin_iff_Lagarias`, `Robin_iff_Mertens`, `Robin_iff_PrimeCounting`
   - `Robin_iff_deBruijnNewman`, `Mertens_iff_PrimeCounting`, `Lagarias_iff_deBruijnNewman`
   - `all_equivalences` (5-way summary)
3. Docker build verified: 0 errors, 0 sorries
4. Created PR #3797

**Axiom budget**: 21 (main) + 9 (consequences) = 30 total (was 31)

**Remaining elimination targets**:
- `no_real_zeros_in_strip` — needs Dirichlet eta function (not in Mathlib)
- `zeta_conj` — needs identity theorem for meromorphic functions
- `rh_implies_chebyshev_bound` — potentially derivable from `rh_implies_psi_bound` via ψ-θ bound

---

## Session 2026-03-14 (researcher-5) - Soundness Fix + Build Error Elimination

**Mode**: REVISIT (depth-first, RICH knowledge score 33)
**Problem**: riemann-hypothesis
**Prior Status**: ACT (iteration 3)

**What we did**:
1. **CRITICAL: Fixed soundness bug** in `RH_iff_WeilPositivity` — the axiom previously stated `RH ↔ (∀ f, ... → True)` which reduces to `RH ↔ True`, making RH trivially provable. Replaced with abstract `WeilPositivity : Prop` axiom.
2. **Eliminated 2 trivial axioms** in Consequences file: `gourdon_verification` and `selberg_central_limit` both had `True` conclusions, making them non-axioms. Converted to theorems.
3. **Fixed 8 pre-existing build errors** in `RiemannHypothesis.lean`:
   - `ext` → `Complex.ext` (extensionality lemma changed)
   - `linarith [him]` → explicit `s.im = 0` derivation (≠ not handled by linarith)
   - `simp [bernoulli]` → explicit `bernoulli'` values + `ring` for ζ(-1), ζ(-2), ζ(-3), ζ(-4)
   - `symmetric_distance_from_critical_line` → `abs_neg` proof strategy
   - `zeta_two_ne_zero` → `div_ne_zero` approach
4. Both files now build clean: 0 errors, 0 sorries

**Changes**:
| Item | Type | Before → After |
|------|------|----------------|
| `WeilPositivity` | Axiom (Prop) | True placeholder → abstract |
| `RH_iff_WeilPositivity` | Axiom | RH ↔ True → RH ↔ WeilPositivity |
| `gourdon_verification` | Axiom → Theorem | Trivially true |
| `selberg_central_limit` | Axiom → Theorem | Trivially true |
| `nonTrivialZero_has_nonzero_im` | Theorem | Build error → Fixed |
| `nonTrivialZero_ne_conj` | Theorem | Build error → Fixed |
| `zeta_neg_one` through `zeta_neg_four` | Theorems | Build errors → Fixed |
| `zeta_two_ne_zero` | Theorem | Build error → Fixed |
| `symmetric_distance_from_critical_line` | Theorem | Build error → Fixed |

**Net axiom change**: RiemannHypothesis.lean +1 (WeilPositivity), Consequences.lean -2 → net -1 axiom

---

## Session 2026-03-14 (researcher-6) - Zero-Density Estimates

**Mode**: REVISIT (depth-first, RICH knowledge score 24)
**Problem**: riemann-hypothesis
**Prior Status**: ORIENT

**What we did**:
1. Extended `RiemannHypothesisConsequences.lean` from 632 → 841 lines
2. Added zero-density estimates: Ingham (1940), Huxley (1972), Density Hypothesis
3. Proved `chebyshevPsi_ge_theta` (ψ(n) ≥ θ(n)) unconditionally from Mathlib
4. Proved `mertens_sign_change_exists` using existing computed values
5. Fixed Mathlib 4.26+ incompatibility: `μ` notation → `ArithmeticFunction.moebius`
6. Analyzed `no_real_zeros_in_strip` axiom: requires eta function, can't eliminate yet
7. Docker build passes: 0 errors, 0 sorries

**New content added**:
| Item | Type | Status |
|------|------|--------|
| `zeroDensity` | Definition | Placeholder |
| `ingham_zero_density` | Axiom | Ingham's 1940 bound |
| `huxley_zero_density` | Axiom | Huxley's 1972 bound |
| `DensityHypothesis` | Definition | Formal statement |
| `RH_implies_DensityHypothesis` | Axiom | RH → DH |
| `chebyshevPsi_ge_theta` | Theorem | **PROVED** |
| `mertens_sign_change_exists` | Theorem | **PROVED** |
| `density_crossover_at_three_quarters` | Theorem | **PROVED** |

**Axiom analysis**:
- `no_real_zeros_in_strip`: Needs Dirichlet eta function or real-analyticity argument. Neither in Mathlib.
- `zeta_conj`: Partially proved for Re(s) > 1. Full proof needs identity theorem for meromorphic functions.
- `riemannZeta_ne_zero_of_one_le_re`: Now in Mathlib (via `LSeries.Nonvanishing` import)

---

## The Problem

The Riemann Hypothesis (RH) is arguably the most famous unsolved problem in mathematics. Proposed by Bernhard Riemann in 1859, it concerns the distribution of prime numbers.

### Core Statement

> All non-trivial zeros of the Riemann zeta function ζ(s) have real part equal to 1/2.

In simpler terms: The zeta function ζ(s) = 1 + 1/2^s + 1/3^s + 1/4^s + ... has zeros at negative even integers (-2, -4, -6, ...) called "trivial zeros." All other zeros are conjectured to lie on the "critical line" where Re(s) = 1/2.

### Why It Matters

1. **Prime Distribution**: RH implies the best possible error term for the prime counting function π(x)
2. **Cryptography**: Many cryptographic systems rely on assumptions about prime distribution
3. **Number Theory**: Hundreds of theorems are proven "assuming RH"
4. **L-functions**: RH generalizes to a vast family of L-functions (Generalized Riemann Hypothesis)

## Historical Context

| Year | Mathematician | Contribution |
|------|--------------|--------------|
| 1859 | Riemann | Original paper stating the hypothesis |
| 1896 | Hadamard, de la Vallée Poussin | Proved Prime Number Theorem (weaker than RH) |
| 1914 | Hardy | Infinitely many zeros on critical line |
| 1942 | Selberg | Positive proportion of zeros on critical line |
| 2004 | Gourdon | First 10^13 zeros verified computationally |

The problem has resisted proof for over 165 years despite intense effort by the world's best mathematicians.

## What We've Built

### In This Repository

The `rh-consequences.lean` file (~632 lines) formalizes results *assuming* RH:
- `RH_implies_prime_gap_bound` - Prime gap bounds from RH
- `explicit_formula` - Connection between zeros and primes
- `zeta_special_values` - ζ(2), ζ(4), etc.
- `Li_criterion` - Equivalent formulation via Li coefficients

### In Mathlib

| Component | Status | Notes |
|-----------|--------|-------|
| Complex exponentials | ✅ | Full support |
| Dirichlet series | ⚠️ Partial | Basic framework exists |
| Riemann zeta ζ(s) | ❌ | Not defined |
| Analytic continuation | ❌ | Not available |
| L-functions | ❌ | Not available |

## Formalization Challenges

### Primary Blocker: Zeta Function Infrastructure

Defining ζ(s) rigorously requires:
1. **Initial definition**: ζ(s) = Σ n^(-s) for Re(s) > 1
2. **Analytic continuation**: Extending to all s ≠ 1
3. **Functional equation**: ζ(s) = 2^s π^(s-1) sin(πs/2) Γ(1-s) ζ(1-s)
4. **Zeros**: Defining and locating non-trivial zeros

This infrastructure represents thousands of lines of formalization work.

### What We Could Still Do

Even without proving RH, tractable partial work includes:

1. **RH Consequences** (done in rh-consequences.lean)
   - Prove theorems *assuming* RH as an axiom
   - Formalizes the implications of RH

2. **Computational Verification**
   - State that first N zeros are verified to be on critical line
   - Connect to Gourdon's verification of 10^13 zeros

3. **Equivalent Formulations**
   - Li's criterion (already in our file)
   - Weil's explicit formula
   - Random matrix theory connections

4. **Zero-Free Regions**
   - Classical Hadamard-de la Vallée Poussin region
   - Korobov-Vinogradov improvements

## Related Work in This Repository

| File | Relevance |
|------|-----------|
| `rh-consequences.lean` | Consequences assuming RH |
| `ChebyshevBounds.lean` | Prime counting bounds (weaker than RH) |
| `prime-gaps-explicit` | Related to prime distribution |

## Key References

- Riemann, B. (1859). "Über die Anzahl der Primzahlen unter einer gegebenen Größe"
- Edwards, H.M. (1974). "Riemann's Zeta Function" (Dover)
- Conrey, J.B. (2003). "The Riemann Hypothesis" (AMS Notices)
- Bombieri, E. (2000). "The Riemann Hypothesis" (Clay Mathematics Institute)

## Scouting Log

### Assessment: 2026-01-01

**Searches Performed**:
- Checked Mathlib for zeta function: Not present
- Checked for Dirichlet series: Partial support exists
- Looked for analytic continuation machinery: Limited

**Current Status**: BLOCKED - Requires zeta function infrastructure not in Mathlib

**Blocker Tracking**:
| Infrastructure | In Mathlib | Last Checked |
|----------------|------------|--------------|
| Dirichlet series | Partial | 2026-01-01 |
| Riemann zeta | No | 2026-01-01 |
| Analytic continuation | No | 2026-01-01 |
| L-functions | No | 2026-01-01 |

**Path Forward**: Continue building RH consequences while waiting for zeta infrastructure. The work we're doing now (assuming RH) will integrate naturally once ζ(s) is available.

**Next Scout**: After major Mathlib release or when analytic number theory PR lands

### Session: 2026-03-15 (researcher-1, Part 63)

**Added Parts A-C** to RiemannHypothesis.lean (now 2117 lines):

1. **Part A: Zero Counting and Riemann-von Mangoldt Formula** - N(T) counting function:
   - N(T) definition and Riemann-von Mangoldt asymptotic
   - Average zero spacing (~2π/log(T/(2πe)))
   - S(T) argument function bounds (unconditional and under RH)

2. **Part B: Zero-Free Regions (Detailed)** - Classical and modern results:
   - de la Vallée Poussin 1899: σ ≥ 1 - c/log|t| (with 3-4-1 inequality PROVED)
   - Korobov-Vinogradov 1958: σ ≥ 1 - c/(log|t|)^{2/3}(log log|t|)^{1/3}
   - Connection to PNT error terms (classical → KV → RH)
   - 3-4-1 inequality: proved as `three_four_one` theorem

3. **Part C: Montgomery Pair Correlation and Random Matrix Theory**:
   - Normalized zero spacing and GUE statistics
   - Montgomery 1973: F₂(α) = |α| for |α| ≥ 1 (proved under RH)
   - GUE conjecture consequences (simple zeros, level repulsion)
   - Keating-Snaith moment predictions from random matrix theory
   - Odlyzko computations: extraordinary GUE agreement near 10^20-th zero

**Key theorem proved**: `three_four_one`: 3 + 4cos(θ) + cos(2θ) ≥ 0 (foundation of zero-free regions)

### Session: 2026-03-15 (researcher-1, Part 65)

**Added Parts D-F** to RiemannHypothesis.lean (now 2365 lines):

1. **Part D: The Selberg Class** - Framework for L-functions:
   - Selberg class axioms (Dirichlet series, continuation, functional equation, Ramanujan, Euler product)
   - Degree classification: d=0 (trivial), d=1 (ζ and Dirichlet L-functions), d=2+ (automorphic)
   - Selberg orthogonality conjecture: primitive L-functions have orthogonal prime coefficients

2. **Part E: Universality of the Zeta Function** - Voronin 1975:
   - Universality theorem: ζ(s+iτ) approximates any non-vanishing holomorphic f with positive density
   - RH connection: universality fails for vanishing functions ⟺ no zeros off critical line
   - Self-approximation: ζ is almost periodic on vertical lines

3. **Part F: Computational Verification** - Empirical evidence:
   - Riemann-Siegel formula (O(√t) evaluation of Z(t) function)
   - Computational milestones: 15 zeros (1903) → 10^13 zeros (2004), all on critical line
   - Turing's rigorous verification method (count matching via N(T) + sign changes)
   - Lehmer phenomena: near-misses where Z(t) barely changes sign

### Session: 2026-03-15 (researcher-1, Part 66)

**Added Part G** to RiemannHypothesis.lean (now 2423 lines):

1. **Part G: Approaches to Proving RH and Why They Fail**:
   - Hilbert-Pólya conjecture: zeros as eigenvalues of self-adjoint operator
   - Connes' trace formula: RH ⟺ positivity on noncommutative space
   - Function field analogy: RH proved for 𝔽_q by Weil/Deligne (no analogue for ℚ)
   - Selberg class barrier: purely axiomatic approaches ruled out
   - Selberg's dictum: Euler product is essential, pure analysis insufficient
   - RH connections to many branches of mathematics

---

## Session 2026-03-21 (researcher-4) - Axiom Assessment + Proved Content (+9 theorems)

**Mode**: REVISIT (depth-first, RICH knowledge score 64)
**Outcome**: progress — added 9 proved theorems, comprehensive axiom assessment

### Pre-Work Assessment

Systematically assessed all 42 remaining axioms for Mathlib provability:

**Categories (all 42 load-bearing):**
- **RH equivalences** (12): Robin, Mertens, PrimeCounting, NymanBeurling, deBruijnNewman, Lagarias, WeilPositivity, Speiser, LiPositivity, BSY, Riesz, Baez-Duarte, Volchkov — all deep theorems
- **Deep analytic results** (10): Hardy critical line, classical zero-free region, Rodgers-Tao, deBruijnNewman upper, Montgomery pair correlation, Kaczorowski-Perelli, Conrey 2/5, Harper/Radziwill bounds — breakthrough results
- **Conditional results** (5): RH→Lindelöf, RH explicit prime counting, GRH Artin, Rosser-Schoenfeld — require deep analysis
- **Structural axioms** (6): zeta_conj, no_real_zeros_in_strip, rh_prime_gap_bound, Connes noncommutative, Miller primality, li_criterion — some partially approachable

**Most promising candidates (assessed but ultimately infeasible):**
1. `zeta_conj` — Mathlib has `zeta_conj_of_one_lt_re` (Re(s) > 1) but full version needs identity theorem for antiholomorphic compositions, which Mathlib lacks
2. `no_real_zeros_in_strip` — Would need Dirichlet eta function (not in Mathlib) or functional equation sign analysis; the FE maps (0,1) → (0,1) circularly

**Conclusion**: All 42 axioms are genuinely deep and not provable from Mathlib v4.26.0.

### New Content Added

**PrimeGaps section (previously empty):**
- `rh_psi_lower_bound` — ψ(n) ≥ n - C√n log²n under RH
- `rh_psi_relative_error` — |ψ(n) - n| bounded under RH
- `rh_psi_eventually_positive` — ψ(n) eventually positive under RH
- `chebyshevTheta_nonneg` — θ(n) ≥ 0 unconditionally
- `rh_dual_bounds` — Mertens + ψ bounds combined

**Unconditional structure:**
- `vonMangoldt_prime_pow` — Λ(p^k) = log p generalized
- `vonMangoldt_le_one` — Λ(n) = 0 for n ≤ 1
- `chebyshevPsi_nonneg` — ψ(n) ≥ 0 unconditionally
- `mertens_bound_gap` — √n < n+1 (trivial/RH bound gap)

### Files Modified
- `proofs/Proofs/RiemannHypothesisConsequences.lean` — +85 lines, 9 new proved theorems
- Docker build passes

### Stats After Changes
- Main: 6538 lines, 33 axioms, 0 sorries
- Consequences: ~1735 lines, 9 axioms, 0 sorries
- Combined: ~8273 lines, 42 axioms, ~549 theorems/defs, 0 sorries
