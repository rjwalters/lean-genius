# Knowledge — erdos-1001-oq-01

## S1 (researcher-10, 2026-05-13): initial survey

### Parent file context

`proofs/Proofs/Erdos1001Problem.lean` (249 lines, 0 sorries, 2 axioms)
formalises Erdős Problem #1001.  Key components:

| Name | Type | Source location | Status |
|------|------|-----------------|--------|
| `isApproximable` | `(A : ℝ) (y : ℕ) (α : ℝ) → Prop` | lines 42-43 | def |
| `approximationSet` | `(N : ℕ) (A c : ℝ) → Set ℝ` | lines 46-47 | def |
| `S` | `(N : ℕ) (A c : ℝ) → ℝ` (`= volume approximationSet`) | lines 50-51 | noncomputable def |
| `f` | `(A c : ℝ) → ℝ` (`= 12 A log c / π²`) | lines 64-65 | noncomputable def |
| `f_pos`, `f_linear_A`, `f_zero_A`, `f_one_c` | algebraic | lines 68-91 | theorem (proved) |
| `limitExists` | `(A c : ℝ) → Prop` | lines 94-95 | def |
| `inESTRegime` | `(A c : ℝ) → Prop` (`0 < A ∧ A < c/(1+c²)`) | lines 103-104 | def |
| `erdos_szusz_turan` | tendsto-statement in EST regime | lines 107-110 | **axiom** |
| `est_explicit_formula` | EST formula consequence | lines 112-115 | theorem |
| `kesten_sos` | `limitExists A c` (general) | lines 130-131 | **axiom** |
| `limitValue` | `(A c : ℝ) → ℝ` (via `Classical.choose kesten_sos`) | lines 134-138 | noncomputable def |
| `limit_convergence` | `Tendsto (S · A c) atTop (nhds (limitValue A c))` | lines 141-143 | theorem |
| `boca_method`, `xiong_zaharescu_method` | placeholder `Prop` | lines 154-158 | def (placeholders) |
| `FareyFraction` | `(n : ℕ) → Set ℚ` (uninstantiated) | lines 181-182 | def (stub) |
| `estBoundary` | `(c : ℝ) → ℝ` (`= c/(1+c²)`) | lines 192-193 | noncomputable def |
| `estBoundary_pos` | `c > 0 → estBoundary c > 0` | lines 196-198 | theorem |
| `outsideESTRegime` | `0 < A ∧ c/(1+c²) ≤ A` | lines 201-202 | def |
| `limit_in_est_regime` | EST regime: `limitValue A c = f A c` | lines 205-209 | theorem (via tendsto_nhds_unique) |
| `erdos_1001` | `limitExists A c` (the main result) | lines 234-236 | theorem (= `kesten_sos`) |

The S1 survey's load-bearing observation: **`limit_in_est_regime` (lines 205-209) is the
template the sub-goals A and B must follow.**  Its three-line proof

```lean
have hconv := erdos_szusz_turan A c hA hc hregime    -- tendsto to f A c
have hconv2 := limit_convergence A c hA hc            -- tendsto to limitValue
exact tendsto_nhds_unique hconv2 hconv
```

is the cleanest available pattern.  Sub-goal A (`limit_at_est_boundary`)
needs a `tendsto_at_boundary` analogue of `erdos_szusz_turan`; Sub-goal
B (`limit_tendsto_one_as_A_infty`) needs an interchange-of-limits
argument plus a measure-fill claim.

### Mathlib API map — verified at S1 via lake-pinned SHA

Lake-pinned: `proofs/lake-manifest.json` → mathlib4 @
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`, toolchain `v4.26.0`.

**Diophantine approximation (relevant; available):**

| Symbol | File | Line | Notes |
|---|---|---|---|
| `Real.exists_int_int_abs_mul_sub_le` | `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean` | 95 | Dirichlet pigeonhole |
| `Real.exists_nat_abs_mul_sub_round_le` | `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean` | 135 | Dirichlet, `k` natural |
| `Real.exists_rat_abs_sub_le_and_den_le` | `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean` | 147 | Dirichlet, rational |
| `Real.exists_rat_abs_sub_lt_and_lt_of_irrational` | `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean` | 176 | `|ξ - q| < 1/q.den²` for irrational ξ |
| `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational` | `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean` | 197 | Infinite-many-approximators |
| `Rat.finite_rat_abs_sub_lt_one_div_den_sq` | `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean` | 253 | Converse for rational ξ |
| `Real.exists_rat_eq_convergent` | `Mathlib/NumberTheory/DiophantineApproximation/Basic.lean` | 538 | Legendre: good approx is a convergent |
| `Real.convergent` | `Mathlib/NumberTheory/DiophantineApproximation/ContinuedFractions.lean` | (TBD; not audited at S1) | CF-convergent definition |

**Measure theory (relevant; available):**

| Symbol | File | Notes |
|---|---|---|
| `MeasureTheory.volume` | `Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean` | Lebesgue measure on `ℝ` (parent already imports) |
| `Tendsto.lim`, `tendsto_nhds_unique` | `Mathlib/Order/Filter/Basic.lean` | Used in `limit_in_est_regime` proof |

**Farey-fraction infrastructure (NOT in Mathlib v4.26.0):**

| Spelling searched | Result |
|---|---|
| `Mathlib/NumberTheory/Farey.lean` | NOT FOUND |
| `FareyFraction` (Mathlib) | NOT FOUND |
| `Farey.gap_bound` / `Farey.successor` / `Farey.pair_correlation` | NOT FOUND |
| `threeDistance` / Steinhaus three-distance | NOT FOUND |

The audit method: `gh api search/code` queries for `"Farey"` and
`"threeDistance"` against `repo:leanprover-community/mathlib4` at SHA
`2df2f015` returned **0 hits in `Mathlib/`**.  Hits in `nolints` /
metadata files are not load-bearing.

**Conclusion.** Closing the OQ-01 main goal via Farey-fraction
pair-correlation (BCZ 2001) requires a substantial upstream Mathlib
contribution.  Sub-goals A and B can be closed using only the parent
file's primitives + `tendsto_nhds_unique` + (possibly) a single
additional axiom.

### Three insights

1. **`limitValue` is opaque, but `tendsto`-statements about `S` are
   transparent.**  The parent's `limitValue` is `Classical.choose` of
   `kesten_sos`; any explicit equation about it must factor through
   uniqueness of limits.  The cleanest pattern: state an independent
   `tendsto`-statement (axiom or theorem) for `S(·, A, c)` under the
   regime hypothesis, then close via `tendsto_nhds_unique`
   against `limit_convergence`.  This is exactly what
   `limit_in_est_regime` does for the EST regime — it uses
   `axiom erdos_szusz_turan : Tendsto (fun N => S N A c) atTop (nhds (f A c))`.

2. **Sub-goal A (boundary case) is one continuity argument away.**
   If we additionally axiomatise (or prove via a continuity-from-
   monotonicity bridge):

   ```lean
   axiom limitValue_continuous_at_boundary :
     ContinuousAt (fun A => limitValue A c) (estBoundary c)
   ```

   then by composing with `est_explicit_formula` (whose hypothesis is
   `inESTRegime A c`, i.e., `A < c/(1+c²)`) and a left-limit argument,
   `limitValue (c/(1+c²)) c = lim_{A↗c/(1+c²)} f(A, c) = f(c/(1+c²), c)`.
   This is the cleanest path to a "boundary explicit formula" for
   `limitValue`.

3. **Sub-goal B (saturation) is a `Filter.Tendsto.atTop` claim.**
   `Tendsto (fun A => limitValue A c) atTop (nhds 1)` decomposes as:
   (i) **monotonicity** of `limitValue` in `A` (more `A` ⇒ larger
       approximation set ⇒ larger measure);
   (ii) **upper bound** `limitValue A c ≤ 1` (the set is a subset of
       `(0, 1)`); and
   (iii) **density** of the approximation set as `A → ∞` (the union
       becomes co-null in `(0, 1)`).
   The hardest part is (iii); (i) and (ii) are direct from the
   `S(N, A, c)` definition.  An axiomatisation of (iii)
   (`axiom approximation_set_fills` or analogue) reduces (B) to a
   `tendsto_of_monotone_bounded` Mathlib lemma.

### Two Mathlib gaps (sub-questions for upstream contribution)

A. **`Mathlib.NumberTheory.Farey`** — the basic infrastructure.
   Minimum content: `FareyFraction (n : ℕ) : Finset ℚ` with proven
   cardinality `1 + ∑_{k=1}^n φ(k)`; `Farey.gap_lower_bound`
   (`|x₁/y₁ − x₂/y₂| ≥ 1/(y₁ y₂)`); `Farey.successor` /
   `Farey.predecessor`; the three-distance theorem; the **Stern–Brocot
   tree** as a constructive enumeration.  Significance: high (used
   throughout analytic number theory); tractability: medium-high
   (well-documented in textbooks; the cardinality formula is
   elementary).

B. **`Mathlib.NumberTheory.FareyPairCorrelation`** — the BCZ
   measure.  Significance: medium-high (the OQ-01 main goal directly
   uses this); tractability: low (the BCZ density `Z(t)` involves
   integrals over the modular surface; significant analytic
   machinery).

### Race-safety check (S1)

```
$ gh pr list --search "erdos-1001-oq-01 in:title" --state all
(no hits)
```

PRs containing "erdos-1001" but for sibling slugs (oq-02, oq-02-oq-01,
oq-03) exist; none touch `oq-01`.  This is a clean fresh-slug S1.

Open claim: researcher-10, expires 2026-05-13T12:47:25Z.

### Build status

S1 is documentation-only.  No Lean files modified.  No build required.

### Next steps (S2-S4)

- **S2** — Sub-goal A boundary case.  Either add `axiom
  limitValue_continuous_at_boundary` and prove `limit_at_est_boundary`
  by left-limit, or attempt a direct
  `tendsto_at_boundary`-style axiom + `tendsto_nhds_unique`.
  Estimated: +20-40 lines in `Erdos1001Problem.lean`, +0 or +1 axiom.
- **S3** — Sub-goal B saturation limit.  State
  `limit_tendsto_one_as_A_infty` and discharge via
  (i) monotonicity (provable from `approximationSet_subset`),
  (ii) upper bound (provable from `approximationSet ⊆ Ioo 0 1`),
  (iii) density (likely 1 axiom or sub-goal).  Estimated: +30-60
  lines, +0-1 axiom.
- **S4+** — Main goal (BCZ-explicit form).  Defer to a Farey-
  infrastructure follow-up PR.
