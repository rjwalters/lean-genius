## Session 14 (researcher-3, 2026-05-14) — PREP: Mathlib v4.26.0 CLT-bearer audit refutes S9 plan

**Mode**: REVISIT (RICH; knowledge score 61) **Phase**: PREP (doc-only) **Iteration**: 14

### Why this PREP

S9 knowledge.md (researcher-8, 2026-05-08) committed Phase-4 to a
Portmanteau-bridge plan whose foundation is "apply Mathlib's i.i.d. CLT
to the Bernoulli-sum representation of `Binomial(n,p)`". S10/S11/S12
inherited this plan without re-verifying. With the file now BUILD
VERIFIED at S12 (`3209 jobs`, PR #18971 merged), the next step in the
deferred Phase-4 axiom-elimination is to discharge
`binomial_clt_pointwise` via that S9 plan. Before opening an ACT
session for the Portmanteau path, this PREP audits the cited Mathlib
bearers against the lake-pinned v4.26.0 SHA
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.

### Findings (verified via `gh api .../contents/...?ref=<SHA>`)

#### ✅ Portmanteau bridge — bearer present, signature confirmed

```
Mathlib/MeasureTheory/Measure/Portmanteau.lean:350

theorem ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
    {Ω ι : Type*} {L : Filter ι}
    [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]
    [HasOuterApproxClosed Ω]
    {μ : ProbabilityMeasure Ω} {μs : ι → ProbabilityMeasure Ω}
    (μs_lim : Tendsto μs L (𝓝 μ))
    {E : Set Ω} (E_nullbdry : μ (frontier E) = 0) :
    Tendsto (fun i ↦ μs i E) L (𝓝 (μ E))
```

NNReal-valued conclusion (the unprimed version). For specialization to
`Ω := ℝ` and `E := Set.Iic x`:

- `MeasurableSpace ℝ` ✅ (standard Borel instance)
- `TopologicalSpace ℝ` ✅ (standard)
- `OpensMeasurableSpace ℝ` ✅ (`borelSpace_real`, automatic)
- `HasOuterApproxClosed ℝ` ✅ — via the global instance at
  `Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.lean:217–218`:
  ```
  noncomputable instance (X : Type*) [TopologicalSpace X]
      [TopologicalSpace.PseudoMetrizableSpace X] : HasOuterApproxClosed X
  ```
  `ℝ` is `MetricSpace` ⇒ `PseudoMetrizableSpace`, so this fires
  automatically. (S9 cited line 31 incorrectly — the actual instance
  is line 217.)

#### ✅ `frontier_Iic` — bearer present, hypothesis confirmed

```
Mathlib/Topology/Order/DenselyOrdered.lean:149

theorem frontier_Iic [NoMaxOrder α] {a : α} : frontier (Iic a) = {a}
```

`NoMaxOrder ℝ` ✅ (standard instance).

#### ❌ Mathlib `iid_central_limit_theorem` — **DOES NOT EXIST at the pin**

Verified by tree traversal of the pinned SHA:

```
$ gh api "repos/leanprover-community/mathlib4/git/trees/<SHA>?recursive=true" \
    --jq '.tree[].path' | grep -i -E 'CentralLimit|/CLT|iid_central'
(no matches)
```

The S9 knowledge.md cites `Mathlib.Probability.CentralLimitTheorem` as
"providing Lindeberg–Lévy–style CLT scaffolding". **This file does not
exist at the v4.26.0 pin.** The full contents of
`Mathlib/Probability/` at the pin are:

```
BorelCantelli.lean    CDF.lean              CondVar.lean
ConditionalExpectation.lean    ConditionalProbability.lean
Decision/         Density.lean          Distributions/
HasLaw.lean       HasLawExists.lean     IdentDistrib.lean
IdentDistribIndep.lean    Independence/    Integration.lean
Kernel/           Martingale/           Moments/         Notation.lean
ProbabilityMassFunction/    Process/    ProductMeasure.lean
StrongLaw.lean    UniformOn.lean
```

There is `StrongLaw.lean` (with `strong_law_ae` and `strong_law_Lp`
proved unconditionally), but no CLT analogue. GitHub code search for
`iid_central_limit` and `central_limit` across the repo also returns
zero hits at all recent SHAs (search not pinned, but no hit at any
recent revision).

#### ⚠️ Local `Proofs.CentralLimitTheorem` — itself axiomatized

`proofs/Proofs/CentralLimitTheorem.lean` (the local CLT file)
provides `central_limit_theorem` at line 375, but the proof chain
depends on `clt_general_case_axiom` (line 352), `levy_continuity_axiom`
(line 309), `charFun_normalized_sum_limit` (line 241), `gaussian_fourier_identity`
(line 100), `stdGaussian`/`stdGaussian_isProbabilityMeasure` (lines 89/92),
and others. Importing this would **swap one axiom for several**, not
eliminate. Per the gallery's Axiom Integrity Policy, this is
not an axiom-elimination path — only a *re-architecture* path.

#### ✅ `gaussianReal` (Gaussian probability measure on ℝ) — bearer present

```
Mathlib/Probability/Distributions/Gaussian/Real.lean

:200  def gaussianReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ
:210  instance IsProbabilityMeasure (gaussianReal μ v)
:213  lemma noAtoms_gaussianReal {μ : ℝ} {v : ℝ≥0} (h : v ≠ 0) :
        NoAtoms (gaussianReal μ v)
:217  lemma gaussianReal_apply (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (s : Set ℝ) :
        gaussianReal μ v s = ∫⁻ x in s, gaussianPDF μ v x
:221  lemma gaussianReal_apply_eq_integral (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (s : Set ℝ) :
        gaussianReal μ v s = ENNReal.ofReal (∫ x in s, gaussianPDFReal μ v x)
```

The `Iic x` mass of `gaussianReal 0 1` is the integral
`∫_{Set.Iic x} gaussianPDFReal 0 1 t dt`, which matches our
`standardNormalCDF x` definition (this file, line ≈ 156). A small
bridge lemma (~5–10 LOC) would identify
`(gaussianReal 0 1 : ProbabilityMeasure ℝ) (Set.Iic x) = standardNormalCDF x`
with ENNReal/NNReal casts. **No Mathlib lemma at the pin closes this
directly**; this becomes a new local helper.

#### ✅ `PMF.binomial` — bearer present (PMF form)

```
Mathlib/Probability/ProbabilityMassFunction/Binomial.lean:29

def binomial (p : ℝ≥0) (h : p ≤ 1) (n : ℕ) : PMF (Fin (n + 1))
```

PMF-form, not Measure-form. The Mathlib path `PMF.toMeasure` exists
generically (`Mathlib/Probability/ProbabilityMassFunction/Basic.lean`),
but the composition `(PMF.binomial p h n).toMeasure (Set.Iic x)` is
*not* a named identity at the pin. Identifying it with our concrete
`binomialCDF n p x` (this file) is another local bridge lemma (~10–20
LOC); the discrete-sum unfolding goes through `PMF.toMeasure_apply` +
`Finset.sum_filter`.

#### ❌ No `Mathlib.Probability.Distributions.Binomial.lean` (Measure form)

The Distributions/ directory at the pin has:
`Beta.lean`, `Exponential.lean`, `Fernique.lean`, `Gamma.lean`,
`Gaussian/`, `Geometric.lean`, `Pareto.lean`, `Poisson.lean`,
`Uniform.lean`. **No `Binomial.lean` in Distributions/.** The binomial
distribution is only available as a PMF, never as a measure with a
named identity.

### What this means for Phase-4 (axiom-elimination of `binomial_clt_pointwise`)

The S9 plan (apply Mathlib's i.i.d. CLT + Portmanteau bridge) has
**one half intact and one half missing** at v4.26.0:

| Half | Status |
|---|---|
| Portmanteau bridge (`tendsto_measure_of_null_frontier_of_tendsto`) | ✅ Present, signature matches S9 template |
| The i.i.d. CLT input it consumes (`Tendsto μs atTop (𝓝 μ)` for standardized binomial → standardGaussian) | ❌ No Mathlib bearer exists at the pin |

**Three viable next-actions**, in increasing order of effort:

1. **Defer Phase-4; keep the axiom honestly.** The status `axiomatized`
   with `axiomCount: 1` reflects a real mathematical assumption (the
   classical de Moivre–Laplace theorem). No degradation; the entry is
   correctly classified per the Axiom Integrity Policy. *Estimated
   work: 0 LOC.* Honest.

2. **Construct the local i.i.d. CLT input directly from
   characteristic functions** using Mathlib's `charFun` API
   (`Mathlib/Probability/Moments/ComplexMGF.lean` and friends). This
   would build, just for the Bernoulli/binomial case, the
   characteristic-function convergence
   `charFun (μs n) → charFun (gaussianReal 0 1)` and chain it through
   Lévy continuity (local proof) to weak convergence. Heavy: requires
   the Mathlib `charFun` API surface to be reverified, plus a local
   Lévy-continuity statement (which the local
   `Proofs.CentralLimitTheorem` axiomatizes as `levy_continuity_axiom`
   at line 309). Net: still axiomatized, just by a *smaller, more
   canonical* axiom than `binomial_clt_pointwise`. *Estimated work:
   200–400 LOC, multi-iteration.* Trades one specific axiom for a
   more general one — gallery taste choice.

3. **Track upstream Mathlib for a named CLT.** Mathlib community PRs
   on CLT are reportedly in flight (no specific PR number verified in
   this PREP — that would be a separate audit). When a named
   `iid_central_limit_theorem` or `central_limit_lindeberg_levy` lands,
   the S9 plan becomes mechanically viable: import it, instantiate at
   the standardized binomial, apply the Portmanteau bridge above,
   bridge `binomialCDF` ↔ `(PMF.binomial _ _ _).toMeasure`. *Estimated
   work once upstream lands: 50–100 LOC.* This is the realistic
   long-game answer.

### Recommendation

**Option 1 (defer) is correct for now.** The slug is BUILD VERIFIED,
the axiom is mathematically honest (classical de Moivre–Laplace, well
beyond textbook level), and the structural reduction
`multinomialMarginalCDF_eq_binomialCDF` (the substantive Lean
contribution of this slug) is fully proven. The path to elimination
exists in principle (Option 3 will be plug-and-play once Mathlib lands
a named CLT), and Option 2 is available if the gallery prefers a more
atomic axiom. **There is no remaining sorry; the open question is
purely a future Mathlib-bearer dependency**, and S9's
plan—reinterpreted at the correct v4.26.0 pin—remains valid as a
template for the day the bearer arrives.

### What S14 explicitly does NOT do

- **No Lean changes.** The Lean file is BUILD VERIFIED and at
  `703 LOC / 0 sorries / 1 axiom` per S12 (PR #18971). No tactic
  edits, no new lemmas, no axiom restructuring.
- **No state.md / JSON edit.** The open S13 STATE-SYNC PR #19018 by
  researcher-9 (2026-05-14T07:44Z, mergeable, clean) refreshes
  `state.md` summary lines and JSON `currentState.*` fields; this PREP
  is intentionally orthogonal to avoid race-collision. After #19018
  merges, a downstream session can roll forward state.md/JSON to
  reference this S14 finding.
- **No annotations.json / meta.json edit.** Gallery metadata unchanged.
- **No Docker build.** Doc-only PREP.

### Files modified by S14

- `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03/sessions/2026-05-14-s14-prep-mathlib-v426-clt-bearer-audit.md` (this file)
- `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03/knowledge.md` (append S14 entry summarising the bearer audit; no edits to prior entries)

### Verification trail (commands)

```bash
SHA=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67

# Portmanteau bridge bearer
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/MeasureTheory/Measure/Portmanteau.lean?ref=$SHA" \
  --jq .content | base64 -d | grep -n 'tendsto_measure_of_null_frontier_of_tendsto'
# → 333, 348, 350, 354, 365

# frontier_Iic bearer
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Topology/Order/DenselyOrdered.lean?ref=$SHA" \
  --jq .content | base64 -d | grep -n 'frontier_Iic\b'
# → 146, 149

# HasOuterApproxClosed for ℝ
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/MeasureTheory/Measure/HasOuterApproxClosed.lean?ref=$SHA" \
  --jq .content | base64 -d | grep -n 'PseudoMetrizableSpace'
# → 218 (instance line)

# Mathlib CLT absence
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Probability?ref=$SHA" \
  --jq '.[].name' | grep -i -E 'central|clt'
# → (empty)
gh api "repos/leanprover-community/mathlib4/git/trees/$SHA?recursive=true" \
  --jq '.tree[].path' | grep -i -E 'CentralLimit|iid_central|/CLT'
# → (empty)

# Gaussian measure on ℝ
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Probability/Distributions/Gaussian/Real.lean?ref=$SHA" \
  --jq .content | base64 -d | grep -nE 'gaussianReal\b' | head
# → 24, 30, 32, 200, 203, 207, 210, 213, 217, 221, 228, 230, ...

# Binomial PMF (no Measure form)
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Probability/Distributions?ref=$SHA" \
  --jq '.[].name' | grep -i binomial
# → (empty)
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/Probability/ProbabilityMassFunction/Binomial.lean?ref=$SHA" \
  --jq .content | base64 -d | grep -n '^def\|^theorem' | head
# → 29 (def binomial), 42, 47, 52, 56, 60, …
```

### Race disclosure

- **PR #19018** (open, doc-only Session 13 STATE-SYNC by researcher-9,
  2026-05-14T07:44Z, `MERGEABLE`/`CLEAN`) modifies `state.md` and the
  JSON. This PR is intentionally orthogonal: only `knowledge.md` (which
  #19018 does not touch) and a new session file. **No race collision.**
- No other open PR mentions this slug. (`gh pr list ... --search "binomial-theorem-oq-02-oq-01-oq-01-oq-03 in:title" --state open` returned only #19018 at 2026-05-14T20:35Z.)

### Pre-claim cross-checks

- ✅ Worktree synced to `origin/main` BEFORE branch creation
  (`git checkout -B ... origin/main`)
- ✅ Fresh topic branch off `origin/main`
- ✅ Disjoint from #19018 (knowledge.md + new session file vs.
  state.md/JSON)
- ✅ No Lean edits — preserves BUILD VERIFIED status from S12 (PR #18971)
- ✅ `--repo rjwalters/lean-genius --head <branch-name>` (worktree
  multi-remote workaround per researcher-feedback memory)
- ✅ Mathlib bearers verified at v4.26.0 pinned SHA
  `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (not master)

### Outcome

**Mode**: REVISIT (RICH, score 61)
**Phase**: PREP (doc-only)
**Build status**: unchanged — BUILD VERIFIED (S12, 3209 jobs)
**Axiom count**: unchanged — 1 (`binomial_clt_pointwise`)
**Sorry count**: unchanged — 0
**S14 contribution**: Mathlib v4.26.0 bearer audit refuting the
key S9 assumption (Mathlib iid CLT does not exist at the pin) and
articulating three Phase-4 next-action options (defer / local-charFun /
upstream-track). Honest research finding; prevents future researchers
from re-walking the S9 path expecting a Mathlib bearer that isn't
there.
