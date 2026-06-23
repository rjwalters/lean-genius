# S13 PREP — `binomial_clt_pointwise` discharge: Mathlib-pinned bearer audit

**Researcher**: researcher-3 (Claude Opus 4.7)
**Date**: 2026-05-15 ~04:50 UTC
**Phase**: PREP (pre-ACT, doc-only)
**Trigger**: post-S12 BUILD-VERIFIED state — file is clean, sole remaining axiom
is `binomial_clt_pointwise` (de Moivre–Laplace), and the S9 discharge plan
named one specific Mathlib bearer (`ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum`).
S13 pin-verifies that bearer at the lake-pinned Mathlib SHA before any ACT
session attempts the bridge.

**Conflict-free**: only adds this single new file under `sessions/`. No edits
to `state.md`, `knowledge.md`, `*.json`, or any `.lean` file. Composes
trivially with any future ACT or with concurrent PREPs on this slug.

---

## §1 — Critical finding: S9 plan is BLOCKED at the lake-pinned SHA

The S9 (researcher-8, 2026-05-12) and S11 (researcher-1, 2026-05-13)
discharge plans both name `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum`
as the Mathlib CLT lemma to compose against. Pin-verification shows:

```
$ gh api "repos/leanprover-community/mathlib4/contents/\
    Mathlib/Probability/CentralLimitTheorem.lean\
    ?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"
{"message":"Not Found", ...}

$ gh api "repos/leanprover-community/mathlib4/contents/\
    Mathlib/Probability/CentralLimitTheorem.lean"   # master HEAD
{"name":"CentralLimitTheorem.lean", "size":7635, ...}      ✓ exists at master
```

**`Mathlib/Probability/CentralLimitTheorem.lean` does not exist at the
lake-pinned Mathlib SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`** (per
`proofs/lake-manifest.json:mathlib`). It exists only at master HEAD.
Therefore, `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum`
cannot be cited as a bearer until either (a) the lake manifest is bumped
to a Mathlib SHA that contains the file, or (b) the gallery introduces a
new explicit axiom with the same statement.

The S9 plan is invalid as written.

### What the bearer would have provided (master-HEAD signature)

Reproduced verbatim from
`Mathlib/Probability/CentralLimitTheorem.lean@master` for forensic record:

```lean
/-- **Central Limit Theorem:** Given a sequence of random variables
`X : ℕ → Ω → ℝ` that are independent, identically distributed, centered
and with variance `1` and a random variable `Y : Ω' → ℝ` following
`gaussianReal 0 1`, the sequence
`n ↦ (√n)⁻¹ * ∑ k ∈ Finset.range n, X k` converges to `Y` in
distribution. -/
theorem tendstoInDistribution_inv_sqrt_mul_sum
    (hY : HasLaw Y (gaussianReal 0 1) P')
    (h0 : P[X 0] = 0) (h1 : P[X 0 ^ 2] = 1) (hindep : iIndepFun X P)
    (hident : ∀ (i : ℕ), IdentDistrib (X i) (X 0) P P) :
    TendstoInDistribution
      (fun (n : ℕ) ω ↦ (√n)⁻¹ * ∑ k ∈ Finset.range n, X k ω)
      atTop Y (fun _ ↦ P) P'
```

The proof at master HEAD goes via Lévy convergence /
characteristic functions, which themselves require:

| Bearer | At master HEAD | At lake-pinned SHA |
|---|---|---|
| `Mathlib/Probability/CentralLimitTheorem.lean`              | ✓ | **✗** |
| `Mathlib/MeasureTheory/Measure/CharacteristicFunction/...`  | ✓ | **✗** |
| `Mathlib/MeasureTheory/Measure/LevyConvergence.lean`        | ✓ | **✗** |
| `Mathlib/Probability/Independence/CharacteristicFunction.lean` | ✓ | ✓ |

Three of the four bearer transitive-dependencies are also absent at SHA;
this is not a single missing file but a missing module subsystem.

---

## §2 — Pin-verified bearer table (what IS present at SHA)

Verified via `gh api repos/leanprover-community/mathlib4/contents/...?ref=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`
on 2026-05-15. All sizes/line numbers extracted from base64-decoded
`.content` payloads.

| # | Bearer | File @ SHA | Size | Notes |
|---|---|---|---|---|
| B1 | `MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto` | `Mathlib/MeasureTheory/Measure/Portmanteau.lean:350` | 46 KB | requires `[OpensMeasurableSpace Ω] [HasOuterApproxClosed Ω]` |
| B2 | `frontier_Iic` | `Mathlib/Topology/Order/DenselyOrdered.lean:149` | — | requires `[NoMaxOrder α]`; ℝ qualifies |
| B3 | `MeasureTheory.TendstoInDistribution` (def) | `Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean:~80` | 15.7 KB | structure with three fields; namespace `MeasureTheory`, NOT `ProbabilityTheory` |
| B4 | `MeasureTheory.TendstoInDistribution.continuous_comp` | `…/ConvergenceInDistribution.lean` | — | continuous mapping theorem |
| B5 | `MeasureTheory.TendstoInDistribution.prodMk_of_tendstoInMeasure_const` | `…/ConvergenceInDistribution.lean` | — | Slutsky's theorem |
| B6 | `ProbabilityTheory.HasLaw` (structure) | `Mathlib/Probability/HasLaw.lean:38` | 5.9 KB | `aemeasurable + map_eq` fields |
| B7 | `ProbabilityTheory.IdentDistrib` (structure) | `Mathlib/Probability/IdentDistrib.lean` | 17.2 KB | i.i.d. predicate |
| B8 | `ProbabilityTheory.iIndepFun` | `Mathlib/Probability/Independence/Basic.lean:136` | — | family-of-functions independence |
| B9 | `ProbabilityTheory.gaussianReal` | `Mathlib/Probability/Distributions/Gaussian/Real.lean:200` | — | the standard normal MEASURE |
| B10 | `ProbabilityTheory.gaussianReal_apply_eq_integral` | `…/Gaussian/Real.lean:221` | — | `gaussianReal μ v s = ENNReal.ofReal (∫ x in s, gaussianPDFReal μ v x)` |
| B11 | `ProbabilityTheory.noAtoms_gaussianReal` | `…/Gaussian/Real.lean:213` | — | `NoAtoms (gaussianReal μ v)` for `v ≠ 0` |
| B12 | `IsProbabilityMeasure (gaussianReal μ v)` instance | `…/Gaussian/Real.lean:~205` | — | infer-instance |
| B13 | `PMF.binomial` | `Mathlib/Probability/ProbabilityMassFunction/Binomial.lean:~30` | — | `PMF (Fin (n+1))`, NOT yet `Measure ℝ` |
| B14 | `PMF.binomial_apply` | `…/ProbabilityMassFunction/Binomial.lean:~40` | — | concrete formula matches our `binomialCDF` summand |

**Implied bearer absences** (relative to S9 plan):

- ❌ `ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum` — see §1
- ❌ `ProbabilityTheory.charFun_inv_sqrt_mul_sum` — same module
- ❌ `MeasureTheory.ProbabilityMeasure.tendsto_iff_tendsto_charFun` — same subsystem
- ❌ Any direct `Bernoulli sum → Binomial` measure-equivalence lemma in Mathlib
  (search returned no hits at SHA)

---

## §3 — Three corrected discharge options

### Option A (Mathlib-bump, recommended IF gallery-wide bump is acceptable)

**Plan**: bump `proofs/lake-manifest.json:mathlib.rev` from
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` to a SHA that contains
`Mathlib/Probability/CentralLimitTheorem.lean`. Then the S9 plan applies
nearly verbatim:

1. **Lemma A** (Bernoulli→Binomial bridge): construct n i.i.d. Bernoulli(p)
   random variables `X₁, …, Xₙ` on a finite product probability space; show
   the law of `∑ Xᵢ` equals `Binomial(n, p)` (as a `Measure ℝ` via the
   pushforward of `PMF.binomial`'s `toMeasure`). ~80–150 LOC.

2. **Lemma B** (CLT application): apply `tendstoInDistribution_inv_sqrt_mul_sum`
   to `Yⱼ := (Xⱼ - p) / √(p(1-p))` (centered, unit-variance, i.i.d.); deduce
   that `(√n)⁻¹ * ∑ Yⱼ` converges in distribution to `gaussianReal 0 1`.
   ~30–50 LOC.

3. **Lemma C** (Portmanteau bridge): from convergence in distribution +
   `noAtoms (gaussianReal 0 1)` + `frontier_Iic`, deduce pointwise CDF
   convergence at every `x : ℝ`. ~25–40 LOC. **(Provable at SHA — see §4.)**

4. **Compose** into the discharge of `binomial_clt_pointwise`. ~30–50 LOC.

**Risk profile**:
- Mathlib bump touches ~1500–3000 transitive theorem rebuilds; v4.26.0 →
  later may surface API drift across the entire gallery (memory pattern
  `feedback_mechanic_mathlib_v426_*` shows this is a recurring cluster).
- Worst-case: gallery-wide mechanic-kit needed before the discharge
  itself can land.
- Best-case: bump is clean and discharge lands within ~250 LOC.
- **LOC budget**: ~200–300 LOC research + Mathlib-bump cascade
  (unbounded a-priori).

### Option B (axiom-rebase, conservative)

**Plan**: keep the lake-pinned Mathlib version. Refactor the existing
`binomial_clt_pointwise` axiom into smaller pieces; replace the
"de Moivre–Laplace" axiom with a more granular CLT-statement-axiom
plus provable bridge lemmas.

```lean
-- New axiom (drop-in replacement, mirrors master-HEAD CLT statement):
axiom iid_central_limit_theorem_pinned_SHA
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {X : ℕ → Ω → ℝ}
    (h0 : ∫ ω, X 0 ω = 0) (h1 : ∫ ω, (X 0 ω)^2 = 1)
    (hindep : ProbabilityTheory.iIndepFun X volume)
    (hident : ∀ i : ℕ, ProbabilityTheory.IdentDistrib (X i) (X 0) volume volume) :
    MeasureTheory.TendstoInDistribution
      (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ k ∈ Finset.range n, X k ω)
      Filter.atTop (fun _ : Ω => (0 : ℝ)) -- dummy Y; will fix to gaussian sample
      (fun _ => volume) volume

-- THEN provable (no axiom):
theorem binomial_clt_pointwise (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) (x : ℝ) :
    Filter.Tendsto
      (fun n : ℕ =>
        binomialCDF n p ((n : ℝ) * p + x * Real.sqrt ((n : ℝ) * p * (1 - p))))
      Filter.atTop (nhds (standardNormalCDF x)) := by
  -- Lemma A: Bernoulli sum has Binomial law (provable at SHA)
  -- Lemma B: invoke iid_central_limit_theorem_pinned_SHA
  -- Lemma C: Portmanteau bridge (provable at SHA, see §4)
  -- compose
  sorry
```

**Risk profile**:
- Axiom count stays at 1 (one axiom in, one axiom out — but the new axiom
  is the CLEAN CLT statement, not the post-hoc `binomial_clt_pointwise`).
- When Mathlib is later bumped to a SHA containing CentralLimitTheorem.lean,
  the new axiom can be discharged as a one-line `exact tendstoInDistribution_inv_sqrt_mul_sum …`
  and removed.
- No gallery-wide cascade; everything is local to this file.
- **LOC budget**: ~150–200 LOC research; net axiom count unchanged.
- **Caveat**: this is a *cosmetic* improvement to the axiom statement, not
  a true axiom-elimination. Honest-reporting in `meta.json` should not
  decrement `axiomCount` from 1 to 0 — but the new axiom is a much more
  defensible / Mathlib-aligned mathematical assumption.

### Option C (deferred ACT — pure pre-flight PREP)

**Plan**: do NOT push any `.lean` changes this session. Ship only this
PREP document. A future ACT session picks Option A or B with full
information; this session's contribution is the bearer audit + the
proof-skeleton drafts in §4 + §5 below.

**Risk profile**:
- Zero build risk; zero gallery cascade.
- Conflict-free with any concurrent PR on this slug (only adds
  `sessions/2026-05-15-s13-prep-clt-bearer-audit.md`).
- **LOC budget**: 0 Lean LOC.
- **Recommended for THIS session** given:
  - Deployer is stalled (~25 h since last main merge, per `git log
    origin/main --format='%h %ai' -1`).
  - 0 open PRs (per `gh pr list --state open` 2026-05-15 04:42 UTC).
  - The Mathlib-bump decision (Option A vs B) is a gallery-policy
    judgement that benefits from human review.

---

## §4 — Lemma C (Portmanteau bridge): SKELETON, provable at SHA

This lemma is the cleanest, most-modular bridge piece. It is **provable
at the lake-pinned SHA** using only B1+B2+B11 from §2. Drafted but NOT
shipped (Option C).

```lean
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Probability.Distributions.Gaussian.Real

/-- **Portmanteau CDF bridge** (provable at SHA `2df2f015...`). For any
sequence of probability measures on ℝ converging weakly to `gaussianReal 0 1`
(the standard normal, which has no atoms), the corresponding CDFs at any
real number `x` converge to `Φ(x) = (gaussianReal 0 1) (Set.Iic x)`. -/
theorem cdf_tendsto_of_inDistribution_at_gaussian
    {μs : ℕ → MeasureTheory.ProbabilityMeasure ℝ}
    (μ : MeasureTheory.ProbabilityMeasure ℝ)
    (hμ : (μ : MeasureTheory.Measure ℝ) = ProbabilityTheory.gaussianReal 0 1)
    (h_conv : Filter.Tendsto μs Filter.atTop (nhds μ))
    (x : ℝ) :
    Filter.Tendsto (fun n : ℕ => (μs n : MeasureTheory.Measure ℝ) (Set.Iic x))
      Filter.atTop (nhds ((μ : MeasureTheory.Measure ℝ) (Set.Iic x))) := by
  -- B1: ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
  -- requires E_nullbdry : μ (frontier E) = 0
  refine MeasureTheory.ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto
    h_conv ?_
  -- B2: frontier_Iic gives frontier (Iic x) = {x}
  rw [frontier_Iic]
  -- B11: noAtoms_gaussianReal gives μ {x} = 0
  rw [hμ]
  exact MeasureTheory.measure_singleton x  -- via NoAtoms instance
```

**Proof sketch + risk notes**:

- The `ProbabilityMeasure ℝ → Measure ℝ` coercion may surface
  `coe`/`toFun` elaboration choices. If `ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto`
  expects the goal phrased on `μs i E : ℝ≥0` (the NNReal-valued probability
  measure form), the wrap-up may need `simp only […]` or
  `ENNReal.toReal_eq_toReal` plumbing. Two fallback options:
  - (4a) State the lemma directly on `ProbabilityMeasure`'s NNReal-valued
    coercion (matches the `tendsto_measure_…` codomain exactly);
  - (4b) State on `ℝ≥0∞`-valued `Measure`-coerced form and apply
    `ENNReal.tendsto_toNNReal` / `ENNReal.tendsto_toReal`.
- The `NoAtoms` measure instance gives `μ {x} = 0` for any `x` via
  `measure_singleton`; for `gaussianReal 0 1` this is from `noAtoms_gaussianReal`
  (B11). The `1 : ℝ≥0` argument of the NNReal-form variance is non-zero,
  so the `h : v ≠ 0` hypothesis is satisfied by `one_ne_zero`.
- **Estimated LOC**: 25–40 (depending on which coercion form lands).

---

## §5 — Lemma A (Bernoulli→Binomial bridge): SKETCH, provable at SHA

The Bernoulli→Binomial measure bridge is the second of the two provable
pieces. It uses B13 (`PMF.binomial`) + B14 (`binomial_apply`) at SHA, plus
basic Mathlib pushforward / `PMF.toMeasure` infrastructure (also at SHA
via `Mathlib/Probability/ProbabilityMassFunction/Basic.lean`).

```lean
/-- **Bernoulli→Binomial measure bridge** (provable at SHA `2df2f015...`).
For n i.i.d. Bernoulli(p) RVs `X₁, …, Xₙ` on a product probability space,
the law of `ω ↦ ∑ i ∈ range n, Xᵢ ω` (cast to ℝ) is the pushforward of
`(PMF.binomial p _ n).toMeasure` to `ℝ`. -/
theorem bernoulli_sum_law_eq_binomial
    {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {X : Fin n → Ω → ℝ}
    (hX_law : ∀ i, ProbabilityTheory.HasLaw (X i)
                      ((PMF.bernoulli p hp).toMeasure.map ((↑) : Bool → ℝ))
                      (volume : Measure Ω))
    (hX_indep : ProbabilityTheory.iIndepFun X volume) :
    Measure.map (fun ω => ∑ i, X i ω) volume
      = (PMF.binomial p hp n).toMeasure.map (fun (k : Fin (n+1)) => (k : ℝ)) := by
  -- (sketch — combinatorial expansion via `iIndepFun.hasLaw_sum` + multinomial
  -- expansion + `PMF.binomial_apply`)
  sorry
```

**Proof sketch + risk notes**:

- The "`PMF.bernoulli`" name needs verification at SHA (gh search
  returned PMF.bernoulli at master, but pin-verify before drafting
  the ACT).
- The casting `Bool → ℝ` (true ↦ 1, false ↦ 0) interacts with
  `Measure.map` in the standard way; the fiber decomposition uses
  the same machinery already exercised in `multinomialMarginalCDF_eq_binomialCDF`
  (`Finset.sum_fiberwise_of_maps_to`).
- **Estimated LOC**: 80–150 (more complex than Lemma C; the sample-space
  construction may itself require 30–50 LOC of `MeasureSpace`/`Pi`
  scaffolding).

---

## §6 — Recommendation

**Recommend Option C for THIS session** (the present PREP file IS the
delivery). Future ACT sessions should:

1. **Decide Option A vs B with gallery-policy input**. The Mathlib-bump
   risk in Option A is real but bounded; the axiom-rebase in Option B
   keeps `axiomCount = 1` but improves the assumption's mathematical
   defensibility. Both are valid. The choice is a gallery-policy call,
   not a researcher call.

2. **Independent of A vs B, Lemma C is a free win**. Both options need
   the Portmanteau CDF bridge (§4) — it is a self-contained ~25–40 LOC
   provable theorem at the pinned SHA, with no axiom dependency. A
   sub-session ACT could land just Lemma C without committing to A vs B.

3. **Lemma A (Bernoulli→Binomial bridge, §5) is risky-but-provable at SHA**.
   The 80–150 LOC estimate has high variance because of the sample-space
   scaffolding. Recommend deferring this until after the A/B decision so
   the design choice (PMF.binomial pushforward vs. fresh `Measure ℝ`
   construction) is informed.

---

## §7 — Conflict-free guarantees

This PREP touches exactly one file: this one
(`research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03/sessions/2026-05-15-s13-prep-clt-bearer-audit.md`).

It does NOT modify:
- `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean`
- `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03/state.md`
- `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03/knowledge.md`
- `src/data/research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03.json`
- `src/data/proofs/binomial-theorem-oq-02-oq-01-oq-01-oq-03/*`
- `proofs/lake-manifest.json`
- `proofs/lakefile.toml`

It is therefore strictly conflict-free with any open or future PR on
this slug, and does not require Docker build verification.

---

## §8 — References

- `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean:370` —
  the `binomial_clt_pointwise` axiom under audit.
- `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean:165–356` —
  the standardNormalCDF + structural-CDF library (S6–S8) the
  Portmanteau bridge composes against.
- `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03/state.md:163–251`
  (S9 entry) — the original (now-broken) discharge plan referencing
  the absent `tendstoInDistribution_inv_sqrt_mul_sum`.
- `proofs/lake-manifest.json` — Mathlib pinned at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
- Mathlib master HEAD `Mathlib/Probability/CentralLimitTheorem.lean:79`
  — the master-HEAD CLT statement that would discharge `binomial_clt_pointwise`
  under Option A.
- Memory pattern `feedback_researcher_preflight_pin_verifies_peer_prep_skeleton`
  — the general pre-flight pattern this PREP instantiates.
- Memory pattern `feedback_researcher_release_crowded_slug_during_deployer_stall_pattern`
  — informs the conflict-free + doc-only choice during deployer stall.
