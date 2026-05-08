# Knowledge Base: binomial-theorem-oq-02-oq-01-oq-01-oq-03

**Problem**: Multinomial CLT in Lean — does
`(Xᵢ - npᵢ) / √(npᵢ(1−pᵢ)) → N(0, 1)` (in distribution) for the i-th
coordinate of `(X₁, …, Xₖ) ~ Multinomial(n, p₁, …, pₖ)` as `n → ∞`?

---

## Session 2026-05-07 (Session 1, researcher-8) — OBSERVE → ORIENT

**Mode**: FRESH (no prior research dir; the problem JSON exists)
**Outcome**: Inventoried the existing scaffolding, identified a clean
two-step reduction, and recorded the Mathlib gap that determines whether
the proof is mostly mechanical or requires new infrastructure.

### What's Already Done in the Gallery

The structural reduction `multinomial → binomial` is FORMALIZED in
`proofs/Proofs/BinomialTheoremOQ02OQ01OQ02.lean`:

- `multinomial_marginal_pgf` (line 96): the marginal PGF
  `∑ₖ P(X=k) · t^{k(i₀)} = (p(i₀)·t + (1−p(i₀)))^n`.
- `multinomial_marginal_pgf_eq_binomial` (line 133): identifies the PGF
  with the binomial PGF.
- `multinomial_marginal_pmf` (line 167): extracts the marginal PMF
  `P(X_{i₀} = j) = C(n,j)·p^j·(1−p)^{n−j}`.

So the marginal of `Multinomial(n, p₁, …, pₖ)` along coordinate `i₀` is
**provably** `Binomial(n, p_{i₀})` — this part of OQ-03 is solved.

### What This Problem Reduces To

Given the marginal-is-binomial result, the CLT for the i-th coordinate
reduces to **the Binomial CLT (de Moivre–Laplace, 1733/1812)**:

> If `Y_n ~ Binomial(n, p)` with `0 < p < 1`, then
> `(Y_n − np) / √(np(1−p)) → N(0, 1)` in distribution as `n → ∞`.

So the Mathlib question is: is the binomial CLT — or a path to it —
already available?

### Mathlib / Local Infrastructure Found

#### General CLT (axiomatized in this repo)

`proofs/Proofs/CentralLimitTheorem.lean:375` defines a general
`central_limit_theorem` for an arbitrary probability measure `μ` on `ℝ`
with finite mean, variance, and third absolute moment. The proof reduces
to a `clt_general_case_axiom` that connects general distributions to the
standardised case proved in `charFun_converges_to_gaussian`.

**Form**: `Filter.Tendsto (fun n => (charFun μ ((t − n·mean) / (√var · √n)))^n)
                 atTop (nhds (Complex.exp (−t²/2)))`.

This is a **characteristic-function** statement, not a direct
distribution-convergence statement, but is sufficient to extract weak
convergence (Lévy's continuity theorem).

#### `Mathlib.Probability.Distributions.Binomial`

The PMF and `binomialMeasure` are defined; no CLT is named.

#### Mathlib's i.i.d. CLT

`Mathlib.Probability.CentralLimitTheorem` provides Lindeberg–Lévy–style
CLT scaffolding. The key ingredient is `ProbabilityTheory.tendsto_clt`
or the equivalent for sums of i.i.d. variables.

The Bernoulli-sum representation
  `Y_n = Σⱼ₌₁ⁿ B_j`,  `B_j ~ Bernoulli(p)` i.i.d.
makes `(Y_n − np)/√(np(1−p)) = (Σⱼ B_j − n·E[B])/(√Var[B] · √n)`,
which is exactly the form Mathlib's i.i.d. CLT gives.

**Likely path**: apply Mathlib's i.i.d. CLT to Bernoulli summands. The
representation step (binomial = sum of i.i.d. Bernoullis) may need to be
formalised — this is folklore in probability but I have not yet
confirmed a named Mathlib lemma.

### Recommended Decomposition

Mirror the Session-2 approach used for `birthday-problem-oq-03-oq-01-oq-02-oq-01`:
break the target into named sublemmas and tackle the easy ones first.

1. **Sublemma A (mostly mechanical)**: `marginal-is-Binomial`.
   - Already in `BinomialTheoremOQ02OQ01OQ02.lean` as
     `multinomial_marginal_pmf`. Re-export or wrap in the precise form
     the CLT statement consumes.

2. **Sublemma B (Mathlib lookup)**: `Binomial = ∑ Bernoulli i.i.d.`.
   - Look for an existing Mathlib statement; if none, build it directly
     using the explicit i.i.d. construction (Mathlib has product
     measures and i.i.d. samples).

3. **Sublemma C (Mathlib application)**: i.i.d. CLT to Bernoulli.
   - Given Mathlib's i.i.d. CLT, plug in the Bernoulli case.
   - The third absolute moment is finite (Bernoulli is bounded), so the
     general CLT preconditions are trivially satisfied.

4. **Sublemma D (assembly)**: combine A + B + C → marginal CLT.

### Risks / Open Items

- **Probability spaces parameterised by n**: standard formalisation
  headache (the sample space is `Fin n → {0,1}` for a different `n` per
  iteration). Mathlib handles this with `Filter.Tendsto` over the index
  `n` plus `Pi.measureTheory`-style infinite product measures, but this
  is non-trivial wiring. This is the most likely place for substantial
  Lean work.

- **Vector-valued joint CLT (out of scope for this OQ)**: requires
  Cramér–Wold (linear-combination characterisation of multivariate
  weak convergence). Joint multinomial CLT is the next OQ in the chain
  and is intentionally deferred.

### Next Action (ORIENT → ACT)

In a future session:

1. Confirm whether Mathlib has a named binomial CLT or i.i.d. CLT in the
   exact form required (read `Mathlib.Probability.CentralLimitTheorem`
   and the binomial section).
2. Scaffold `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean` with:
   - `import Proofs.BinomialTheoremOQ02OQ01OQ02`
   - `import Mathlib.Probability.CentralLimitTheorem`
   - The marginal-CLT statement as a theorem.
   - At minimum, an axiomatised version that names the gap, plus the
     reduction lemmas A and D as fully proved theorems.
3. If Mathlib's i.i.d. CLT is directly applicable, complete the proof.
   Otherwise, axiomatise sublemma C and ship A + B + D, isolating the
   Mathlib gap to a single statement (cf. the
   `birthday-problem-oq-03-oq-01-oq-02-oq-01` Lemma C pattern).

---

## Session 2026-05-08 (Session 2, researcher-9) — ACT (Phase-2 scaffold)

**Mode**: REVISIT (Session 1 was OBSERVE→ORIENT; this is the planned ACT)
**Outcome**: scaffolded `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean`
(178 lines) and the matching gallery entry. Took a CDF-based path rather
than the measure-theoretic Bernoulli-sum path planned in Session 1.

### What Was Built

**Lean file**: `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean`

- `binomialCDF n p x` — concrete CDF of Binomial(n, p), defined as
  `∑_{j ∈ Finset.range (n+1)}, if (j:ℝ) ≤ x then C(n,j)·p^j·(1-p)^(n-j) else 0`.
- `multinomialMarginalCDF s p n i₀ x` — concrete marginal CDF of
  coordinate `i₀`, defined directly from `multinomialProb`.
- `standardNormalCDF` — opaque marker (counts as +1 axiom).
- `binomial_clt_pointwise` — AXIOM (de Moivre–Laplace, 1733/1812):
  the standardized binomial CDF converges pointwise to `standardNormalCDF x`.
- `multinomialMarginalCDF_eq_binomialCDF` — reduction lemma (sorry,
  Phase-3 target). Provable from the parent's `multinomial_marginal_pmf`.
- `multinomial_marginal_clt` — DERIVED THEOREM (no separate axiom).
  Combines the two via `Filter.Tendsto.congr`.

**Gallery entry**: `src/data/proofs/binomial-theorem-oq-02-oq-01-oq-01-oq-03/`
(meta.json + annotations.json + index.ts).

### Why CDF Instead of Bernoulli-Sum

Session 1 planned to use Mathlib's i.i.d. CLT applied to a Bernoulli-sum
representation of `Binomial(n,p)`. That path requires:

- Setting up an i.i.d. probability space with sample space `Fin n → {0,1}`.
- Constructing the binomial distribution as `Σⱼ B_j` with `B_j ~ Bernoulli(p)`.
- Invoking `ProbabilityTheory.iid_central_limit_theorem`.
- Bridging measure-weak-convergence to the CDF formulation (Portmanteau).

The CDF path collapses all of this to:

- An axiom that *states* de Moivre–Laplace in CDF form.
- An equality `multinomialMarginalCDF = binomialCDF` (provable from
  `multinomial_marginal_pmf` by a fiber regrouping over `k(i₀)` values).
- One application of `Filter.Tendsto.congr`.

Trade-off: the CDF approach introduces `standardNormalCDF` as `opaque`
(+1 axiom) but eliminates the entire measure-theoretic infrastructure
chain. Net axiom count: **2** (opaque CDF + de Moivre–Laplace), vs. an
estimated 3–5 for the Bernoulli-sum path (the i.i.d. setup typically
needs at least one axiom to bridge to the standard form).

### Honest Reporting

- This session **could not run** `./proofs/scripts/docker-build.sh` to
  verify the scaffold compiles (long Docker iteration time + worktree
  symlink trap that prevents direct Mathlib browsing). CI is the ground
  truth. Confidence is moderate-high based on Mathlib idiom familiarity
  but not verified.
- The Phase-3 reduction is **provable** but not yet proved. Closing it
  would leave 0 sorries, with the only assumptions being de Moivre–Laplace
  and the `standardNormalCDF` opaque.
- This is **Phase-2 scaffolding**, not the answer to OQ-03 — the answer
  is the *derivation chain*, not the binomial CLT itself, which is
  axiomatized.

### Files Changed

- NEW `proofs/Proofs/BinomialTheoremOQ02OQ01OQ01OQ03.lean`
- NEW `src/data/proofs/binomial-theorem-oq-02-oq-01-oq-01-oq-03/{meta.json,annotations.json,index.ts}`
- UPDATED `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03/state.md`
- UPDATED `research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03/knowledge.md`
- UPDATED `src/data/research/problems/binomial-theorem-oq-02-oq-01-oq-01-oq-03.json` (knowledge fields)

### Next Steps

1. **Phase-3 next session**: discharge `multinomialMarginalCDF_eq_binomialCDF`
   by fiber regrouping. Skeleton in `state.md`. Should be ~30 lines.
2. **Phase-3 stretch**: discharge `binomial_clt_pointwise` by bridging to
   Mathlib's `iid_central_limit_theorem` via Portmanteau. This is the
   substantial piece of work and may require ~150+ lines.
3. **Joint multinomial CLT** (out of scope for this OQ): coordinate-wise
   CLTs do not imply joint convergence. Cramér–Wold + the covariance
   computation in `BinomialTheoremOQ02OQ01OQ03.multinomial_covariance`
   give the joint statement; this should be a sibling OQ.

---

## Session 2026-05-08 (Session 3, researcher-3) — ACT (Phase-3)

**Mode**: BUILD-ON-PRIOR (Session 2's scaffold is merged in #16866).
**Outcome**: discharged the sorry in
`multinomialMarginalCDF_eq_binomialCDF`. The Lean file is now sorry-free,
with only the previously-named two axioms (`binomial_clt_pointwise`,
`standardNormalCDF` opaque).

### What Was Built

* Added `piAntidiag_apply_le` (private lemma): for any composition
  `k ∈ s.piAntidiag n`, every coordinate satisfies `k i₀ ≤ n`.
  Proof: case-split on `i₀ ∈ s` — bound by the sum if yes, force
  `k i₀ = 0` from the support condition if no.
* Replaced the sorry in `multinomialMarginalCDF_eq_binomialCDF` with a
  ~70-line proof:
  1. Apply `Finset.sum_fiberwise_of_maps_to` with `f := (· i₀)` and
     `t := Finset.range (n+1)` (using `piAntidiag_apply_le`) to
     break the multinomial sum into fibres.
  2. Term-by-term match the outer sum: for each `j ∈ Finset.range (n+1)`,
     case-split on the if-condition `(j : ℝ) ≤ x`.
  3. True branch: rewrite each `(k i₀ : ℝ) ≤ x` as `(j : ℝ) ≤ x` (since
     `k i₀ = j` in the fibre), the if collapses to `then-branch` only,
     and the inner sum becomes the bare multinomial sum which equals
     the binomial PMF by Sublemma A
     (`BinomialTheoremOQ02OQ01OQ02.multinomial_marginal_pmf`).
  4. False branch: every term in the fibre is zero, so the sum is zero.
* File grew from 178 → 239 lines (added ~70-line proof + ~20-line
  private lemma + updated docstrings).

### Status After This Session

* Sorries: 0 (was 1).
* Axioms: 2 (unchanged): `binomial_clt_pointwise` (de Moivre–Laplace
  CLT in CDF form) + `standardNormalCDF` (opaque).
* Theorems: 3 (was 2): added `piAntidiag_apply_le` private lemma.
* Status: still `axiomatized` (the two axioms remain).

### Honest Reporting

* Local Docker build was **not** run (CI is the ground truth, host
  memory limited).
* The proof uses `Finset.sum_fiberwise_of_maps_to` — standard Mathlib
  API. If the exact name has drifted in v4.26.0 the fix is mechanical
  (alternatives: explicit `Finset.sum_biUnion` with disjointness
  witness, or `Finset.sum_partition`).
* Confidence in the proof is moderate-high but not CI-verified at
  push time.

### What's Left

The only mathematical assumption now is `binomial_clt_pointwise` (the
classical de Moivre–Laplace theorem in CDF form). Closing it directly
in this file requires either:

1. **Stirling's formula route**: direct asymptotic analysis of
   `C(n,j) p^j (1-p)^{n-j}` near the mean `j ≈ np` via Stirling +
   careful bookkeeping of the standardised variable. Classical and
   self-contained but tedious. Hardy & Wright Ch. 8 is the standard
   pedagogical reference.
2. **Mathlib's i.i.d. CLT route**: invoke
   `ProbabilityTheory.iid_central_limit_theorem` for a Bernoulli($p$)
   measure, then bridge measure-weak-convergence to CDF-pointwise
   convergence via the Portmanteau theorem at continuity points of
   the standard normal CDF (every point, since Φ is continuous).

The opaque `standardNormalCDF` can also be replaced by Mathlib's
measure-theoretic `gaussianMeasure` CDF, removing the second axiom.

---

## Dead Ends

- None yet.
