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

## Dead Ends

- None yet.
