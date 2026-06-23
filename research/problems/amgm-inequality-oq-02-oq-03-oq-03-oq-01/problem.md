# Problem: Maclaurin Chain via Mathlib Symmetric Functions

**Slug**: amgm-inequality-oq-02-oq-03-oq-03-oq-01
**Created**: 2026-04-05
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{Can } \texttt{maclaurin\_step} \text{ be proved from } \texttt{Mathlib.RingTheory.MvPolynomial.NewtonIdentities}
$$
$$
\text{without the Newton log-concavity route?}
$$

More precisely: prove `maclaurin_step` — that the k-th Maclaurin symmetric mean satisfies
$$M_k \geq M_{k+1}$$
where $M_k = \left(\frac{e_k(x)}{\binom{n}{k}}\right)^{1/k}$,
using Mathlib's algebraic Newton identity infrastructure rather than log-concavity.

### Plain Language

The Maclaurin chain $M_1 \geq M_2 \geq \cdots \geq M_n$ (which generalizes AM-GM) has a key step: `maclaurin_step k` proves $M_k \geq M_{k+1}$. The current proof goes via log-concavity: Newton's inequality $e_k^2 \geq e_{k-1} \cdot e_{k+1}$ (proved combinatorially), then an inductive power argument.

The open question is whether Mathlib's `MvPolynomial.NewtonIdentities` — which expresses $k \cdot e_k = \sum_{i=1}^{k} (-1)^{i-1} e_{k-i} p_i$ (Newton's power-sum identities) — can provide an alternative, more algebraic proof path.

### Why This Matters

Two reasons:
1. **Alternative proof architecture**: A proof via Newton identities would be more algebraic and potentially generalize to other symmetric function contexts.
2. **Mathlib integration**: It would demonstrate that Mathlib's `MvPolynomial.NewtonIdentities` machinery is powerful enough to derive Maclaurin inequalities directly, strengthening the bridge between the algebraic (power sums) and analytic (mean inequalities) perspectives.

## Known Results

### What's Already Proven

- `maclaurin_step_proved` — Proved in `AmgmInequalityOQ02OQ03.lean` via:
  1. Newton log-concavity: $a_k^2 \geq a_{k-1} \cdot a_{k+1}$ (where $a_k = e_k/\binom{n}{k}$)
  2. Power induction: $a_k^{k+1} \geq a_{k+1}^k$
  3. Monotonicity of `rpow` to conclude $M_k \geq M_{k+1}$

- Mathlib has `MvPolynomial.NewtonIdentities` in `Mathlib.RingTheory.MvPolynomial.NewtonIdentities`
  — The Newton power-sum identities $p_k = \sum_{i=1}^k (-1)^{i-1} e_{k-i} p_i / e_0$

### What's Still Open

- Whether Newton's power-sum identities directly imply log-concavity of $e_k$
- Whether there's a cleaner algebraic path from Newton identities to `maclaurin_step`
- Whether the Mathlib `MvPolynomial` framework (over an arbitrary commutative ring) is compatible with the analytic inequality setting (over `ℝ` with positivity)

### Our Goal

Produce a new file `AmgmInequalityOQ02OQ03OQ03OQ01.lean` (or a new theorem in an existing file) that proves `maclaurin_step` using `Mathlib.RingTheory.MvPolynomial.NewtonIdentities` as the primary algebraic engine, without relying on the log-concavity induction in `AmgmInequalityOQ02OQ03.lean`.

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| `amgm-inequality-oq-02-oq-03-oq-03` | Parent: Full Maclaurin chain using `maclaurin_step` | Induction on index gap |
| `amgm-inequality-oq-02-oq-03` | Proves `maclaurin_step` via log-concavity | Newton log-concavity, rpow monotonicity |
| `amgm-inequality-oq-02` | Base AM-GM, defines `maclaurin_step` as axiom | Symmetric means, Finset |
| `amgm-inequality-oq-03` | Alternative AM-GM approaches | Various |

## Initial Thoughts

### Potential Approaches

1. **Newton identities → log-concavity**: Use Newton identities to first re-derive log-concavity $e_k^2 \geq e_{k-1} \cdot e_{k+1}$, then apply existing power induction.
   - Why it might work: Newton identities constrain $e_k$ via $p_k$; positivity of $p_k$ for positive inputs might force log-concavity
   - Risk: May require substantial positivity transfer between `MvPolynomial` and `ℝ`-valued symmetric polynomials

2. **Direct power-mean inequality from Newton identities**: Apply Newton identities to bound power sums, then relate to means $M_k$ directly.
   - Why it might work: Power means and power sums are closely related; $M_k^k \cdot \binom{n}{k} = e_k(x)$
   - Risk: The translation from formal polynomial identities to real-valued inequalities may be nontrivial

3. **Schur-concavity approach**: Newton identities imply that $e_k$ is Schur-concave; Maclaurin's inequalities follow from majorization.
   - Why it might work: Clean framework, well-known in combinatorics
   - Risk: Schur-concavity may not be formalized in Mathlib yet

### Key Difficulties

- The `MvPolynomial.NewtonIdentities` module works over a generic commutative ring; extracting real-number inequalities requires specialization and positivity arguments
- The existing proof (`AmgmInequalityOQ02OQ03.lean`) uses `elemSymm` (a custom definition), while Mathlib uses `MvPolynomial.esymm` — a compatibility layer may be needed
- Mathlib's Newton identities are algebraic identities, not inequalities; getting inequalities from them requires positivity of the variables

### What Would a Proof Need?

- Key lemma 1: Relate `elemSymm k x` (custom) to `MvPolynomial.esymm σ R k` evaluated at `x`
- Key lemma 2: Specialize Newton identities to `ℝ` with non-negative inputs
- Key lemma 3: Extract log-concavity from Newton identities + positivity, or find a direct route

## Tractability Assessment

**Difficulty**: Medium-High

**Justification**:
- The math is understood: Newton identities → log-concavity is a known path in combinatorics texts
- The Lean challenge: bridging `MvPolynomial` (formal, over any ring) to `ℝ`-valued inequalities is nontrivial API work
- Partial success is valuable: even connecting `MvPolynomial.esymm` to our `elemSymm` would be useful infrastructure

**Estimated Effort**:
- Exploration (checking Mathlib API): 1-2 hours
- If connection is direct: 1 day
- If requires new bridge lemmas: 2-5 days

## References

### Papers
- Hardy, Littlewood, Pólya "Inequalities" (1934) §2.22 — Maclaurin chain proof via AM-GM iteration
- Newton, I. (1707): Original power-sum identities (Arithmetica Universalis)

### Mathlib
- `Mathlib.RingTheory.MvPolynomial.NewtonIdentities` — Newton's identities for elementary symmetric polynomials and power sums
- `Mathlib.Algebra.BigOperators.Ring` — BigOperators for finset products/sums
- `Mathlib.Analysis.MeanInequalities` — Power mean inequalities in Mathlib

### Local Files
- `proofs/Proofs/AmgmInequalityOQ02OQ03.lean` — Current proof of `maclaurin_step_proved` via log-concavity
- `proofs/Proofs/AmgmInequalityOQ02OQ03OQ03.lean` — Full chain using `maclaurin_step`
- `proofs/Proofs/AmgmInequalityOQ02Defs.lean` — Definitions of `elemSymm`, `maclaurinMean`

## Metadata

```yaml
tags:
  - inequalities
  - symmetric-functions
  - combinatorics
  - analysis
  - maclaurin
related_proofs:
  - amgm-inequality-oq-02-oq-03-oq-03
  - amgm-inequality-oq-02-oq-03
  - amgm-inequality-oq-02
difficulty: medium-high
source: gallery-gap
created: 2026-04-05
```

**Significance**: 7/10
**Tractability**: 7/10
