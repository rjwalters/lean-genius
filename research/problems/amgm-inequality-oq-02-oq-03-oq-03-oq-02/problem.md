# Problem: Extend Maclaurin Chain Theorem to Non-Negative Reals Without Strict Positivity

**Slug**: amgm-inequality-oq-02-oq-03-oq-03-oq-02
**Created**: 2026-04-05
**Status**: Active
**Source**: gallery-gap

## Problem Statement

### Formal Statement

$$
\text{For } n \geq 1, \text{ non-negative reals } x_1, \ldots, x_n \geq 0, \text{ and } 1 \leq j \leq k \leq n:
\quad M_j \geq M_k
$$

where $M_k = \left(\frac{e_k(x)}{\binom{n}{k}}\right)^{1/k}$ and $e_k$ is the $k$-th elementary symmetric polynomial.

### Plain Language

Prove the full Maclaurin inequality chain $M_1 \geq M_2 \geq \cdots \geq M_n$ with 0 axioms (or at most the `newton_log_concavity` axiom), using the proved version of the step inequality from `AmgmInequalityOQ02OQ03.lean`.

The parent file `AmgmInequalityOQ02OQ03OQ03.lean` proves the chain but imports from `AmgmInequalityOQ02` which carries two axioms:
- `newton_log_concavity` (deep inductive result — hard, kept as axiom)
- `maclaurin_step` (follows from Newton log-concavity — already proved in OQ02OQ03!)

This problem asks to wire in `maclaurin_step_proved` from `AmgmInequalityOQ02OQ03`, eliminating the redundant `maclaurin_step` axiom.

### Why This Matters

The result reduces the axiom count from 2 to 1 for the full Maclaurin chain, improving the verified status. It also demonstrates that the chain holds for all non-negative inputs (not just strictly positive ones), since `maclaurin_step_proved` carefully handles the zero boundary case via a case split.

## Known Results

### What's Already Proven

- `AmgmInequalityOQ02OQ03.lean` proves `maclaurin_step_proved` from `newton_log_concavity` — same signature as the `maclaurin_step` axiom but as a theorem.
- `AmgmInequalityOQ02OQ03OQ03.lean` proves `maclaurin_full_chain` using `maclaurin_step` (axiom). The proof uses a simple induction on the gap `d = k - j`.
- `maclaurin_step_proved` uses `hx : ∀ i, 0 ≤ x i` (non-negative, not strict positivity).
- The `power_inequality` lemma in OQ02OQ03 handles the case `normElemSymm (k+1) x = 0` with a `by_cases` split.

### What's Still Open

- Replacing the `maclaurin_step` axiom with `maclaurin_step_proved` in the full chain proof.
- Producing a version of `maclaurin_full_chain` and `maclaurin_m1_ge_mn` with no reference to the `maclaurin_step` axiom.

### Our Goal

Create `AmgmInequalityOQ02OQ03OQ03OQ02.lean` that:
1. Imports `AmgmInequalityOQ02OQ03` (which has `maclaurin_step_proved`)
2. Uses `maclaurin_step_proved` in place of `maclaurin_step`
3. Proves the same theorems as OQ02OQ03OQ03 with 1 axiom (newton_log_concavity) instead of 2

## Related Gallery Proofs

| Proof | Relevance | Techniques |
|-------|-----------|------------|
| amgm-inequality-oq-02-oq-03-oq-03 | Direct parent — uses maclaurin_step axiom | Induction on gap |
| amgm-inequality-oq-02-oq-03 | Provides maclaurin_step_proved | Newton log-concavity, rpow monotonicity |
| amgm-inequality-oq-02 | Defines maclaurinMean, elemSymm | Elementary symmetric polynomials |

## Initial Thoughts

### Potential Approaches

1. **Direct substitution**: Copy OQ02OQ03OQ03, replace `import Proofs.AmgmInequalityOQ02` with `import Proofs.AmgmInequalityOQ02OQ03`, and replace calls to `maclaurin_step` with `AmgmInequalityOQ02OQ03.maclaurin_step_proved`. Should require minimal changes.

2. **Re-export approach**: Import both files, prove the chain using the proved step, and verify the axiom count drops to 1.

### Key Difficulties

- Namespace resolution: `maclaurin_step_proved` lives in `AmgmInequalityOQ02OQ03` namespace, while the definitions (`maclaurinMean`, etc.) live in `AmgmInequalityOQ02` or the root namespace. May need `open` statements.
- The parent OQ02OQ03OQ03 has `variable {n : ℕ}` — keep the same structure.

### What Would a Proof Need?

- Correct import: `import Proofs.AmgmInequalityOQ02OQ03`
- Access to `maclaurinMean` and its definition (from AmgmInequalityOQ02)
- Call `AmgmInequalityOQ02OQ03.maclaurin_step_proved` in the inductive step

## Tractability Assessment

**Difficulty**: Low

**Justification**:
- This is essentially a re-wire, not a new mathematical proof.
- The inductive argument is already written in OQ02OQ03OQ03.
- The key substitution is `maclaurin_step` → `maclaurin_step_proved`, which has the same type signature.
- The main risk is namespace/import complexity in Lean 4.

**Estimated Effort**:
- Exploration: 1–2 hours to understand the import chain
- If tractable: 2–4 hours to write and verify

## References

### Lean Files
- `proofs/Proofs/AmgmInequalityOQ02OQ03OQ03.lean` — parent proof (copy as starting point)
- `proofs/Proofs/AmgmInequalityOQ02OQ03.lean` — has `maclaurin_step_proved`
- `proofs/Proofs/AmgmInequalityOQ02.lean` — definitions: `maclaurinMean`, `elemSymm`

### Gallery Entries
- `src/data/proofs/amgm-inequality-oq-02-oq-03-oq-03/meta.json` — parent (1 axiom)
- `src/data/proofs/amgm-inequality-oq-02-oq-03/meta.json` — step proved here

## Metadata

```yaml
tags:
  - analysis
  - inequalities
  - generalization
  - maclaurin
  - elementary-symmetric-polynomials
related_proofs:
  - amgm-inequality-oq-02-oq-03-oq-03
  - amgm-inequality-oq-02-oq-03
difficulty: low
source: gallery-gap
created: 2026-04-05
```
