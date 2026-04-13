# Knowledge Base: newton-inductive-step-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

Newton's inequality: for nonneg reals x₁,...,xₙ, the elementary symmetric means ē_k = e_k/C(n,k) satisfy ē_k² ≥ ē_{k-1}·ē_{k+1}. This is the log-concavity of the ē sequence.

---

## Insights

- The recurrence e_k(x::xs) = e_k(xs) + x·e_{k-1}(xs) gives a natural list-based definition in Lean 4
- Log-concavity of binomial coefficients is a clean special case (all xᵢ = 1)
- Absorption identity approach: C(n,k-1)·C(n,k+1) = k(n-k)/((n-k+1)(k+1))·C(n,k)² and k(n-k) ≤ (n-k+1)(k+1)
- Small cases (n=2,3) reduce to sum-of-squares and nlinarith handles them directly
- The general inductive step requires Cauchy-Schwarz on the two-term recurrence — significant polynomial bookkeeping
- The parent proof (NewtonInductiveStep.lean) provides the binomial inequality used in the inductive step

---

## Built Items

- `proofs/Proofs/NewtonInductiveStepOQ01.lean`: 18 theorems, 2 defs, 0 axioms, 2 sorries
- `src/data/proofs/newton-inductive-step-oq-01/`: Full gallery entry
- PR #8359

---

## Dead Ends

- Direct expansion of the general case without absorption identities leads to unmanageable polynomial expressions
- MvPolynomial.esymm from Mathlib is multivariate polynomial-valued, not directly evaluable on real lists — custom esymm definition is cleaner for this purpose

---

## Progress Summary

Formalized Newton's inequality for elementary symmetric polynomials. Proved log-concavity of binomial coefficients, explicit n=2,3 cases, first Maclaurin inequality, and AM-GM connection. General inductive proof stated with 2 sorries.
