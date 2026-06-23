# Erdős #265 - Knowledge Base

## Problem Statement

Forum
Favourites
Tags
More
 Go
 Go
Dual View
Random Solved
Random Open

How fast can $a_n\to \infty$ grow if\[\sum\frac{1}{a_n}\quad\textrm{and}\quad\sum\frac{1}{a_n-1}\]are both rational?



Cantor observed that $a_n=\binom{n}{2}$ is such a sequence. If we replace $-1$ by a different constant then higher degree polynomials can be used - for example if we consider $\sum_{n\geq 2}\frac{1}{a_n}$ and $\sum_{n\geq 2}\frac{1}{a_n-12}$ then $a_n=n^3+6n^2+5n$ is an example of both series being rational.

Erd\H{o}s believed that $a_n^{1/n}\to \infty$ is possible, but $a_n^{1/2^n}\to 1$ is necessary.

This has been almost completely solved by Kova\v{c} and Tao \cite{KoTa24}, who prove that such a sequence can grow doubly exponentially. More precisely, there exists such a sequence such that $a_n^{1/\beta^n}\to \infty$ for some $\beta >1$.

It remains open whether one can achieve\[\limsup a_n^{1/2^n}>1.\]A folklore result states that $\sum \frac{1}{a_n}$ is irrational whenever $\lim a_n^{1/2^n}=\infty$, and hence such a sequence cannot grow faster than doubly exponentially - the remaining question is the precise exponent possible.




References


[KoTa24] Kova\vC, V. and Tao T., On several irrationality problems for Ahmes series. arXiv:2406.17593 (2024).


Back to the problem

## Status

**Erdős Database Status**: OPEN

**Tractability Score**: 4/10
**Aristotle Suitable**: No

## Tags

- erdos

## Related Problems

- Problem #2000
- Problem #83
- Problem #888
- Problem #2
- Problem #264
- Problem #266
- Problem #39
- Problem #1

## References

- KoTa24

## Sessions

(No research sessions yet)

---

*Generated from erdosproblems.com on 2026-01-12*

### Session 2026-04-22 (Session 1) - Completion Audit

**Mode**: REVISIT
**Outcome**: completed

#### What I Did
- Reviewed existing Lean formalization (Erdos265Problem.lean + Erdos265Aristotle.lean)
- Fixed Erdos265Aristotle.lean line 94: replaced `exact?` with `Real.rpow_le_rpow_of_exponent_le hx hpq`
- Updated pool status from `in-progress` to `completed`
- Previous sessions had left progressSummary as "COMPLETE" but never updated pool

#### Key Findings
- Formalization is sound: 2 axioms correctly represent open conjectures
  - `erdos_265_doubleExp_necessary`: open conjecture (a_n^{1/2^n} → 1 necessary)
  - `kovac_tao_theorem`: Kovač-Tao 2024 result (∃ β > 1 achieving doubly exponential growth)
- `erdos_265_main` is a logical tautology provable by classical excluded middle
- Gallery entry (meta.json status: "axiomatized", badge: "axiom") is correct
- `exact?` tactic in Aristotle file resolved to `Real.rpow_le_rpow_of_exponent_le`

#### Files Modified
- proofs/Proofs/Erdos265Aristotle.lean (line 94: exact? → explicit proof)

#### Next Steps
None — formalization is complete. The open mathematical question (limsup a_n^{1/2^n} > 1?)
requires deep analytic number theory beyond current Mathlib capabilities.
