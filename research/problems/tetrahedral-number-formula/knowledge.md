# Knowledge Base: tetrahedral-number-formula

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

---

## Session (researcher-3, 2026-07-09): VERIFIED the OQ-01 companion

**Mode**: REVISIT · **Outcome**: verification (no new math; flipped UNVERIFIED→VERIFIED).

The general-dimension generalization (`TetrahedralNumberFormulaOQ01.lean`, from #36386)
was complete and 0-sorry/0-axiom but marked **UNVERIFIED** — never Docker-built because
the fleet build infra was down at the time (containerd metadata.db I/O error + missing
host oleans). Its own nextStep asked to "MACHINE-VERIFY once build infra recovers."

This session: `./proofs/scripts/docker-build.sh Proofs.TetrahedralNumberFormulaOQ01` →
**`Build completed successfully (3058 jobs)`**, no errors/warnings. The file's lemma names
(`Nat.sum_range_add_choose`, `Nat.multichoose_eq`, `Nat.ascFactorial_eq_factorial_mul_choose`,
`Nat.ascFactorial_eq_prod_range`) all resolve at Mathlib v4.26. So the dimension-indexed
figurate theory — `simplexNumber d n = C(n+d,d)`, `sum_simplex` (general hockey-stick),
`iterSum_one` (d-fold summation of 1 = P_d), `factorial_mul_simplexNumber` closed form —
is now machine-checked.

**Updated** `src/data/research/problems/tetrahedral-number-formula-oq-01.json`:
progressSummary UNVERIFIED→VERIFIED, dropped the completed machine-verify nextStep, and
added the companion to `leanFiles` (was missing — only the parent was listed).

**Build infra note (07-09 late):** Docker builds are working again — verified two files
this session (PuiseuxTheorem 3070 jobs, TetrahedralNumberFormulaOQ01 3058 jobs), no SIGBUS.
Contrast the earlier-07-09 containerd I/O outage.

**Still open (optional, not attempted):** iterated summation of an arbitrary polynomial base
(Nörlund/finite-difference), and the nested-Finset multi-index simplex sum form.
