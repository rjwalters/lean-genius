# Knowledge Base: erdos-227-wip-01

Insights accumulated during research on this problem.

---

## Problem Understanding

Erdős #227 (SOLVED/DISPROVED, Clunie–Hayman 1964): the limit of μ(r)/M(r) can be
any λ ∈ [0, 1/2]. `Erdos227Problem.lean` formalizes the statement with 3 axioms
(all person-named, deep: `clunie_positive_coeffs`, `clunie_hayman_1964`,
`ratio_upper_bound`) and 1 sorry (`positive_coeffs_normal` — needs the
*existence* of the limit for non-negative coefficients, which is the analytic
heart of Clunie's unpublished theorem).

Key structural fact: the `EntireFunction` structure records only coefficients and
imposes NO convergence. Divergent members hit Mathlib junk values (`tsum = 0`,
unbounded `Real.iSup = 0`), making `termModulusRatio` identically 0 for large r,
so the axioms stay sound over the weak structure (junk regime forces L = 0).

---

## Insights

- **Session 2026-07-22 (researcher-1)**: Added Part 11 — 13 axiom-free theorems
  (`#print axioms` = propext/Classical.choice/Quot.sound only):
  - `IsEntire` predicate (absolute summability at every radius) fixes the
    structure's missing-convergence gap; theorems take it as hypothesis.
  - μ(r) ≤ M(r) for non-negative real coefficients
    (`maxTerm_le_maxModulus_of_nonneg`): no Cauchy integral needed — each term
    aₙrⁿ is a summand of the non-negative series f(r), which is the θ=0 member
    of the family defining M(r).
  - `termModulusRatio_le_one_of_nonneg`, `limit_mem_Icc_of_nonneg`: any ratio
    limit lies in [0,1] — elementary companion to the deep axiomatized L ≤ 1/2
    and L = 0.
  - `expFunction` (coeffs 1/n!) with `expFunction_isEntire`: concrete witness
    via `Real.summable_pow_div_factorial`.
- Lean idioms: `Complex.ofReal_tsum` (NOT `RCLike.ofReal_tsum`) matches goals
  whose coercion elaborated as `Complex.ofReal`; `conv_lhs => rw [...]` needed
  when a coefficient-rewrite would also fire inside `‖·‖` on the RHS;
  `ciSup_le`/`le_ciSup` handle the `Real.iSup` definitions (`le_ciSup` needs
  `BddAbove (Set.range ...)`, provided by the triangle-inequality bound).

---

## Dead Ends

- Proving any of the 3 axioms or the sorry from Mathlib: Wiman–Valiron theory
  (maximum term, central index) and the Clunie/Clunie–Hayman constructions are
  entirely absent. Do NOT re-attempt without new Mathlib infrastructure
  ("materially new mechanism required").
- Do not "close" the sorry by adding a limit-existence axiom — that inflates the
  axiom count for no verification gain.

---

## Open Next Steps

- OPTIONAL (~300–500 lines): bridge `EntireFunction`+`IsEntire` to Mathlib's
  `HasFPowerSeriesOnBall`/`FormalMultilinearSeries` API and prove the
  unconditional Cauchy estimate μ(r) ≤ M(r) (arbitrary complex coefficients).
- DEEP (blocked): sorry elimination and axiom elimination.
