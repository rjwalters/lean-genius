# Knowledge Base: borsuk-ulam-oq-02-oq-01-oq-01-oq-01

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

### Survey 2026-07-05 (researcher-6) — BLOCKED: target is logically independent of the infrastructure

The problem asks: prove the upper bound `buDim(n,d) ≤ buDimFormula(n,d)` (i.e. discharge the
axiom `buDim_le_formula`, `BorsukUlamOQ02OQ01OQ01.lean:60`) using the Fadell-Husseini index from
`BorsukUlamOQ02OQ01OQ04.lean`. It cannot be done from present infrastructure, for two independent
reasons:

1. **`buDim` is an opaque axiom.** `BorsukUlamOQ02OQ01.lean:52` declares
   `axiom buDim (n d : ℕ) : ℕ`, with the only characterizing axioms being
   `buDim_two` (Z/2 case), `buDim_prime` (prime case), and `buDim_mono` (divisor monotonicity).
   These pin down prime and monotone behaviour but **do not determine composite-`n` values**: one
   can define a function satisfying all three axioms yet violating the composite upper bound. Hence
   `buDim_le_formula` is **logically independent** of the axioms already in play — it is not derivable,
   which is precisely why the file states it as an axiom labelled *OPEN CONJECTURE*.

2. **The cited Fadell-Husseini file is a toy, with no bridge to `buDim`.**
   `BorsukUlamOQ02OQ01OQ04.lean` defines `CohRing` / `FHIndex` (`minPower : Option ℕ`) and proves
   `fh_point` / `fh_sphere_free_action` by `rfl` on that toy structure. Its only lemmas that mention
   `buDim` (`fh_implies_buDim_lower_bound`, `fh_recovers_yang_borsuk`, the FH monotonicity restatement)
   simply **re-wrap the parent axioms** `buDim_prime` / `buDim_mono`. There is no equivariant
   cohomology `H*(BG;F_p)`, no index ideal, no restriction/localization map — nothing that could
   discharge the composite upper bound. "Prove the upper bound via the FH index" has no substance to
   build on here.

---

## Dead Ends

- Deriving `buDim_le_formula` from `buDim_two` / `buDim_prime` / `buDim_mono`: impossible — the
  target is logically independent of these (see Insight 1).
- Using `BorsukUlamOQ02OQ01OQ04.lean`'s "Fadell-Husseini index" as-is: it is a decorative
  `Option ℕ` structure with no cohomological content; its buDim lemmas only echo existing axioms.

## Verdict: BLOCKED

A genuine proof requires (a) a **real** Fadell-Husseini index — equivariant cohomology
`H*(BG;F_p)` for cyclic `G`, the index ideal, restriction/localization, Smith theory — which is
>1000 lines of foundational equivariant topology absent from Mathlib 4.26; **and** (b) the general
statement (arbitrary representations, general composite `n`) is **open in the literature** (only
`p^k` via Smith theory and standard complex representations via Yang-Borsuk lifting are known, per
the axiom's own docstring). No scaffolding was added on top of the open axiom. Depth-4 OQ chain →
0 follow-up questions (OQ-depth guard).
