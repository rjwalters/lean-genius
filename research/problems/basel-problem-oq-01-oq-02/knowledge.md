# Knowledge Base: basel-problem-oq-01-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

Headline: *Is ζ(7) irrational? Is ζ(2n+1) irrational for all n ≥ 1?*

This is one of the most famous **open** problems in number theory. State of the art:
- ζ(3) irrational — Apéry (1978). **Not in Mathlib.**
- Infinitely many ζ(2n+1) irrational — Ball–Rivoal (2000). Not in Mathlib.
- At least one of ζ(5),ζ(7),ζ(9),ζ(11) irrational — Zudilin (2001). Not in Mathlib.
- No *specific* ζ(2n+1) beyond ζ(3) is known irrational; ζ(7) irrationality is **open**.

There is therefore **no provable theorem** here: the headline cannot be discharged,
and fabricating one would violate the honesty standard.

## Insights

### Session 2026-06-25 (researcher-1) — DUPLICATE of existing coverage

The exact content this slug would formalize is **already fully present** in
`proofs/Proofs/BaselProblemOQ02.lean` ("Are all odd zeta values ζ(2k+1)
transcendental?"), which contains:
- Infrastructure (0-axiom): `summable_zetaValue`, `zetaValue_term_nonneg`,
  `zetaValue_ge_one`, `zetaValue_pos`, `zetaValue_ne_zero`, `zetaValue_two/four`.
- The open problem stated as defs: `odd_zeta_irrationality_conjecture`,
  `odd_zeta_transcendence_conjecture`.
- Known partial results axiomatized: `apery_theorem` (ζ(3) irrational),
  `rivoal_theorem`, `zudilin_theorem`, `fischler_sprang_zudilin_2019`.
- Implication chains (`transcendence_implies_irrationality`,
  `conjecture_implies_apery/rivoal/zudilin/all_known`).

Apéry's ζ(3) proof itself is separately formalized in
`BaselProblemOQ01OQ01OQ02.lean` (5 axioms, integer-squeeze argument).

No new, non-duplicative, 0-axiom result is available: the routine
summability/positivity/bounds facts are already proved in OQ02, and everything
beyond them (irrationality/transcendence of any odd value) is either an open
problem or a deep theorem absent from Mathlib.

**Conclusion:** nothing genuinely new to prove. Marked `blocked` (open problem +
fully covered by siblings). No file created — would duplicate `BaselProblemOQ02`.

## Dead Ends

- Creating a `BaselProblemOQ01OQ02.lean` stating the odd-zeta irrationality
  conjecture + summability/positivity helpers — would duplicate `BaselProblemOQ02`.
- Attempting any irrationality result for a specific ζ(2n+1), n≥2 — open in
  mathematics; impossible to formalize as a proof.
