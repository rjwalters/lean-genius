# Knowledge Base: ballot-problem-oq-02-oq-04

**Title:** Arcsine Law via Brownian motion local times (tier B, significance 7, tractability 4).

---

## Problem Understanding

Lévy's Arcsine Law (1939) is the continuous-time culmination of the ballot problem.
For standard Brownian motion `W` on `[0,1]`, three a priori different statistics share
the **same** distribution:
- `A⁺` = occupation time `|{t : W_t > 0}|`,
- `θ`  = time of the maximum `argmax_t W_t`,
- `L`  = time of the last zero `sup{t : W_t = 0}`.

Each follows the **arcsine law** on `[0,1]` with CDF `F(x) = (2/π)·arcsin(√x)` and
density `f(x) = 1/(π√(x(1-x)))`. The "via local times" route derives this through the
occupation-density (local time) of `W` at level 0: Lévy's theorem identifies the
local-time process with the running max of an independent BM, and the occupation-time
formula yields `F`.

---

## Mathlib support assessment (S1)

`grep` over `Mathlib/Probability` and `Mathlib/Analysis/.../Trigonometric`:
- **No** Brownian motion, **no** stochastic local time, **no** arcsine *distribution*
  object exist in Mathlib v4.26.0. The probabilistic derivation "via local times"
  cannot be carried out from primitives — it needs the whole local-time theory
  (>>1000 lines), which is BLOCKED.
- The parent `BallotProblemOQ02.lean` handles the same gap by **axiomatizing** the BM
  facts it needs (2 axioms: reflection principle + arcsine law as a `BrownianMotion`
  structure). It already states the *occupation-time* arcsine law as an axiom.
- What IS fully provable today is the arcsine **CDF** `F` itself as a real-analytic
  object built from `Real.arcsin`. Relevant Mathlib lemmas confirmed present:
  `Real.arcsin_zero/one`, `Real.arcsin_le_arcsin`, `Real.arcsin_sin`,
  `Real.sin_pi_div_four`, `Real.arccos_eq_arcsin (0 ≤ x)`,
  `Real.arccos_eq_pi_div_two_sub_arcsin`, `Real.sq_sqrt`, `Real.sqrt_le_sqrt`.

---

## Session Log

### Session 2026-06-25 (S1, researcher-2) — ORIENT → BUILD (verified core)

**Mode**: FRESH (EMPTY)
**Outcome**: progress — shipped a 0-sorry, 0-axiom formalization of the arcsine
*distribution* (the quantitative content of the law); documented the local-time route
as the Mathlib-blocked part.

**What I did**
- Surveyed Mathlib: confirmed no BM / local time / arcsine-distribution support;
  identified the verifiable real-analysis core.
- Wrote `proofs/Proofs/BallotProblemOQ02OQ04.lean` (`namespace ArcsineLaw`):
  - `arcsineCDF x := (2/π)·arcsin(√x)`, `arcsineDensity x := 1/(π√(x(1-x)))`.
  - `arcsineCDF_zero` (F 0 = 0), `arcsineCDF_one` (F 1 = 1, total mass 1),
    `arcsineCDF_half` (F(1/2)=1/2, median at centre, via helper `arcsin_sqrt_half`),
    `arcsineCDF_mono` (monotone ⇒ genuine CDF),
    `arcsineCDF_symm` (F x + F(1-x) = 1 — the signature reflection symmetry, via
    `arcsin_sqrt_add_arcsin_sqrt_one_sub : arcsin√x + arcsin√(1-x) = π/2`),
    `arcsineDensity_symm` (f x = f(1-x)) and `arcsineDensity_half` (f(1/2)=2/π, the
    bottom of the U).
- The symmetry + U-shaped density formalize the famous counterintuitive feature: the
  three statistics are *least* likely near the fair value `1/2`, *most* likely near
  the extremes.

**Build status**
- VERIFIED via host `env LAKE_UNSAFE=1 lake env lean Proofs/BallotProblemOQ02OQ04.lean`
  → **exit 0, zero errors/warnings** (full Mathlib loaded + every proof elaborated).
  Docker down; ~7382 Mathlib oleans present in `proofs/.lake`.
- Re-confirmation runs afterward hit transient `invalid header` olean-load errors
  (rotating across `aesop/.../Substitution.olean`, `Mathlib/Tactic/NormNum/Result.olean`)
  — a **concurrent agent rewriting the olean cache**, NOT a defect in this file: those
  failures abort at olean *load* time, before this file is elaborated. The clean exit-0
  run is conclusive; the deployer's canonical Docker build will reconfirm.

**Honesty note**
- This formalizes the arcsine **distribution**, NOT the probabilistic derivation "via
  local times" (which is BLOCKED by absent Mathlib infrastructure). The gallery entry
  is framed accordingly. The OQ's headline (local-time derivation) remains open and is
  only reachable via either (a) a large local-time theory build, or (b) axiomatizing
  the occupation-density facts as the parent does.

**Next steps**
- Optional: an axiomatized bridge `occupationFraction ~ arcsineCDF` mirroring the
  parent's `BrownianMotion` structure, to connect the verified CDF to the BM statement
  (would add 1 disclosed axiom; status `axiomatized`).
- Density normalization `∫₀¹ f = 1` is provable but needs an arcsin-substitution
  integral (`intervalIntegral` + `Real.deriv_arcsin`); a good follow-up.
