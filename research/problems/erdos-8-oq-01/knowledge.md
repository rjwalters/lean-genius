# Knowledge: erdos-8-oq-01

## Session 2026-03-29 — Axiom elimination + bug fix (PR #7893, researcher-9)

- Reduced axioms 5 → 2 (proved `erdos_8_resolution` and
  `bottleneck_counterexample` from `hough_minimum_modulus`).
- Strengthened `bottleneck_counterexample` to require `k ≥ 2`.
- Fixed `erdos_graham_conjecture` and `erdos_8_disproved` to require
  `hasDistinctModuli` (math bug: without distinct moduli, trivial
  systems like `{0 mod 2, 1 mod 2}` have singleton moduli set `{2}`,
  making the disproval statement vacuously false).
- **Remaining 2 axioms** identified as deep Hough 2015 results.

## Session 2026-05-13 — Honest scope SURVEY (this PR, researcher-1)

Doc-only SURVEY. Key conclusions:

1. **Both remaining axioms are deep published results.** Each requires
   roughly 10⁴ LOC of analytic number theory (Hough's Fourier-analytic
   L²-mean estimates over residue classes) to formalize. Neither is a
   candidate for session-level discharge.

2. **The honest phase is SURVEY, not ACT.** ACT implies we are
   actively eliminating axioms, but we are not — we are surveying what
   else is tractable. Phase downgraded.

3. **Three structural sub-questions** are tractable and would enrich
   the formalization without depending on the deep axioms:
   - SQ-1: explicit small-bound covering-system constructions
   - SQ-2: cardinality lower bounds (Mirsky-style structural bounds)
   - SQ-3: replace the dummy `balister_improved_bound` with a strictly
     smaller explicit constant (axiomatized to BBMST 2022 but
     genuinely distinct from `hough_minimum_modulus`)

See `sessions/2026-05-13-survey-axiom-tractability-and-structural-followups.md`
for details.

---

## Insights

- The two remaining axioms (`hough_minimum_modulus`,
  `density_conjecture_false`) are deep 2015 Hough results, NOT routine
  axioms that can be discharged by a few sessions of work. They are
  honest assumptions corresponding to ~10⁴ LOC each of analytic number
  theory.
- The `balister_improved_bound` theorem currently just re-states
  `hough_minimum_modulus` — this is a **placeholder** that should be
  upgraded to a genuinely different (smaller) axiom citing Balister et al.
  2022.
- The `bottleneck_counterexample` argument is independent of the
  exact Hough bound — it only needs *some* upper bound on minModulus.
  This means any future improvement to the bound (down to even a much
  smaller constant) flows directly into the disproof without rewiring.
- **Structural progress** is possible without touching the deep axioms:
  the gallery would benefit from explicit small-K constructions and
  cardinality lower bounds. These are the natural next-action targets
  for this slug.

## Dead Ends

- **Trying to prove `hough_minimum_modulus` from first principles.**
  This is the main theorem of a 2015 Annals of Math paper. The
  Fourier-analytic L²-mean estimates rely on specialized techniques
  (truncated Gauss sums, equidistribution mod moduli, character sum
  bounds) that are not routinely available in Mathlib.
- **Trying to prove `density_conjecture_false` directly.** Same source
  paper, same toolkit. Both are out of scope for one researcher-agent
  session.
- **Adding placeholder theorems built on top of the deep axioms.** Per
  the researcher role's anti-pattern list ("adding new theorems/parts to
  files with high axiom counts"), the right move when stuck on the
  axioms is to find orthogonal structural work, not to inflate
  theorem-on-axiom scaffolding.

## Open Sub-Questions (tractable, session-scale)

- **SQ-1**: For each `K ∈ {2, 3, 4, 6, 12, …}`, exhibit (or prove
  non-existence of) a `CoveringSystem` with distinct moduli and
  `minModulus = K`. Classical constructions exist for K = 2 and K = 3.
- **SQ-2**: Prove `cs.moduli.card ≥ Ω(log cs.minModulus / log log cs.minModulus)`
  or similar concrete lower bound (Mirsky-style). Avoid the
  Hough-axiom path.
- **SQ-3**: Introduce an explicit BBMST 2022 axiom `balister_2022_bound
  : cs.minModulus ≤ 10^9` (smaller than 616 000? actually BBMST gives
  much smaller; need to look up the explicit constant in the paper).
  Show that this strictly improves `hough_minimum_modulus`.
