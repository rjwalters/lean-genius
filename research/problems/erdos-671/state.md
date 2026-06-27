# Current State

**Phase**: BLOCKED (entry at its natural ceiling; remaining sorries need deep Mathlib infrastructure)
**Since**: 2026-06-26
**Iteration**: 2 (assessment; orphan scaffold for the lone tractable sorry)

## Session 2026-06-26 (Session 6) — confirm BLOCKED + orphan scaffold for `equidistant_diverges`

**Mode**: REVISIT. **Outcome**: no sorries eliminated (consistent with sessions 1–5).

- Re-confirmed the BLOCKED assessment: 3 axioms are the open conjectures; 6 of 7
  sorries need approximation-theory infrastructure absent from Mathlib;
  `equidistant_diverges` is the sole self-contained target.
- **Aristotle backend is DOWN this session**: both `prove_file` and the MCP smoke
  test return HTTP 404 (`https://aristotle.harmonic.fun/api/v1/project` not found),
  so the recommended `prove_file` route for `equidistant_diverges` is unavailable.
- **Local build unusable**: Docker daemon up but host load avg ≈ 47 with many
  concurrent peer builds — declined to add a fresh Mathlib build (would contend
  badly and likely time out; same caution as session 4 at load ≈ 26).
- **New groundwork**: created `proofs/Proofs/Erdos671EquidistantOrphan.lean`
  (UNREGISTERED — not imported by `proofs/Proofs.lean`, so zero gallery/build
  risk). It copies the compiling defs (`InterpolationPoints`, `lagrangeBasis`,
  `lebesgueFunction`, `equidistantNodes`) and isolates the **pointwise** heart of
  `equidistant_diverges` as a single sorry:
  `lebesgueFunction (equidistantNodes n hn) (midPoint n) ≥ 2^(n-1)/n^2`
  at `midPoint n = -1 + 1/(n-1)`. This avoids the `BddAbove`/supremum step
  entirely (that step lower-bounds the constant by the value at any admissible
  point separately) and reduces the goal to a pure finite product/factorial
  inequality — the right shape for `prove_file` or a manual induction once infra
  returns. Also proved `midPoint_mem` (routine Icc membership).

### Next Action (unchanged in spirit, now partly staged)
- When Aristotle is reachable: `prove_file` the orphan file's single sorry.
- Otherwise: manual induction on the factorial inequality (dominant central index
  m ≈ ⌊(n-2)/2⌋ per the numerics), then graft the proof + the separate sup-step
  (`BddAbove` via continuity of `lebesgueFunction` on compact `Icc`) into the
  registered `equidistant_diverges`.
- Do NOT re-attempt the other 6 sorries; they remain infrastructure-blocked.

## Current Focus

Erdős #671 ($250) — Lagrange interpolation convergence. The gallery entry
`Proofs/Erdos671Problem.lean` is `axiomatized` with **3 axioms + 7 sorries**
(15 theorems total). This session was an assessment of whether any remaining
sorry/axiom is tractable. Conclusion: **none is**, for the reasons below.

## Assessment of the 3 axioms

All three are the OPEN conjectures themselves and cannot be proved:
- `question1_open : Question1` — does there exist a node sequence with a point
  where λ_n(x) → ∞ yet L^n f(x) → f(x) for every continuous f? OPEN.
- `question2_open : Question2` — same with λ_n(x) → ∞ for ALL x. OPEN.
- `main_conjecture_open : MainConjecture` — the combined statement. OPEN.

These are correctly axioms; they are the unsolved problem.

## Assessment of the 7 sorries (all deep named theorems, NOT routine)

| line | theorem | classification |
|------|---------|----------------|
| 200 | `bernstein` (∃ divergence point, Bernstein 1931) | DEEP, not in Mathlib |
| 205 | `lebesgueConstant_growth` (Λ_n ≥ (2/π)log n − 1) | DEEP harmonic analysis, not in Mathlib |
| 220 | `erdos_vertesi` (a.e. divergence, Erdős–Vértesi 1980) | DEEP + Baire category, not in Mathlib |
| 317 | `equidistant_diverges` (Runge phenomenon) | DEEP, not in Mathlib |
| 335 | `faber` (Faber's theorem) | DEEP, not in Mathlib |
| 345 | `positive_measure_divergence` | DEEP, not in Mathlib |
| 353 | `full_measure_convergence` | DEEP, not in Mathlib |

None is a routine Mathlib application; each is a major formalization effort
(the Lebesgue-constant lower bound and Faber's theorem alone are research-grade
formalizations). They are **not Aristotle-suitable** — Aristotle spins on
results outside its training distribution, and these are essentially open/hard.

## Blockers

The entry is at its natural ceiling: the open conjectures are axiomatized, and
the supporting "known results" (Bernstein, Erdős–Vértesi, Faber, Lebesgue
constant growth) are deep approximation-theory theorems absent from Mathlib.
Advancing any of them requires building substantial harmonic-analysis
infrastructure (>1000 lines), which is beyond a single session and is itself a
research project. Additionally, Docker was down this session, so no analysis
proof could be build-verified even if attempted.

## Next Action

- Do NOT re-attempt these sorries piecemeal or via Aristotle.
- A genuine advance would require a dedicated multi-session effort to formalize
  the Lebesgue-constant lower bound Λ_n ≥ (2/π)log n + O(1) (the most
  self-contained of the seven), starting from Chebyshev-node estimates.
- Until that infrastructure exists, treat this entry as complete-as-axiomatized.
