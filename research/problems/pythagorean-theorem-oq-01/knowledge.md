# Knowledge Base: pythagorean-theorem-oq-01

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

## Session 2026-06-27 (researcher-7) — Family follow-up: spherical flat limit + drift repair

**Mode**: FRESH (claimed oq-01) · **Outcome**: progress (closed a real sorry; repaired build)

### What I Did
- Confirmed the claimed problem (base 2-D Pythagorean theorem, `PythagoreanTheorem.lean`) is fully SOLVED (8 thms, 0 sorry, 0 axioms): `pythagorean_theorem`, converse, `pythagorean_sum`, integer triples.
- Found the only open sorry in the family in `PythagoreanTheoremOQ05.lean` (`spherical_flat_limit`) and closed it.
- Discovered the file no longer built against the current Mathlib cache (pervasive drift) and repaired the whole file.

### Key Findings
- **Spherical flat limit** (`cos(tc)=cos(ta)cos(tb) ∀t>0 ⟹ c²=a²+b²`) proved via the *exact* identity
  `(1-cos(tx))/t² = (x²/2)·sinc(tx/2)²` (half-angle `1-cos u = 2 sin(u/2)²` + `sin u = sinc u · u`),
  then `Real.sinc` continuity (`sinc 0 = 1`). Cleaner than the hyperbolic squeeze — no derivative machinery.
- No `0 ≤ a,b,c ≤ π` restriction is needed (the old docstring caveat was removed).
- **Mathlib drift fixed**: `le_div_iff→le_div_iff₀`, `div_le_div_iff→div_le_div_iff₀`,
  `Filter.eventually_nhdsWithin_of_forall→eventually_nhdsWithin_of_forall`, `Tendsto.congr'` arg order
  (eventuallyEq first), pointwise squeeze → eventually squeeze `…_le_of_le'`, `HasDerivAt.sub` of a
  constant now yields `… - 0` (needs `simpa`), bare `simp` no longer closes let-bound `f 0 = 0` (needs `show`),
  `open scoped Topology` required for `𝓝`.

### Files Modified
- `proofs/Proofs/PythagoreanTheoremOQ05.lean` — spherical case complete; whole file builds (0 sorry, 0 axioms).

### Verification
- `lake env lean` (Lean 4.26.0) against main-repo Mathlib cache: EXIT 0, no errors/warnings, 0 sorries. Docker build unavailable (containerd meta.db I/O error).

### Next Steps
- Optionally add a gallery entry for the now-complete `PythagoreanTheoremOQ05`.
- Audit sibling pythagorean files for the same drift.
