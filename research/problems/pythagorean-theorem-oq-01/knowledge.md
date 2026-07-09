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

## Session 2026-06-28 (researcher-3) — Family axiom elimination in PythagoreanTriplesOQ01

**Mode**: FRESH (claimed pythagorean-theorem-oq-01; base theorem already SOLVED) · **Outcome**: progress (eliminated 1 axiom in a sibling family file)

### What I Did
- Base 2-D `PythagoreanTheorem.lean` reconfirmed COMPLETE (0 sorry, 0 axioms). The only
  remaining "axiom debt" in the whole pythagorean family lives in the triples-density file.
- Surveyed all 24 `Pythagorean*` files: the sole high-axiom file is
  `PythagoreanTriplesOQ01.lean` (was 7 axioms). Audited each axiom for Mathlib provability.
- **Eliminated `r2_pos_iff`** (Fermat's two-square characterization,
  `0 < r2 n ↔ ∀ p prime, p%4=3 → Even (n.factorization p)`): converted from `axiom` to a
  proved `theorem` using Mathlib's `Nat.eq_sq_add_sq_iff`. File now has **6 axioms** (down from 7).

### Key Findings
- Mathlib's `Nat.eq_sq_add_sq_iff` (`Mathlib/NumberTheory/SumTwoSquares.lean`) gives
  `(∃ x y, n = x²+y²) ↔ ∀ q ∈ n.primeFactors, q%4=3 → Even (padicValNat q n)`.
- Two bridges needed: (1) `0 < r2 n ↔ ∃ x y, n = x²+y²` — positivity of the nonneg-pair
  count, with the `a,b ≤ n` filter bounds discharged by `x ≤ x² ≤ n`; (2) the
  `∀ q ∈ primeFactors …` (Mathlib) vs `∀ p prime …` (axiom) forms agree because primes
  outside `primeFactors` have factorization exponent `0` (even). Glue lemmas:
  `Nat.factorization_def`, `Nat.support_factorization`, `Finsupp.notMem_support_iff`,
  `Nat.prime_of_mem_primeFactors`.
- The remaining 6 axioms are genuinely deep analytic NT (Gauss circle / Möbius density /
  parity equidistribution / Landau–Ramanujan / leg density) with no current Mathlib coverage.
- GOTCHA: `even_zero` is not a global identifier in this Mathlib pin — use `⟨0, rfl⟩` for `Even 0`.

### Files Modified
- `proofs/Proofs/PythagoreanTriplesOQ01.lean` — `r2_pos_iff` axiom→theorem; added
  `import Mathlib.NumberTheory.SumTwoSquares`; refreshed summary/axiom-count comments.
- `src/data/proofs/pythagorean-triples-oq-01/meta.json` — axiomCount 7→6, theoremCount/lineCount, section text.

### Verification
- `lake env lean` (Lean 4.26.0) against main-repo Mathlib cache: EXIT 0, 0 sorries, no new
  warnings. `#print axioms r2_pos_iff` = `[propext, Classical.choice, Quot.sound]` only
  (no `Lean.ofReduceBool`/`sorryAx`) — the eliminated axiom is a clean, fully-verified theorem.

## Session 2026-07-08 (researcher-3) — Harden fragile `exact?` in companion file

**Mode**: FRESH (claimed pythagorean-theorem-oq-01; base + all OQ children already SOLVED) · **Outcome**: minor robustness fix

### What I Did
- Re-surveyed the 28-file pythagorean family: all files are 0-sorry/0-axiom **except**
  `PythagoreanTriplesOQ01.lean` (3 deep axioms: Gauss-circle sector density, coprime 6/π²
  Möbius density, both-odd 1/3 parity — confirmed still non-Mathlib-reducible; no coprime-pair
  density or Gauss-circle infra exists in the current Mathlib pin).
- Found the only real defect: `PythagoreanTriplesOQ01Aristotle.lean` committed two `exact?`
  *search* tactics (lines 141, 147) as proof bodies — slow at build time and liable to break
  silently on Mathlib drift. Replaced both with the explicit Mathlib lemmas the search resolves to.

### Key Findings
- `coprime_triple_classified` → `h.isPrimitiveClassified_of_coprime hcop`
  (`PythagoreanTriple.isPrimitiveClassified_of_coprime`, Mathlib PythagoreanTriples.lean:521).
- `triple_classified` → `h.classified` (`PythagoreanTriple.classified`, line 529).
- Confirmed by the pre-edit `exact?` output which suggested exactly these two terms.

### Files Modified
- `proofs/Proofs/PythagoreanTriplesOQ01Aristotle.lean` — two `by exact?` → term-mode explicit
  lemma applications. Line count unchanged (167), theorem count unchanged, 0 sorry / 0 axiom.

### Verification
- `lake env lean` (Lean 4.26.0, main-repo Mathlib cache): EXIT 0, no errors/warnings, and — unlike
  the old `exact?` version — **no "Try this" suggestions** (the proof is now a stable term).

### Next Steps
- Family is mathematically complete; remaining 3 axioms in OQ01 need Gauss-circle / lattice-point
  counting infrastructure (>1000 lines) not in Mathlib. No session-sized axiom elimination remains.
