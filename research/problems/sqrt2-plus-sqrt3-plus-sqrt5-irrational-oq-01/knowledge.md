# Knowledge Base: sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-01

**Goal**: `Irrational (Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 5 + Real.sqrt 7)`
**Parent**: `sqrt2-plus-sqrt3-plus-sqrt5-irrational` (gallery proof of `Irrational (√2+√3+√5)`,
file `Proofs/Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01.lean`, 145 LOC, 0 sorries).

---

## Problem Understanding

α := √2+√3+√5+√7 is an algebraic integer of **degree 16** over ℚ (NOT degree 8 — see the
2026-06-14 correction below). It is a primitive element of the multiquadratic field
ℚ(√2,√3,√5,√7), whose Galois group is (ℤ/2)⁴ acting by independent sign flips of each radical.
The orbit of α is {±√2±√3±√5±√7}; by ℚ-linear independence of √2,√3,√5,√7 all 16 sign patterns
give distinct values, so the stabilizer is trivial, the orbit has size 16, and the minimal
polynomial of α has degree 16. Degree ≠ 1 ⇒ irrational.

---

## Insights

- **Three formalization strategies** (increasing Mathlib-infrastructure cost):
  - **(A) Elementary iterated squaring** — generalizes the parent's 145-line proof. The parent
    isolates a single residual surd √30 after *two* squarings (`α⁴ − 20α² − 24 = 8α√30`) and
    closes via `Irrational √30`. For four radicals this does **not** collapse to a single surd
    in one extra squaring: after subtracting √7 and squaring once, three independent surds
    √6, √10, √15 appear alongside √7. Reaching a single residual surd takes three squarings,
    producing a residual identity that is degree 8 in α and carries one surd; a fourth squaring
    would give the degree-16 minimal polynomial. Honest LOC estimate **300–600**, all elementary
    (`ring`/`linarith`/`Real.sq_sqrt`/`irrational_sqrt_natCast_iff`), **no new Mathlib**. Upper
    end of the BUILD range; Docker-gated.
  - **(B) ℚ-linear independence of {1,√2,√3,√5,√7}** (Besicovitch) — cleanest argument
    (α rational ⇒ a nontrivial ℚ-linear relation among 1,√2,√3,√5,√7, contradiction). But
    Mathlib has **no ready lemma** for linear independence of square roots of squarefree
    integers (web-confirmed 2026-06). General theorem >500 LOC; a narrow 4-prime version
    ~200–400 LOC.
  - **(C) Field degree [ℚ(√2,√3,√5,√7):ℚ]=16** — parallels the sibling gallery proof
    `Sqrt2PlusSqrt3IrrationalOQ03` (minpoly of √2+√3 = X⁴−10X²+1 via `minpoly`/
    `IntermediateField`), scaled to degree 16; needs linear-disjointness / multiquadratic-degree
    infrastructure not assembled in Mathlib (>500 LOC).

- **Mathlib gaps**: (1) ℚ-linear independence of {√d : d squarefree} (Besicovitch) — needed for
  B; (2) assembled multiquadratic-field degree / linear disjointness of ℚ(√pᵢ) — needed for C.
  Strategy A needs no new Mathlib (`irrational_sqrt_natCast_iff`, `Real.sq_sqrt`, `Real.sqrt_mul`
  all present).

  - **(D) Algebraic-integer + bounded-interval** (NEW, 2026-06-14 Session 2; **now recommended**) —
    α is a sum of four algebraic integers √2,√3,√5,√7 (each a root of the monic `X²−k`), so α is
    integral over ℤ. A rational number that is integral over ℤ lies in ℤ (ℤ is integrally closed
    in ℚ). But `8 < α < 9` (α ≈ 8.0281, verified), so α ∉ ℤ; hence α is irrational. This sidesteps
    the entire degree-16 algebra: **no squaring chain, no minimal polynomial, no surd isolation.**
    Estimated **~60–100 LOC**, no new Mathlib theory — just the integral-closure API.

- **Recommended path**: **Strategy D** — far shorter than A and avoids the messy degree-16
  bookkeeping that A and B/C require. Strategy A remains a valid fallback (no infrastructure
  dependency) but is now superseded; reserve B/C only if the integral-closure lemmas are missing.

- **Explicit minimal polynomial** (sympy-verified, `m(α)=0` exactly): α has degree-16 minimal
  polynomial over ℚ (monic, integer coefficients, even):
  `m(x) = x¹⁶ − 136x¹⁴ + 6476x¹² − 141912x¹⁰ + 1513334x⁸ − 7453176x⁶ + 13950764x⁴ − 5596840x² + 46225`
  (constant term `46225 = 215²`). Equivalently `g(α²)=0` with the degree-8
  `g(y)=y⁸−136y⁷+6476y⁶−141912y⁵+1513334y⁴−7453176y³+13950764y²−5596840y+46225`. This confirms
  the degree-16 claim concretely and gives an alternative Lean target (`m(α)=0` is `ring`-provable
  after `Real.sq_sqrt`, but the 16th-power expansion is heavy — Strategy D avoids needing it).

---

## Dead Ends

- Naive reduction "√2+√3+√5 = q − √7 with both sides irrational" gives **no** contradiction
  (irrational − irrational can be rational). Squaring it yields √6+√10+√15+q√7 ∈ ℚ, i.e. four
  surds again — no shortcut around the degree-16 structure.
- **Strategy-A single-surd reduction has ugly coefficients** (Session 2, numerically confirmed).
  Expressing √210 (= √2·√3·√5·√7) in the power basis of α gives
  `√210 = Σ cᵢ αⁱ` with only even powers but rational coefficients over a common denominator
  `14 499 840` (e.g. `c₀ = 42047681/2899968`, `c₁₄ = −1/906240`). There is **no** clean
  small-integer single-surd identity analogous to the parent's `α⁴−20α²−24 = 8α√30`. This is
  concrete evidence that Strategy A's "isolate one surd" endgame is heavy, reinforcing the switch
  to Strategy D.

---

## Session 2026-06-14 (Session 1) — Build-free ORIENT survey (researcher-10)

**Mode**: FRESH · **Outcome**: surveyed (OBSERVE → ORIENT). Both backends down (Docker
`docker info` timeout; Aristotle `prove` → "Resource not found"), so build-free only.

### What I did
- Resolved the statement on paper (degree-16 argument above).
- Assessed the three strategies vs. current Mathlib (web-checked Besicovitch availability).
- **Corrected a math error in `problem.md`**: it claimed α has "degree 8" with "eight sign
  combinations (even number of minus signs)". α has **degree 16** (trivial stabilizer ⇒ all 16
  sign-flips are distinct conjugates). The degree-8 figure is the *parent's* (√2+√3+√5) degree
  and the lower-degree *intermediate residual identity*, not α's degree.
- **Fixed a doc-integrity defect in the registry JSON**: `leanFiles` pointed at the parent's
  complete file `Sqrt2PlusSqrt3PlusSqrt5IrrationalOQ01.lean` (proves √2+√3+√5, no √7; 0 sorries),
  making this unsolved OQ look solved. Cleared `leanFiles` and added the real problem statement
  (was a placeholder).

### Files modified
- `src/data/research/problems/sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-01.json`
- `research/problems/sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-01/{problem.md, knowledge.md, state.md}`

### Next steps
1. When Docker returns: draft Strategy A in
   `Proofs/Sqrt2PlusSqrt3PlusSqrt5PlusSqrt7IrrationalOQ01.lean` (3-squaring chain to a single
   residual surd). ~300–600 LOC, no new Mathlib. BUILD-class, Docker-gated.
2. Fallback: narrow 4-prime Besicovitch lemma `LinearIndependent ℚ ![1,√2,√3,√5,√7]`.
3. Surd-isolation identities are Aristotle-eligible (HARD-but-known) once stated — blocked by
   the Aristotle backend outage.

---

## Session 2026-06-14 (Session 2) — Build-free strategy deepening (researcher-4)

**Mode**: CONTINUE · **Outcome**: ORIENT deepened (new recommended strategy + verified
artifacts). Both backends still down (Docker `docker info` timeout; Aristotle `prove` →
"Resource not found"), so build-free only — all results checked with sympy/mpmath, not Lean.

### What I found (all numerically/symbolically verified)
1. **Explicit minimal polynomial** of α (sympy `minimal_polynomial`, then `m(α)=0` confirmed
   exactly): degree 16, monic, integer, even — see Insights above. Independently re-derivable
   from `p=√2+√3 ⇒ p⁴−10p²+1=0` and `q=√5+√7 ⇒ q⁴−24q²+4=0` via the resultant
   `Res_y(y⁴−10y²+1, (α−y)⁴−24(α−y)²+4)`.
2. **New Strategy D (algebraic integer + bound)** — now the recommended path; ~60–100 LOC,
   avoids all degree-16 algebra. The key arithmetic fact `8 < α < 9` (α ≈ 8.0281) is verified.
3. **Strategy A's single-surd endgame is ugly** (denominator 14 499 840) — see Dead Ends.

### Strategy D — concrete Lean skeleton (for ACT when Docker returns)
```lean
import Mathlib
open Real
-- √k is integral over ℤ: root of monic X^2 - C k.
lemma isIntegral_sqrt (k : ℕ) : IsIntegral ℤ (Real.sqrt k) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C (k : ℤ), ?_, ?_⟩
  · -- monic (leading coeff 1)
    monicity?  -- Polynomial.monic_X_pow_sub_C-style; degree-2 monic
  · -- aeval (√k) (X^2 - C k) = 0, i.e. (√k)^2 - k = 0
    simp [Real.sq_sqrt (by positivity : (0:ℝ) ≤ k)]
theorem irrational_sum :
    Irrational (sqrt 2 + sqrt 3 + sqrt 5 + sqrt 7) := by
  have hα : IsIntegral ℤ (sqrt 2 + sqrt 3 + sqrt 5 + sqrt 7) :=
    (((isIntegral_sqrt 2).add (isIntegral_sqrt 3)).add (isIntegral_sqrt 5)).add (isIntegral_sqrt 7)
  rintro ⟨r, hr⟩                       -- r : ℚ, (r:ℝ) = α
  -- (r:ℝ) integral over ℤ  ⇒  r integral over ℤ  (ℚ↪ℝ injective)  ⇒  r ∈ ℤ (ℤ integrally closed)
  -- then 8 < (r:ℝ)=α < 9 forces a non-integer integer. Contradiction.
  sorry
```
Open Lean items to confirm at build time (lemma names, not math):
- `IsIntegral.add` (algebraic integers closed under +) — standard, in `Mathlib.RingTheory.IntegralClosure`.
- Descent of integrality along the injective `algebraMap ℚ ℝ` (so `(r:ℝ)` integral ⇒ `r` integral).
- `IsIntegrallyClosed ℤ` ⇒ a rational integral over ℤ equals some `(n:ℤ)` (`IsIntegrallyClosed.isIntegral_iff`).
- Bounds `8 < √2+√3+√5+√7 < 9` via `Real.sqrt_lt_sqrt`/`Real.lt_sqrt` + `norm_num`.

### Files modified
- `research/problems/sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-01/{knowledge.md, state.md}`
- `src/data/research/problems/sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-01.json`

### Next steps
1. When Docker returns: implement **Strategy D** (above) — much smaller than A; verify the four
   Lean lemma names resolve, fill the `sorry`. If `IsIntegrallyClosed` descent is awkward, fall
   back to Strategy A or prove `m(α)=0` and apply the rational-root theorem (α∉ℤ ⇒ irrational).
2. Strategy A remains the no-infrastructure fallback (3-squaring chain; ugly but elementary).
