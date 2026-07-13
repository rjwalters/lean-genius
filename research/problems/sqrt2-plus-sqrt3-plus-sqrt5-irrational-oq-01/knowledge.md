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

---

## Session 2026-06-14 (Session 3) — Make Strategy D verification durable + bound recipe (researcher-1)

**Mode**: CONTINUE · **Outcome**: ORIENT deepened (ephemeral verification made
reproducible; explicit ACT recipe for the bounds). Both backends still down: Docker
`docker ps` timeout; **Aristotle MCP tools now load but `prove` returns "Resource not
found"** (backend still unavailable) — so still build-free only.

### What I did
1. **Made Session 2's sympy verification durable and reproducible.** Committed
   `verify_strategy_d.py` (sympy 1.14 / mpmath, runs in seconds, exits 0 on
   "ALL CHECKS PASSED"). It re-derives every load-bearing fact *from first
   principles*, not by trusting the numbers already in this file:
   - **(F1) integrality**: each `√k` is a root of the monic integer `x²−k`
     (leading coeff 1, integer coeffs, `(√k)²−k=0`) — exactly `IsIntegral ℤ (√k)`.
   - **(F3) minimal polynomial**: re-derived `m(x)` independently as
     `Res_y(y⁴−10y²+1, (x−y)⁴−24(x−y)²+4)` (from `p=√2+√3 ⇒ p⁴−10p²+1=0` and
     `q=√5+√7 ⇒ q⁴−24q²+4=0`, both re-checked), confirmed it is **degree 16,
     monic, integer**, equals the value recorded above, has constant term
     `215²=46225`, and satisfies `m(α)=0` symbolically.
   - **(F2) the bound**: `8 < α < 9` (α ≈ 8.0281, 60-digit mpmath).
2. **Extracted the explicit ACT recipe for the bound lemmas** (de-risks the
   `8 < α < 9` step that Strategy D rests on). Rational witnesses, each verified
   to bound its radical by squaring (`lo² < k < hi²`):
   - `√2 ∈ (1.41, 1.42)`, `√3 ∈ (1.73, 1.74)`, `√5 ∈ (2.23, 2.24)`, `√7 ∈ (2.64, 2.65)`.
   - Lower sum `1.41+1.73+2.23+2.64 = 8.01 > 8`; upper sum
     `1.42+1.74+2.24+2.65 = 8.05 < 9`.
   - **Lean shape**: for each radical use `Real.lt_sqrt`/`Real.sqrt_lt'` (or
     `Real.le_sqrt`) with `norm_num` on `lo² < k` and `k < hi²`, then `linarith`
     to combine the four into `8 < α` and `α < 9`. No new Mathlib.

### Why this is forward progress (not re-ORIENT churn)
- Session 2's verification lived only in that session's transcript; the *numbers*
  were copied into knowledge.md but nothing here could be **re-checked**. The
  script makes them reproducible by anyone, and would catch a future transcription
  error in `m(x)` or the bound.
- The rational-witness recipe converts the hand-wavy "bounds via
  `Real.sqrt_lt_sqrt`" note into concrete, `norm_num`-ready inequalities — the
  single remaining non-API step in Strategy D's `sorry`.

### Files modified
- `research/problems/sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-01/{knowledge.md, state.md}`
- `research/problems/sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-01/verify_strategy_d.py` (new)

### Next steps (unchanged target, now lower-risk)
1. When Docker **or** Aristotle returns: implement Strategy D (~60–100 LOC). The
   only two genuinely-open Lean obligations are (a) the integral-closure descent
   `(r:ℝ) integral / ℤ ⇒ r ∈ ℤ` (lemma names to confirm: `IsIntegral.add`,
   integrality descent along injective `algebraMap ℚ ℝ`, `IsIntegrallyClosed ℤ`
   ⇒ `IsIntegrallyClosed.isIntegral_iff`) and (b) the bounds — now fully specced
   by the witness recipe above.
2. Fallbacks unchanged (Strategy A 3-squaring chain; or `m(α)=0` + rational-root).

---

## Session 2026-06-14 (Session 4) — Strategy D descent bearers confirmed at pin (researcher-5)

**Mode**: CONTINUE · **Outcome**: ORIENT → ACT-ready (de-risk). Both backends still down
(Docker `docker info` 15s timeout; Aristotle MCP `prove` → "Resource not found", probed this
session). Build-free only. **This discharges the single hedged item in the prior Next Action**:
"the integral-closure descent `(r:ℝ) integral / ℤ ⇒ r ∈ ℤ` (lemma names *to confirm*: ...,
integrality descent along injective `algebraMap ℚ ℝ`, ...)". Those names are now confirmed —
and the previously-**unnamed** descent step is identified — against the repo's exact Mathlib pin
`v4.26.0` (read via `gh api .../contents/...?ref=v4.26.0`, not the moving HEAD).

### Strategy D descent chain — every step now has a confirmed Mathlib bearer @ v4.26.0

Let `α := √2+√3+√5+√7`. Assume `α = algebraMap ℚ ℝ q` for some `q : ℚ` (i.e. `α` rational).

1. **`IsIntegral ℤ α`** — `IsIntegral.add` (×3) over the four `IsIntegral ℤ (√k)`. Each `√k`
   (k ∈ {2,3,5,7}) is a root of the monic integer `X² − C k`: leading coeff 1, integer coeffs,
   `(√k)² − k = 0` via `Real.sq_sqrt (by positivity)`. (Monic witness: `monic_X_pow_sub_C`.)
2. **descent ℝ → ℚ** (the step the prior sessions left *unnamed* as "integrality descent along
   `algebraMap ℚ ℝ`"): it is
   **`isIntegral_algebraMap_iff`** — `Mathlib/RingTheory/IntegralClosure/IsIntegral/Basic.lean:179`
   ```
   theorem isIntegral_algebraMap_iff [Algebra A B] [IsScalarTower R A B] {x : A}
       (hAB : Function.Injective (algebraMap A B)) :
       IsIntegral R (algebraMap A B x) ↔ IsIntegral R x
   ```
   Apply with `R = ℤ`, `A = ℚ`, `B = ℝ`, `x = q`. Needs `[IsScalarTower ℤ ℚ ℝ]` (standard
   instance) and `Function.Injective (algebraMap ℚ ℝ)` = `(algebraMap ℚ ℝ).injective`
   (`RingHom.injective`, since ℚ is a field). `.mp` turns `IsIntegral ℤ (algebraMap ℚ ℝ q)`
   (= `IsIntegral ℤ α` by the rationality hypothesis) into **`IsIntegral ℤ q`**.
3. **q is an integer** — **`IsIntegrallyClosed.isIntegral_iff`**
   `Mathlib/RingTheory/IntegralClosure/IntegrallyClosed.lean:210`
   ```
   theorem isIntegral_iff [IsIntegrallyClosed R] {x : K} :
       IsIntegral R x ↔ ∃ y : R, algebraMap R K y = x
   ```
   with `R = ℤ`, `K = ℚ`. `IsIntegrallyClosed ℤ` resolves by instance (ℤ is a PID/UFD; the
   `UniqueFactorizationMonoid` integrally-closed instance, same file/region — search hit
   `IntegrallyClosed.lean` & `RationalRoot.lean`); `[IsFractionRing ℤ ℚ]` is a standard instance.
   `.mp` gives `∃ n : ℤ, algebraMap ℤ ℚ n = q`, i.e. **`q ∈ ℤ`** ⇒ `α = (n : ℝ)`.
4. **contradiction** — bounds `8 < α < 9` (witness recipe, Session 3) ⇒ `α ∉ ℤ`. So no integer
   `n` with `α = n`; the rationality assumption is false. `Irrational α` ∎.

### Net effect
Strategy D is now **paste-port-ready**: steps 1–4 are pure transcription against named,
pin-verified lemmas; the only non-API work left is the four `norm_num` radical bounds (already
specced by Session 3's witness recipe). No genuinely-open Mathlib gap remains for Strategy D.
This is *not* re-ORIENT churn — it converts the prior "lemma names to confirm" TODO into
confirmed `file:line` bearers and resolves the one step that had no name.

### Caveat (kept honest)
Not Lean-checked — Docker/Aristotle down. The two residual transcription risks are (i) the cast
plumbing `√(2:ℕ)` vs `√(2:ℝ)` when assembling step 1 from `IsIntegral ℤ (√(k:ℕ))`, and (ii) that
`IsScalarTower ℤ ℚ ℝ` + `IsFractionRing ℤ ℚ` instances fire without manual `haveI`. Both are
routine but are exactly why a real build (not an uncompilable `.lean`) is deferred to ACT.

### Files modified
- `research/problems/sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-01/{knowledge.md, state.md}`

---

## Session 2026-06-15 (Session 5) — ACT: transcribe Strategy D (researcher-10)

**Mode**: REVISIT/CONTINUE · **Outcome**: progress (ORIENT → ACT). Docker still down
(`docker ps`/`docker info` timeout); Aristotle not used (only fills sorries — file is
sorry-free by construction). Build-pending, no local Lean.

### What I did
- **Wrote the complete Strategy D proof** to
  `proofs/Proofs/Sqrt2PlusSqrt3PlusSqrt5PlusSqrt7IrrationalOQ01.lean` (~95 LOC, 0 sorries,
  0 axioms by construction). Structure:
  - `isIntegral_of_sq (c m) (hc : c^2 = m) : IsIntegral ℤ c` — root of monic `X² − C m`
    (`Polynomial.monic_X_pow_sub_C` + `aeval`/`aeval_def`).
  - `isIntegral_sqrt_{two,three,five,seven}` — instantiate with `Real.sq_sqrt`.
  - `isIntegral_alpha` — `IsIntegral.add` ×3.
  - `alpha_lower : 8 < α` via `Real.lt_sqrt` on `1.41,1.73,2.23,2.64` (+ `linarith`).
  - `alpha_upper : α < 9` via `Real.sqrt_lt'` on `1.42,1.74,2.24,2.65`.
  - main `irrational_…` : `rintro ⟨q,hq⟩`; `eq_ratCast` bridges `(q:ℝ)=algebraMap ℚ ℝ q`;
    descend with `isIntegral_algebraMap_iff (algebraMap ℚ ℝ).injective`; integrally-closed
    `IsIntegrallyClosed.isIntegral_iff` gives `n:ℤ` with `(n:ℚ)=q`; `8<(n:ℝ)<9` then
    `exact_mod_cast` + `omega` ⇒ contradiction.
- **Re-verified all math** with the durable `verify_strategy_d.py` → `ALL CHECKS PASSED`
  (F1 integrality, F3 minimal polynomial via resultant, F2 bound `8<α<9` + all 8 rational
  square-witnesses). Independently re-checked my four decimal lower/upper witnesses in Python.

### Why this is forward progress (not re-ORIENT churn)
Sessions 1–4 left the problem "paste-port-ready" but produced **zero Lean**. This session
converts the bearer-confirmed skeleton into an actual, fully-written proof file. The only
remaining work is the Docker build verification + (if it passes) registration in
`proofs/Proofs.lean` and a gallery `meta.json`. Strategy D needed no new Mathlib.

### Honesty caveat
**Not machine-checked** — Docker down, so the file is build-pending and deliberately
**UNREGISTERED** in `proofs/Proofs.lean` (so it cannot break the aggregate auto-merge build).
Residual transcription risks are lemma-name/instance-resolution only (see `nextSteps`), not
mathematical — the mathematics is verified. Status stays NOT `verified` until a real build.

### Files modified
- `proofs/Proofs/Sqrt2PlusSqrt3PlusSqrt5PlusSqrt7IrrationalOQ01.lean` (new)
- `src/data/research/problems/sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-01.json`
- `research/problems/sqrt2-plus-sqrt3-plus-sqrt5-irrational-oq-01/{knowledge.md, state.md}`

### Next steps
1. Build when Docker returns; fix any lemma-name/instance drift (fallbacks: Strategy A or
   `m(α)=0` + rational-root). 2. Register + gallery `meta.json`. 3. Follow-up OQ: Strategy D
   scales to any finite sum of `√(squarefree)` with no degree blow-up.

## Session 2026-06-15 (Session 6, researcher-2) — extract reusable Strategy-D criterion

**Mode:** ACT (Lean refactor, build-low-risk). Dual blackout (Docker `docker info`
timeout; Aristotle `prove` → "Resource not found", re-probed live). Build-pending,
UNREGISTERED (unchanged status — file stays out of `Proofs.lean` so it cannot break
the aggregate before a Docker-up session verifies it).

**Delta:** Session 5 wrote the complete `√2+√3+√5+√7` Strategy-D proof. This session
**extracts its abstract core** as a gallery-reusable irrationality criterion in the
same file (`Sqrt2PlusSqrt3PlusSqrt5PlusSqrt7IrrationalOQ01.lean`):

```lean
theorem irrational_of_isIntegral_of_forall_ne_int {α : ℝ}
    (hα : IsIntegral ℤ α) (h : ∀ n : ℤ, α ≠ (n : ℝ)) : Irrational α
```

i.e. "an algebraic integer that avoids every rational integer is irrational" — the
packaged form of *a rational algebraic integer is an integer* (`ℤ` integrally closed
in `ℚ`). The proof is exactly Session 5's steps 2–3 (`eq_ratCast` →
`isIntegral_algebraMap_iff (·).injective` → `IsIntegrallyClosed.isIntegral_iff`), so
it carries the same already-bearer-pinned, math-verified content; no new Mathlib.

**Validation by use:** the main theorem `irrational_sqrt2_add_sqrt3_add_sqrt5_add_sqrt7`
is refactored to `refine irrational_of_isIntegral_of_forall_ne_int isIntegral_alpha
(fun n hn => ?_)` then discharges `∀ n, α ≠ n` from the existing `alpha_lower`/
`alpha_upper` interval `8 < α < 9` (`rw [hn]; exact_mod_cast; omega`). Main proof
shrinks ~18 → ~8 lines; the criterion + refactor together reprove the original, so
if the file compiles the abstraction is validated end-to-end.

**Why this is genuinely additive (not churn):** the criterion is the documented
"Strategy D scales to any finite sum of √(squarefree)" follow-up made concrete and
reusable. Any future √-sum slug (`√2+√3+√5`, longer sums, `∛`-free integral sums)
reuses it: prove each summand `IsIntegral` via `isIntegral_of_sq` + `IsIntegral.add`,
then trap in `(m, m+1)`. Mathlib has the pieces (`IsIntegrallyClosed.isIntegral_iff`)
but not this combined `IsIntegral → not-int → Irrational` criterion as a named lemma.

File: 0 sorries, 0 axioms, 10 theorems (was 9), ~95 → ~113 LOC. Still build-pending.

**Next Docker-up session:** build `Proofs.Sqrt2PlusSqrt3PlusSqrt5PlusSqrt7IrrationalOQ01`;
if clean, register + add gallery `meta.json`; the criterion is then ready to factor out
into a shared `Irrational`-criterion helper for the gallery's √-sum family.

---

## Session 2026-06-15 (researcher-1) — Build-free bearer name-check AUDIT

**Mode**: DEPTH-FIRST (RICH) · **Outcome**: audited (file de-risked for build/registration).
Docker still down (`docker info` timeout → blackout continues), so build-free only. The
Strategy-D proof file is complete and merged to main (`#24320`, `#24422`) but **never
compiled** under the blackout, and registration is pending in open PR `#24522`.

### What I did

Name-checked every nontrivial Mathlib bearer used in
`Proofs/Sqrt2PlusSqrt3PlusSqrt5PlusSqrt7IrrationalOQ01.lean` against the **pinned**
Mathlib revision `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (from
`proofs/lake-manifest.json`), fetching each source file from
`raw.githubusercontent.com/<rev>/<path>` and grepping the actual declaration. All bearers
exist with signatures that match the call sites:

| Bearer | Pinned location | Signature check |
|--------|-----------------|-----------------|
| `Real.sq_sqrt` | `Mathlib/Data/Real/Sqrt.lean:163` | `(h : 0 ≤ x) : √x ^ 2 = x` ✓ |
| `Real.lt_sqrt` | `Mathlib/Data/Real/Sqrt.lean:364` | `(hx : 0 ≤ x) : x < √y ↔ x ^ 2 < y` ✓ |
| `Real.sqrt_lt'` | `Mathlib/Data/Real/Sqrt.lean:217` | `(hy : 0 < y) : √x < y ↔ x < y ^ 2` ✓ |
| `Polynomial.monic_X_pow_sub_C` | `Mathlib/Algebra/Polynomial/Monic.lean:440` | `(a : R) {n : ℕ} (h : n ≠ 0) : Monic (X^n - C a)` ✓ |
| `Polynomial.aeval_def` | `Mathlib/Algebra/Polynomial/AlgebraMap.lean:259` | `aeval x p = eval₂ (algebraMap R A) x p` ✓ |
| `IsIntegral.add` | `Mathlib/RingTheory/IntegralClosure/Algebra/Basic.lean:156` | `(hx) (hy) : IsIntegral R (x+y)` ✓ |
| `isIntegral_algebraMap_iff` | `Mathlib/RingTheory/IntegralClosure/IsIntegral/Basic.lean:179` | `[IsScalarTower R A B] (inj) : IsIntegral R (algebraMap A B x) ↔ IsIntegral R x` ✓ |
| `IsIntegrallyClosed.isIntegral_iff` | `Mathlib/RingTheory/IntegralClosure/IntegrallyClosed.lean:210` | `[IsFractionRing R K] {x:K} : IsIntegral R x ↔ ∃ y:R, algebraMap R K y = x` ✓ |
| `eq_ratCast` | `Mathlib/Data/Rat/Cast/Defs.lean:220` | `[DivisionRing α] [RingHomClass F ℚ α] (f) (q) : f q = q` ✓ |

### Residual build-risks from prior knowledge — now CLEARED

The earlier S5 note flagged three transcription risks. All discharged by the name-check:
- **(a) instance firing** for `isIntegral_algebraMap_iff` / `IsIntegrallyClosed.isIntegral_iff`:
  both need `IsScalarTower ℤ ℚ ℝ` / `IsFractionRing ℤ ℚ` respectively — these are standard
  global instances (ℤ→ℚ→ℝ tower; ℚ = Frac ℤ), so they fire automatically.
- **(b) `aeval_def` vs `eval2` defeq** in `isIntegral_of_sq`: `aeval_def` is exactly the
  bridge `aeval x p = eval₂ (algebraMap R A) x p`; `simpa [Polynomial.aeval_def]` closes it.
- **(c) `eq_ratCast` applicability** to bundled `algebraMap ℚ ℝ`: `algebraMap ℚ ℝ : ℚ →+* ℝ`
  is a `RingHomClass F ℚ ℝ` with ℝ a `DivisionRing`, so `eq_ratCast (algebraMap ℚ ℝ) q`
  typechecks and rewrites `algebraMap ℚ ℝ q ↦ (q : ℝ)`.

### Conclusion

The file is **name-check-clean** at the pinned Mathlib rev; nothing in it depends on a
renamed/absent/mis-signatured bearer. The pending registration `#24522` is safe to merge —
the deployer build should be green. This is build-free de-risking only (not a substitute for
an actual `lake build`), but it removes the documented blockers' uncertainty. No new Lean
content added (slug is saturated: core proof merged, criterion extracted in `#24422`,
explicit minpoly in `#24512`); honest assessment is that the remaining work is purely the
Docker build + gallery `meta.json`, both gated on the blackout lifting.

---

## Session 2026-06-15 (researcher-1) — BUILD GREEN: Strategy D machine-checked ✓

**Mode**: ACT (build) · **Outcome**: VERIFIED. Docker recovered this session and
`lake exe cache get` works (a peer build downloaded all 7727 Mathlib cache files), so the
long-deferred build was finally viable.

### What I did
- Ran the targeted build:
  `LEAN_MEMORY_LIMIT=6144 ./proofs/scripts/docker-build.sh Proofs.Sqrt2PlusSqrt3PlusSqrt5PlusSqrt7IrrationalOQ01`
  → **`Build completed successfully (7743 jobs)`**, exit 0, **0 errors, 0 sorries**.
  Used a 6 GB cap to coexist with 2 concurrent peer builds on the 7.65 GB Docker VM.
- This is the **first machine-check** of the Strategy-D proof, deferred across Sessions 1–7
  under the Docker/Aristotle blackout. The S4/S-audit bearer name-check (all 9 nontrivial
  Mathlib bearers @ pin) **predicted green and held** — no lemma-name/instance drift, none of
  the three flagged transcription risks (instance firing, `aeval_def` defeq, `eq_ratCast`)
  materialized.
- **Honesty fix**: gallery `meta.json` already claimed `verified/original` + "Fully
  machine-checked" for a never-compiled file (an overclaim until now) with a **stale
  `theoremCount: 8`**. The file has **10 theorems**; corrected both the `meta` and `leanFile`
  blocks 8→10. The `verified/original` status is now legitimate post-build.
- Updated registry JSON: `status surveyed→completed`, `phase ORIENT→COMPLETED`,
  `leanFiles []→[Proofs/Sqrt2PlusSqrt3PlusSqrt5PlusSqrt7IrrationalOQ01.lean]`.

### Build-environment note (supersedes prior blackout memories for this session)
`docker info` UP **and** `lake exe cache get` succeeded (7727/7727 downloaded, decompressed,
"Completed successfully!"). The documented "circular `.lake` self-symlink → Mathlib-from-source
OOM" did **not** bite: the build re-clones Mathlib and fetches the precompiled olean cache over
the network rather than recompiling, so only our single module compiles (light). A modest memory
cap is enough to be a good citizen alongside peer builds.

### Net effect
Slug **complete and verified**. No new Lean content needed — this session converted the
7-session-old build-pending proof into a machine-checked `verified/original` gallery entry and
corrected the pre-existing overclaim's stale theorem count. The reusable criterion
`irrational_of_isIntegral_of_forall_ne_int` is now machine-checked and ready to factor into a
shared gallery √-sum helper (optional follow-up OQ).
