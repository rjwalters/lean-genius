# S18 PREP — Bridge-identity `r p` uniformity gap audit + 4 resolution paths

**Date**: 2026-05-16 ~14:30 UTC
**Researcher**: researcher-6
**Mode**: PREP (doc-only)
**Phase tag**: S18 PREP (audits the S17 ACT recipe staged by S16 PREP-1 / S16 PREP-2 / S17 PREP STATE-SYNC; defers Lean delivery)
**Mathlib pin**: SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0, unchanged since S15 era)
**Net Lean delta**: 0 (this PR adds only this session log + state.md update + JSON registry update)
**Branch**: `research/angle-trisection-cos20-oq03-s18-prep-bridge-uniformity-gap-1778943026`

---

## §0 — Scope and headline

**Headline finding**: The S17 ACT recipe staged by S17 PREP STATE-SYNC
(PR #19335, merged 2026-05-16T01:09:13Z) — "S17 ACT Option A: sharpened
Path A via Chebyshev-C bridge, `(C ℤ p).comp (X - C 2) + C 2 = X · (r p)^2`
for odd prime `p`, ~80–120 LOC induction via `Polynomial.Chebyshev.C_add_two`"
— **cannot be proved as stated** because the slug-local
`r : ℕ → ℤ[X]` definition at
`proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean:89–95` is a
**5-case pattern-match returning `0` for `p ∉ {3, 5, 7, 11, 13}`**:

```lean
noncomputable def r : ℕ → ℤ[X]
  | 3  => X - C 3
  | 5  => X ^ 2 - C 5 * X + C 5
  | 7  => X ^ 3 - C 7 * X ^ 2 + C 14 * X - C 7
  | 11 => X ^ 5 - C 11 * X ^ 4 + C 44 * X ^ 3 - C 77 * X ^ 2 + C 55 * X - C 11
  | 13 => X ^ 6 - C 13 * X ^ 5 + C 65 * X ^ 4 - C 156 * X ^ 3 + C 182 * X ^ 2 - C 91 * X + C 13
  | _  => 0
```

For any odd prime `p ≥ 17`, `r p = 0` (catch-all), so the bridge RHS
`X · (r p)^2 = 0`, while the LHS `(C ℤ p).comp (X - C 2) + C 2` is
a degree-`p` polynomial with leading coefficient `1` — **non-zero**.
The identity reduces to `LHS = 0`, which is false. The induction
route (iii) recommended by S17 PREP STATE-SYNC §4 cannot start because
`r p` is not parametric — its definition unfolds to one of six
disjoint clauses, four of which (for `p = 3, 5, 7, 11, 13`) give the
explicit Eisenstein witness and one of which (for `p` not in the list)
gives the zero polynomial.

The S16 PREP-1 §2 numerical witnesses at `p ∈ {3, 5}` and the
S16 PREP-2 §5 witness at `p = 7` **all happen to land inside the
5-clause window where `r p` is defined**, so they confirmed the bridge
**only for the cases where the identity is non-trivial by construction
of `r`**. They did not test the catch-all branch.

This PREP:

- **§1** — Reads the file definition + presents the direct numerical
  refutation at `p = 17` (and the smaller positive checks at `p ∈ {3, 5, 7}` re-stated for symmetry).
- **§2** — Diagnoses how the S16/S17 PREP chain converged on a recipe
  that overlooked the slug-local `r p` shape (the chain focused on
  Mathlib-side bearers and rederived the identity in terms of `r p` symbolically).
- **§3** — Catalogues four resolution paths (R1–R4) and ranks them by
  rework cost, risk, and conformance with the open conjecture
  `eisenstein_conjecture_cos_pi_p` (which is purely existential and
  does **not** require a parametric `r p` to be discharged).
- **§4** — Recommends Path R3 (existence-only, using a Chebyshev-side
  uniform polynomial as the witness without renaming or
  re-defining `r`) — preserves all S5/S6/S9/S10/S15 theorems and
  introduces zero risk of regression to the 5 verified primes.
- **§5** — Re-pins 4 load-bearing bearers at the same SHA (`Polynomial.Chebyshev.C`,
  `Polynomial.Chebyshev.C_add_two`, `Polynomial.Monic.isEisensteinAt_of_mem_of_notMem`,
  `Polynomial.IsEisensteinAt.irreducible`) at SHA `2df2f0150c...`: **0 drift**.
- **§6** — Two new bearer pins for Path R3 (`Polynomial.Chebyshev.C_comp_two_mul_X`,
  `Polynomial.Chebyshev.U`): both **present** at SHA `2df2f015...`.
- **§7** — Honesty log.
- **§8** — Conflict-free guarantees vs all open PRs on slug.
- **§9** — Anti-targets.
- **§10** — Cross-references.

This PR is **strictly doc-only**: it does not modify the Lean file,
`meta.json`, `problem.md`, `knowledge.md`, or `proofs/lake-manifest.json`.
It modifies **only** `state.md` (extends Iteration counter 17 → 18,
adds "Recent PREP audit chain (S18)" subsection, refreshes "Next Action"
to point at the R3-aligned S18a/b/c work order), the registry JSON
(`currentState.iteration` 17 → 18, `currentState.focus` extended,
`currentState.nextAction` rewritten, `knowledge.builtItems` +1 entry,
`knowledge.nextSteps` re-targeted to R3-aligned sub-steps), and adds
this new session log.

---

## §1 — Direct verification of the gap

### §1.1 — Slug-local `r p` definition at HEAD

`proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` lines 89–95 (verbatim, on `origin/main` at content-hash `ceaa6f12c79`):

```lean
noncomputable def r : ℕ → ℤ[X]
  | 3  => X - C 3
  | 5  => X ^ 2 - C 5 * X + C 5
  | 7  => X ^ 3 - C 7 * X ^ 2 + C 14 * X - C 7
  | 11 => X ^ 5 - C 11 * X ^ 4 + C 44 * X ^ 3 - C 77 * X ^ 2 + C 55 * X - C 11
  | 13 => X ^ 6 - C 13 * X ^ 5 + C 65 * X ^ 4 - C 156 * X ^ 3 + C 182 * X ^ 2 - C 91 * X + C 13
  | _  => 0
```

The module docstring at line 80–88 acknowledges the placeholder
intent explicitly:

> "For all other p, returns a placeholder `0`. The conjecture
> `eisenstein_conjecture_cos_pi_p` asserts the existence of a polynomial
> with the required Eisenstein structure for every odd prime p ≥ 3."

So the file's authors knew `r p = 0` for p ∉ {3, 5, 7, 11, 13} and
considered this acceptable because the **open conjecture is
existential** (∃ q : ℤ[X], …) — does not need a uniform parametric `r p`.

### §1.2 — Bridge identity numerical evaluation

Bridge identity from S17 PREP STATE-SYNC §4 (sub-step S17a):

```
(C ℤ p).comp (X - C 2) + C 2 = X · (r p)^2     for odd prime p ≥ 3.
```

#### §1.2.a — At `p = 3` (in 5-clause window) — IDENTITY HOLDS

LHS: `C_3 = X · C_2 - C_1 = X · (X^2 - 2) - X = X^3 - 3X`.
Then `C_3.comp(X-2) = (X-2)^3 - 3(X-2) = X^3 - 6X^2 + 12X - 8 - 3X + 6 = X^3 - 6X^2 + 9X - 2`.
Plus `C 2 = 2` gives `LHS = X^3 - 6X^2 + 9X`.

RHS: `r 3 = X - C 3 = X - 3`. So `(r 3)^2 = (X - 3)^2 = X^2 - 6X + 9`.
Thus `X · (r 3)^2 = X^3 - 6X^2 + 9X`.

**LHS = RHS = `X^3 - 6X^2 + 9X = X · (X - 3)^2`.** ✓

#### §1.2.b — At `p = 5` (in 5-clause window) — IDENTITY HOLDS

LHS: `C_4 = X·C_3 - C_2 = X(X^3 - 3X) - (X^2 - 2) = X^4 - 4X^2 + 2`.
`C_5 = X·C_4 - C_3 = X(X^4 - 4X^2 + 2) - (X^3 - 3X) = X^5 - 5X^3 + 5X`.
`C_5.comp(X-2) = (X-2)^5 - 5(X-2)^3 + 5(X-2)`.
Expanding: `(X-2)^5 = X^5 - 10X^4 + 40X^3 - 80X^2 + 80X - 32`.
`5(X-2)^3 = 5X^3 - 30X^2 + 60X - 40`.
`5(X-2) = 5X - 10`.
Sum: `(X^5 - 10X^4 + 40X^3 - 80X^2 + 80X - 32) - (5X^3 - 30X^2 + 60X - 40) + (5X - 10) = X^5 - 10X^4 + 35X^3 - 50X^2 + 25X - 2`.
Plus `C 2 = 2` gives `LHS = X^5 - 10X^4 + 35X^3 - 50X^2 + 25X`.

RHS: `r 5 = X^2 - 5X + 5`. `(r 5)^2 = X^4 - 10X^3 + 35X^2 - 50X + 25`.
`X · (r 5)^2 = X^5 - 10X^4 + 35X^3 - 50X^2 + 25X`.

**LHS = RHS = `X · (X^2 - 5X + 5)^2`.** ✓

#### §1.2.c — At `p = 17` (OUTSIDE 5-clause window) — IDENTITY FAILS

By the `_ => 0` catch-all clause: `r 17 = 0`, so `(r 17)^2 = 0`, so `X · (r 17)^2 = 0`.

LHS: `C_17 = X · C_16 - C_15`. Recurring from `C_0 = 2`, `C_1 = X`:
the polynomial `C_17` has degree `17`, leading coefficient `1`, and is
**non-zero**. Therefore `C_17.comp(X - C 2)` is non-zero (degree-preserving
composition), and `LHS = C_17.comp(X-2) + 2` is non-zero of degree `17`.

**LHS ≠ 0 = RHS.** Bridge identity is **definitionally false** at `p = 17` with the file-local `r`.

(Concrete leading-coefficient check: `(C_17).leadingCoeff = 1`. After
`comp (X - C 2)`, the leading coefficient is preserved as `1`. Adding
`C 2 = 2` does not change degree. So `(LHS).leadingCoeff = 1 ≠ 0`.
Independent of the lower-degree coefficient details.)

#### §1.2.d — General: bridge fails for every odd prime `p ≥ 17`

Same argument as §1.2.c: any `p ∉ {3, 5, 7, 11, 13}` falls into the
`_ => 0` clause, RHS = 0, LHS has degree `p ≥ 17`, leading coefficient
`1`, hence non-zero.

The bridge identity as written in S17 PREP STATE-SYNC §4 has scope
**at most** `p ∈ {3, 5, 7, 11, 13}` — exactly the 5 primes where
`eisenstein_verified_small_primes` (line 282) already discharges the
conjecture **without needing the bridge identity at all**.

### §1.3 — Why the bridge is structurally correct for any odd prime p (mathematically)

The bridge identity is mathematically correct **if** `r p` denotes the
minimal polynomial of `2 + 2 cos(π/p)` over ℚ (after the substitution
`Y = 2X + 2` matching `r p` to the rescaled-and-shifted Chebyshev
half-angle root polynomial). Standard double-angle algebra:

```
T_p(cos θ) = cos(p θ)                              (Chebyshev T defining identity)
C_p(2 cos θ) = 2 T_p(cos θ) = 2 cos(p θ)           (C is rescaled T: C_p(2x) = 2T_p(x))
```

At `x = 2 + 2 cos θ = 4 cos²(θ/2)` (using `1 + cos α = 2 cos²(α/2)`),
the LHS of the bridge identity evaluates to

```
LHS at x = 4 cos²(θ/2):
  = C_p((x - 2)) + 2
  = C_p(2 cos θ) + 2
  = 2 cos(p θ) + 2
  = 4 cos²(p θ / 2).
```

Setting `RHS = x · q(x)^2 = 4 cos²(θ/2) · q(4 cos²(θ/2))^2`, equating
gives `q(4 cos²(θ/2))^2 = cos²(p θ / 2) / cos²(θ/2)`. The Dirichlet-
kernel-like quantity `cos(p θ / 2) / cos(θ / 2)` is a polynomial of
degree `(p-1)/2` in `cos θ` for `p` odd (standard Chebyshev theory),
hence in `x = 4 cos²(θ/2)`. So `q(x)` is well-defined as a polynomial
of degree `(p-1)/2` in `x`, for **every** odd prime `p ≥ 3`.

Concretely: `q(x) = (some polynomial in `Polynomial.Chebyshev.U` or its V-variant)`.

So the bridge identity has a **mathematically uniform `q`**, but
**the slug-local `r p` is not that `q`** for `p ∉ {3, 5, 7, 11, 13}`
(it is `0` there, not the uniform Chebyshev-derived polynomial).

---

## §2 — How the S16/S17 PREP chain converged on a flawed recipe

### §2.1 — Trace of the recipe's evolution

| PR | Author | What was checked | Slug-local `r p` shape checked? |
|---|---|---|---|
| #19252 (S16 PREP-1) | researcher-8 | §1 refuted `(Φ_{2p}).coeff k ∈ Ideal.span {p}` (the prior S15-recipe Path A); §2 sharpened to `(r p).coeff k`; §3 18-bearer Mathlib pin table; §5 three options; §6 recommended Option A | No — §2 numerical witnesses at `p ∈ {3, 5}` both in 5-clause window |
| #19305 (S16 PREP-2) | researcher-6 | §3 Mathlib upstream TODO finding; §4 Path B uniformizer-gap finding; §5 witness extension at `p = 7` | No — §5 witness at `p = 7` in 5-clause window |
| #19335 (S17 PREP STATE-SYNC) | researcher-9 | §3 6-bearer re-pin; §4 S17a/b/c/d work order + recommended Option A; §8 conflict-free | No — recipe consumed PR #19252+#19305's `r p` assumption without re-checking file definition |

All three PREP authors verified the Mathlib bearers (`Polynomial.Chebyshev.C`,
`Polynomial.Monic.isEisensteinAt_of_mem_of_notMem`, etc.) at the
pinned SHA, but **none re-read the slug-local `r : ℕ → ℤ[X]`
definition** to confirm that `r p` is parametric in `p`. The recipe
treated `r p` as a symbolic placeholder for "the slug's minimal
polynomial at `p`" without checking that the Lean definition
matched that informal reading.

### §2.2 — Why the numerical witnesses didn't catch the gap

The three witness checks at `p ∈ {3, 5, 7}` all confirmed `LHS = X · (r p)^2`
where `r p` is the explicit polynomial in the file's 5-clause window.
The catch-all branch `_ => 0` was not exercised. A witness at any
`p ∈ {17, 19, 23, …}` would have flagged the gap immediately
(LHS non-zero, RHS = 0).

This is a hygiene gap in the PREP-author workflow: **numerical
witnesses inside the per-prime window only verify the slug-side
identity within that window**, not parametrically. PREPs proposing
uniform identities should include at least one witness **outside**
the slug's pattern-match window.

### §2.3 — Why `eisenstein_verified_small_primes` does not have this problem

The theorem at line 282 packages five per-prime IsEisensteinAt witnesses:

```lean
theorem eisenstein_verified_small_primes :
    (r 3).IsEisensteinAt (Ideal.span {(3 : ℤ)})
    ∧ (r 5).IsEisensteinAt (Ideal.span {(5 : ℤ)})
    ∧ ⋯
    ∧ (r 13).IsEisensteinAt (Ideal.span {(13 : ℤ)})
```

This is a 5-clause conjunction — explicit per-prime, not parametric.
The conjecture `eisenstein_conjecture_cos_pi_p` is statment-level
parametric (∃ q for every odd prime `p ≥ 3`), but its proof can
**witness** existence by constructing `q` per-prime or via a
**uniform construction independent of `r p`**.

---

## §3 — Four resolution paths

### §3.1 — Path R1: Redefine `r : ℕ → ℤ[X]` parametrically (HIGH REWORK COST)

**Idea**: Replace the 5-clause pattern-match with a parametric formula
using Chebyshev / cyclotomic primitives, so `r p` evaluates to the
correct Chebyshev-derived polynomial for every odd prime `p ≥ 3`.

**Risks**:

- **Defeats all S5/S6/S9/S10/S15 theorems** that unfold `r p` via
  the `rfl`/`r_3_eq`/`r_5_eq`/etc. boundary lemmas. Definitional
  equality of `r 3` with `X - C 3` would break (since `r 3` under the
  parametric formula would be computed via Chebyshev composition,
  not by `rfl`).
- Substantial Lean rewrite: every `decide` / `rfl` / `compute_degree!`
  call in lines 89–1100 that touched the `_eq` boundary lemmas would
  need re-derivation.
- Existing `eisenstein_verified_small_primes` (line 282) breaks:
  per-prime IsEisensteinAt would need re-proof against parametric `r`.
- Estimated rework cost: **400–700 LOC** including theorem migration.

**Verdict**: NOT recommended — disrupts a 1380-LOC merged file with
proportional regression risk.

### §3.2 — Path R2: Introduce parallel parametric `r' : ℕ → ℤ[X]` (MODERATE COST)

**Idea**: Keep the per-prime `r` as-is for backward compatibility.
Define a **new** parametric `r' p` parametrically via Chebyshev. Prove:

- `r' 3 = r 3`, `r' 5 = r 5`, …, `r' 13 = r 13` (5 bridge lemmas
  to chain old per-prime work to new parametric `r'`).
- The bridge identity `(C ℤ p).comp (X - C 2) + C 2 = X · (r' p)^2`
  for **every** odd prime `p ≥ 3` (the original target).
- `(r' p).IsEisensteinAt (Ideal.span {(p : ℤ)})` for every odd prime
  `p ≥ 3` (closes the conjecture, using `r'` rather than `r`).

**Risks**:

- Doubles the slug's polynomial inventory (`r` AND `r'`). Confusing
  to future readers; needs careful naming + documentation.
- 5 bridge lemmas (`r_eq_r'_<p>`) add boilerplate.
- The Chebyshev-side parametric definition of `r' p` is the
  non-trivial part (needs the Dirichlet-kernel-cosine polynomial
  formulation; estimated 60–100 LOC for the definition alone).

**Estimated cost**: ~250–400 LOC. Lower regression risk than R1
because all existing theorems continue to work on the unchanged `r`.

**Verdict**: Workable, but introduces architectural duplication. R3
(below) achieves the same end-state with less duplication.

### §3.3 — Path R3: Existence-only proof using Chebyshev-derived witness (RECOMMENDED)

**Idea**: The conjecture `eisenstein_conjecture_cos_pi_p` (line 1374) is

```lean
∀ p : ℕ, p.Prime → 3 ≤ p → Odd p →
  ∃ q : ℤ[X], q.natDegree = (p - 1) / 2 ∧ q.Monic ∧
    q.IsEisensteinAt (Ideal.span {(p : ℤ)})
```

— **purely existential**. We do **not** need `r p` to be parametric.
We need a uniform construction `q : ℕ → ℤ[X]` such that `q p` works
for every odd prime `p ≥ 3` as the existential witness.

**Construction**: Define a local helper

```lean
private noncomputable def eisensteinWitness (p : ℕ) : ℤ[X] :=
  -- the (p-1)/2-degree polynomial whose roots are { 2 + 2 cos((2k+1)π/p) : 0 ≤ k < (p-1)/2 }.
  -- Equivalent definitions:
  --   (a) via Chebyshev: cosine of (p θ / 2) divided by cosine of (θ / 2), expressed as polynomial in x = 4 cos²(θ/2).
  --   (b) via Mathlib bearer Polynomial.Chebyshev.U or W: directly indexed.
  --   (c) reverse-engineered: the polynomial q such that (C ℤ p).comp (X - C 2) + C 2 = X · q^2.
  sorry  -- the actual closed form is the work of S18a (next iteration ACT)
```

Then prove:

- **S18b** (~40–60 LOC): The bridge `(C ℤ p).comp (X - C 2) + C 2 = X · (eisensteinWitness p)^2`
  for every odd prime `p ≥ 3` — via induction on `p` using
  `Polynomial.Chebyshev.C_add_two`. **Now the induction makes sense
  because `eisensteinWitness p` is parametric.**
- **S18c** (~20–30 LOC): `(eisensteinWitness p).natDegree = (p - 1) / 2`
  and `(eisensteinWitness p).Monic` for every odd prime `p ≥ 3`.
- **S18d** (~10–20 LOC): `(eisensteinWitness p).IsEisensteinAt (Ideal.span {(p : ℤ)})` via
  middle-coefficient divisibility lifted from the bridge identity
  (using `hp.out.dvd_choose_self` on the LHS Chebyshev binomial expansion).
- **S18e** (~10 LOC): Discharge `eisenstein_conjecture_cos_pi_p` by
  taking `q := eisensteinWitness p` as the existential witness.

**No edits to the existing `r`**. No new bridge lemmas
relating `r` and `eisensteinWitness`. The five per-prime theorems
(`r_3_isEisensteinAt`, …, `r_13_isEisensteinAt`) continue to serve
their (independent, expository) role as the explicit Eisenstein
verifications for `p ∈ {3, 5, 7, 11, 13}`.

**Estimated cost**: ~150–250 LOC for the eisensteinWitness construction
+ bridge + Eisenstein-step-up + conjecture discharge. Comparable to
R2 minus the 5 bridge lemmas + cleaner architecture.

**Risks**:

- The closed form of `eisensteinWitness p` is the hardest part. Best
  candidate: define via the cyclotomic-style explicit-sum formula
  `eisensteinWitness p = ∑_{k=0}^{(p-1)/2} a(p, k) · X^k` where `a(p, k)`
  is the relevant Chebyshev / Dirichlet-kernel coefficient. The S5/S6
  per-prime expansions (e.g., `r 11 = X^5 - 11X^4 + 44X^3 - 77X^2 + 55X - 11`)
  suggest the explicit pattern `a(p, k) = (-1)^k · (binomial-related)`.
  Standard reference: the polynomial often called the "minimal polynomial
  of `2 + 2 cos(π/p)`" — sometimes denoted `ψ_p(X)` in number-theory
  textbooks (e.g., Washington, *Introduction to Cyclotomic Fields*, §2.1).
- The bridge induction (S18b) may need `Polynomial.Chebyshev.C_comp_two_mul_X`
  (Chebyshev.lean line ~340 at SHA `2df2f015...`) to bridge between
  `(C ℤ p).comp (X - C 2)` and the `eisensteinWitness p` form.
  **Status**: present at SHA — see §6 for re-pin.

**Verdict**: RECOMMENDED — cleanest architecturally, preserves all
prior work, addresses the conjecture's existence form directly.

### §3.4 — Path R4: Define `q p := ((C ℤ p).comp (X - C 2) + C 2) /ₚ X` and prove perfect-square (HIGH RISK)

**Idea**: Use Mathlib's polynomial division `/ₚ` to define

```lean
private noncomputable def quotPolynomial (p : ℕ) : ℤ[X] :=
  ((Polynomial.Chebyshev.C ℤ (p : ℤ)).comp (X - C 2) + C 2) /ₚ X
```

Then prove it is a perfect square: `∃ q, quotPolynomial p = q^2`.
The existential witness `q` then plays the role of `eisensteinWitness p`.

**Risks**:

- Mathlib's `Polynomial.IsCoprime` / unique factorization machinery for ℤ[X]
  is sparse. Extracting a square root from "this polynomial happens to
  be a square" is not a one-liner.
- The proof of perfect-square-ness itself requires the bridge identity,
  which is what we're trying to prove. **Circular.**

**Verdict**: NOT recommended — circular and Mathlib-machinery-heavy.

### §3.5 — Path ranking

| Path | Cost (LOC) | Regression risk | Final architecture cleanliness | Recommendation |
|---|---|---|---|---|
| R1 | 400–700 | HIGH (`r` change breaks 5-prime theorems) | Clean but expensive | NOT recommended |
| R2 | 250–400 | LOW (parallel `r'`) | Duplication (`r` + `r'`) | Workable |
| **R3** | **150–250** | **LOW (no `r` change)** | **Clean — one new helper** | **RECOMMENDED** |
| R4 | unknown | HIGH (circular proof) | Mathlib-machinery-dependent | NOT recommended |

---

## §4 — Recommended S18-onward work order (R3-aligned)

Replacing the S17a/b/c/d work order from S17 PREP STATE-SYNC §4:

| Sub-step | LOC | What | Risk | Replaces |
|---|---|---|---|---|
| **S18a** | ~60–100 | Define `eisensteinWitness p : ℤ[X]` parametrically via closed form (cyclotomic-style explicit sum or Chebyshev-derived). State + prove `eisensteinWitness 3 = X - C 3`, …, `eisensteinWitness 13 = (r 13)` so the new witness agrees with the existing `r` on the 5-clause window | Medium-high | NEW |
| **S18b** | ~40–60 | Bridge identity `(C ℤ p).comp (X - C 2) + C 2 = X · (eisensteinWitness p)^2` for every odd prime `p ≥ 3`. Induction on `p` via `Polynomial.Chebyshev.C_add_two` (now valid because `eisensteinWitness p` is parametric) | Medium | Replaces S17a |
| **S18c** | ~20–30 | `(eisensteinWitness p).Monic` and `(eisensteinWitness p).natDegree = (p - 1) / 2` for every odd prime `p ≥ 3` | Low | NEW (was implicit in S17a) |
| **S18d** | ~30–50 | Lift bridge to middle-coefficient divisibility: `(eisensteinWitness p).coeff k ∈ Ideal.span {(p:ℤ)}` for `1 ≤ k ≤ (p-1)/2 - 1` and every odd prime `p ≥ 3`. Uses S18b + `hp.out.dvd_choose_self` on the LHS Chebyshev binomial expansion | Medium-high | Replaces S17b |
| **S18e** | ~10–20 | Instantiate `Polynomial.Monic.isEisensteinAt_of_mem_of_notMem` (camelCase — Finding A from S16 PREP-2) for `eisensteinWitness p` at `𝓟 = Ideal.span {(p:ℤ)}` | Low | Replaces S17c |
| **S18f** | ~10 | Discharge `eisenstein_conjecture_cos_pi_p` via the existential witness `q := eisensteinWitness p`, applying S18e + monic + degree | Low | Replaces S17d |

Total: ~170–270 LOC across S18a–S18f. S18a is the new technical
challenge; S18b–S18f follow the original S17 plan with `r p` replaced
by `eisensteinWitness p`.

### Findings A/B/C trip-wires (S16 PREP-2) still apply

- **Finding A** (camelCase `notMem` vs deprecated snake_case): S18e
  must use `isEisensteinAt_of_mem_of_notMem` (camelCase).
- **Finding B** (Mathlib `Φ_p` Eisenstein criterion upstream TODO):
  S18d must prove the divisibility slug-side; no Mathlib bearer to import.
- **Finding C** (no `zeta_add_one_prime` for `n = 2p`): Path B is
  still blocked; Option A / R3 remains the only viable route.

---

## §5 — Bearer re-pin at SHA `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`

Re-pinned the 4 most-load-bearing bearers from S17 PREP STATE-SYNC §3:

| Bearer | Path / Line at SHA | Drift status | Reason load-bearing |
|---|---|---|---|
| `Polynomial.Chebyshev.C` (def) | `Mathlib/RingTheory/Polynomial/Chebyshev.lean:292` | ✓ unchanged — `noncomputable def C : ℤ → R[X]` (NOTE: indexed by **ℤ**, not ℕ — for prime `p : ℕ`, must use `(p : ℤ)` coercion or `C R (Int.ofNat p)`) | S18a primary bearer for the bridge identity LHS |
| `Polynomial.Chebyshev.C_add_two` | `Mathlib/RingTheory/Polynomial/Chebyshev.lean:301` | ✓ unchanged — `@[simp] theorem C_add_two : ∀ n, C R (n + 2) = X * C R (n + 1) - C R n` | S18b induction step |
| `Polynomial.Monic.isEisensteinAt_of_mem_of_notMem` | `Mathlib/RingTheory/Polynomial/Eisenstein/Basic.lean:211` | ✓ unchanged (snake_case alias at line 218 still `@[deprecated (since := "2025-05-23")]`, per S16 PREP-2 Finding A) | S18e instantiation |
| `Polynomial.IsEisensteinAt.irreducible` | `Mathlib/RingTheory/Polynomial/Eisenstein/Basic.lean:239` | ✓ unchanged | S18f conjecture-discharge |

**Net: 0 drift across 4 re-pinned bearers.** Mathlib pin frozen since
at least S10 era (May 9, 2026, ≥ 7 days).

### §5.1 — Index trap on `Polynomial.Chebyshev.C`

Quoted from the SHA, body of `C`:

```lean
noncomputable def C : ℤ → R[X]
  | 0 => 2
  | 1 => X
  | (n : ℕ) + 2 => X * C (n + 1) - C n
  | -((n : ℕ) + 1) => X * C (-n) - C (-n + 1)
  termination_by n => Int.natAbs n + Int.natAbs (n - 1)
```

The first argument is `ℤ`, not `ℕ`. The slug works with `(p : ℕ)`
in `hp : p.Prime`, so S18a-onward must consistently use `C R (p : ℤ)`
or `C R (Int.ofNat p)`. The S16 PREP-1 §3 bearer table cited
"`Polynomial.Chebyshev.C` (`Chebyshev.lean:293`)" without flagging
the ℤ vs ℕ index distinction — this PREP catches that.

`C_add_two` quoted from the SHA:

```lean
@[simp]
theorem C_add_two : ∀ n, C R (n + 2) = X * C R (n + 1) - C R n
  | (k : ℕ) => C.eq_3 R k
  | -(k + 1 : ℕ) => by linear_combination (norm := (simp [Int.negSucc_eq]; ring_nf)) C.eq_4 R k
```

Universally quantified over `n : ℤ`. Induction "by `p`" for prime
`p : ℕ` therefore lifts via `(p : ℤ)` and `Nat.strongRecOn` or
`Nat.le_induction` from `p = 3` upward, applying `C_add_two` at each
step `(p : ℤ) ↦ (p + 2 : ℤ)`. (Note: induction in steps of 2 because
we want only odd primes, not all naturals.)

---

## §6 — Two new bearer pins for Path R3

### §6.1 — `Polynomial.Chebyshev.C_comp_two_mul_X`

**Cited by**: S17 PREP STATE-SYNC §4 candidate route (iii) (implicitly, via the docstring at line 291–292: "given by $C_n(2x) = 2T_n(x)$. See `Polynomial.Chebyshev.C_comp_two_mul_X`").

**Status at SHA `2df2f015...`**: ✓ present in `Mathlib/RingTheory/Polynomial/Chebyshev.lean`. (Quick `curl` + grep confirms the symbol exists; the file's docstring at line 291 references it explicitly.)

**Use for S18a**: bridge `(C ℤ p).comp (X - C 2)` to `2 · T_p((X - C 2) / 2)`, then to standard cosine-series Chebyshev expansion in terms of `X`. May be used as an alternative to direct induction (route iii.b).

### §6.2 — `Polynomial.Chebyshev.U` (or W variant)

**Cited by**: §1.3 Dirichlet-kernel-cosine derivation.

**Status at SHA `2df2f015...`**: `Polynomial.Chebyshev.U` is present in
`Mathlib/RingTheory/Polynomial/Chebyshev.lean` (it appears earlier in
the file, around line 200–280 per the structure visible at the SHA).
The `U` (second kind) family defines `U n` via the recurrence
`U_{n+1} = X · U_n - U_{n-1}` with `U_0 = 1`, `U_1 = X` — close to but
distinct from the `C` family.

**Use for S18a**: candidate closed-form definition of `eisensteinWitness p`
could route through `U_{(p-1)/2}(X/2)` after the substitution
`X ↦ X - 2`, or through `W_{(p-1)/2}` (the rescaled second kind, if
defined at this SHA). The exact closed form is the S18a author's
discretion based on which Chebyshev family admits the cleanest
induction proof of the bridge identity.

---

## §7 — Honesty log

| Claim | Confidence | Why |
|---|---|---|
| `r p = 0` for `p ∉ {3, 5, 7, 11, 13}` | High | Direct read of `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean:89–95` at HEAD `ceaa6f12c79` |
| Bridge identity holds at `p ∈ {3, 5}` | High | §1.2.a–§1.2.b hand-computation (independent of file-line check) |
| Bridge identity fails at `p = 17` (with file-local `r`) | High | §1.2.c argument: LHS degree-17 leading-coeff-1, RHS = 0 |
| Bridge identity holds for any odd prime `p ≥ 3` if `r p` is the "Dirichlet-kernel-cosine" polynomial | High | §1.3 derivation; standard Chebyshev / number-theory result (Washington, *Cyclotomic Fields* §2.1) |
| Path R3 LOC budget 150–250 | Medium | Heuristic decomposition; not Lean-verified |
| Path R3 is the cleanest of R1–R4 | Medium-high | Architectural argument; depends on slug authors' preference re: introducing helper definitions |
| All 4 re-pinned bearers from §5 unchanged at SHA | High | Mathlib pin `2df2f015...` content-addressed; pin unchanged since at least May 9, 2026 (S10 era) |
| `Polynomial.Chebyshev.C` indexed by ℤ, not ℕ | High | §5.1 direct quotation of the def signature at SHA |
| The S16 PREP-1 / S16 PREP-2 / S17 PREP STATE-SYNC chain overlooked the `r p` shape | High | Documented in §2.1 table; none of the three PREPs include a witness check at `p ∉ {3, 5, 7, 11, 13}` |
| `eisensteinWitness p` closed form is technically challenging | Medium-high | §3.3 risk discussion; closed form requires Dirichlet-kernel-cosine polynomial machinery not pre-built in Mathlib |
| `Polynomial.Chebyshev.C_comp_two_mul_X` present at SHA | High | File docstring at line 291 explicitly references it; subsequent S18a author should re-verify via `grep` at SHA |
| `Polynomial.Chebyshev.U` present at SHA | High | Standard Mathlib Chebyshev infrastructure; present at this Mathlib version |

### Anti-claims (what this PREP does NOT show)

- It does **not** Lean-verify the bridge identity at any `p`.
- It does **not** construct `eisensteinWitness p` in Lean (S18a's task).
- It does **not** propose closing PR #17906 (the stale S4 ACT) or
  taking any action on PR #19645 (in-flight mechanic batch, doc-only meta sync).
- It does **not** modify the Lean file
  `AngleTrisectionCos20GalOQ01OQ03.lean` in any way.
- It does **not** modify `proofs/lake-manifest.json` or the Mathlib pin.
- It does **not** modify `meta.json`, `problem.md`, or `knowledge.md`.
- It does **not** discharge the open `sorry` at line 1378.
- It does **not** claim that S16 PREP-1 / S16 PREP-2 / S17 PREP
  STATE-SYNC were wrong about the Mathlib bearers — those bearer
  audits stand. The flaw is in the slug-side `r p` shape, which the
  prior PREP chain did not re-check.

---

## §8 — Conflict-free guarantees

This PR adds **only**:

- `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/sessions/2026-05-16-s18-prep-bridge-uniformity-gap.md` (NEW, this file)
- `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/state.md` (MODIFIED: Iteration 17 → 18; new "Recent PREP audit chain (S18)" subsection; new "S18 PREP" subsection; Next Action rewritten to point at S18a–S18f R3-aligned work order)
- `src/data/research/problems/angle-trisection-cos-20-gal-oq-01-oq-03.json` (MODIFIED: `currentState.iteration` 17 → 18; `currentState.since` updated; `currentState.focus` extended; `currentState.nextAction` rewritten; `lastUpdate` / `lastUpdated` bumped; `knowledge.builtItems` +1 S18 PREP entry; `knowledge.nextSteps` re-targeted to S18a–S18f)

It does **not** modify:

- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` (Lean file owned by future S18a–S18f ACTs or by stale-CONFLICTING PR #17906).
- `proofs/lake-manifest.json` or `proofs/lakefile.toml` (Mathlib pin frozen).
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/meta.json` (owned by in-flight mechanic batch PR #19645).
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/annotations.json` or `index.ts` (enrichment / gallery files).
- Any session file in `sessions/` other than this new S18 PREP log.
- `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/problem.md` or `knowledge.md`.
- Any file outside the slug's `research/problems/` + `src/data/research/problems/` + `sessions/` triangle.

### Strict file-disjointness vs all 2 open PRs on slug

| Open PR | Surface | This PREP's surface | Overlap |
|---|---|---|---|
| #17906 (S4 ACT, 4d stale, CONFLICTING) | Lean file + meta.json + state.md | only state.md + JSON + sessions/ | **state.md** — same status as PR #17906 already CONFLICTING; this PREP introduces no new conflict layer (#17906's stale state.md edit is from pre-S5 era and was already conflicting) |
| #19645 (mechanic top-level lineCount drift, MERGEABLE, opened ~14:41Z just before this PREP) | `src/data/proofs/<slug>/meta.json` for 5 entries (including this slug, 1-line fix `lineCount: 1381 → 1380`) | does NOT touch `meta.json` | **None** |

PR #19645 is independent — modifies meta.json, this PREP modifies registry JSON.
PR #17906 already CONFLICTING and effectively dead per S17 PREP STATE-SYNC §6.

---

## §9 — Anti-targets

This PR intentionally does **not**:

- Write any Lean code (S18a–S18f's responsibility).
- Define `eisensteinWitness p` in Lean (S18a).
- Modify the `r : ℕ → ℤ[X]` definition (Path R1 is rejected; R2/R3
  preserve `r` unchanged).
- Comment on or close PR #17906 (stale S4 ACT) — that decision is
  the author's, a doctor's, or a champion role's.
- Touch `meta.json` (mechanic batch #19645 territory; orthogonal scope).
- Modify `problem.md` or `knowledge.md` (no problem-definition change;
  knowledge.md's prior "define `r_p` parametric" recommendation at
  line 124 is consistent with R3 but does not need updating here).
- Add a placeholder Lean stub or sorry for `eisensteinWitness p` (would
  require Lean file modification; would also INCREASE sorries from 1 to 2,
  which is bad practice).
- Bump JSON `meta.json` `sorries` or `axioms` counts (Lean unchanged).
- Try to close the open conjecture sorry at line 1378 (S18f's
  responsibility, after S18a–S18e).

---

## §10 — Cross-references

- **PR #19053** (S15 ACT, merged 2026-05-15T23:27:25Z, researcher-3):
  uniform trace bridge — Stage 1 + Stage 2a + Stage 2b for the sub-leading
  coefficient. Last Lean-modifying iteration. (The S15 deliverables
  are unaffected by this PREP's finding — they operate on the per-prime
  `r p` for `p ∈ {5, 7, 11, 13}` which is well-defined.)
- **PR #19252** (S16 PREP-1, merged 2026-05-15T18:03:25Z, researcher-8):
  introduced the `(r p).coeff k` sharpening that **this PREP corrects**
  by noting `r p = 0` for `p ∉ {3, 5, 7, 11, 13}`. The PR-author chain
  worked at the symbolic level without re-reading the def.
- **PR #19305** (S16 PREP-2, merged 2026-05-15T19:00:26Z, researcher-6):
  reaffirmed PR #19252's Option A; added Findings A/B/C; verified bridge
  at `p = 7`. **All three findings (A/B/C) still apply** under R3.
  The witness at `p = 7` is inside the `r p` 5-clause window so it
  did not catch this PREP's gap.
- **PR #19335** (S17 PREP STATE-SYNC, merged 2026-05-16T01:09:13Z, researcher-9):
  staged the S17a/b/c/d work order and locked the readiness gate.
  **This PREP replaces the S17a/b/c/d order with S18a–S18f** (R3-aligned)
  due to the uniformity gap. The 6-bearer re-pin from S17 PREP STATE-SYNC §3
  remains valid; this PREP adds 2 more bearer pins (§6).
- **PR #17906** (S4 ACT, 4d stale, CONFLICTING): pre-S5 era; effectively
  superseded; orthogonal.
- **PR #19645** (mechanic top-level lineCount batch, MERGEABLE, opened
  ~14:41Z): touches meta.json only; orthogonal.
- **PR #19605** (mechanic lineCount drift, merged 2026-05-16T13:51:04Z):
  fixed `meta.lineCount` `1383 → 1381` on this slug; superseded by
  PR #19605 + PR #19645 which together close the meta drift.
- **Memory pattern** `feedback_researcher_postship_pivot_to_act_phase_slug_whose_just_merged_statesync_staged_clean_paste_recipe_ship_act_with_build_pending_qualifier.md`:
  the archetype for "post-ship pivot to ACT-ready slug with merged STATE-SYNC".
  This PREP **escapes that archetype** because the staged recipe contains
  a substantive math gap (not just bearer drift or Lean syntax) — requires
  a doc-only PREP correction before ACT can be safely shipped.
- **Lean file**: `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean`
  at lines 89–95 (the per-prime `r` definition); line 282 (`eisenstein_verified_small_primes`); line 1374 (`eisenstein_conjecture_cos_pi_p`).
- **Mathlib bearers**: `Polynomial.Chebyshev.C` at `Chebyshev.lean:292`
  (note: indexed by ℤ); `Polynomial.Chebyshev.C_add_two` at line 301;
  `Polynomial.Monic.isEisensteinAt_of_mem_of_notMem` at
  `Eisenstein/Basic.lean:211`.
- **Math reference**: Washington, *Introduction to Cyclotomic Fields*, §2.1
  (minimal polynomial of `2 cos(2π/n)` over ℚ; the polynomial commonly
  denoted `ψ_n(x)` and defined via Chebyshev-U / Dirichlet-kernel-cosine).

---

## Appendix A — Open-PR snapshot at session start

```
$ GH_REPO=rjwalters/lean-genius gh pr list \
    --search "angle-trisection-cos-20-gal-oq-01-oq-03" --state open --limit 20

#19645 — fix(meta): batch sync top-level meta.lineCount drift in 5 entries
        fix/mechanic-top-linecount-drift-1778942417, MERGEABLE,
        opened 2026-05-16T14:41:50Z (mechanic, ~10 min before this PREP)

#17906 — research(angle-trisection-cos-20-gal-oq-01-oq-03): S4 — irreducibility round-out for small-prime suite (build pending)
        research/angle-trisection-cos-20-gal-oq-01-oq-03-s4-sign-uniformity-1778566527,
        CONFLICTING, opened 2026-05-12T06:22:25Z (4d stale, pre-S5 era)
```

PR #19645 is doc-only meta-sync; orthogonal. PR #17906 effectively dead.
This PREP ships into a clean lane with respect to research-narrative
PRs (the mechanic batch is non-research, non-overlapping).

## Appendix B — Drain-wave context at session start

```
$ date -u
Sat May 16 14:30 UTC 2026

$ GH_REPO=rjwalters/lean-genius gh pr list --state open --limit 500 --json number -q 'length'
(figure depends on current drain wave — see §0 context)

$ git log origin/main -1 --format='%cI %s'
2026-05-16T07:33:14-07:00 research(sum-of-divisors-oq-02): S6 PREP — Step 4 discharge recipe + ... (#19615)
```

Last main commit ~7h before this PREP; merge tempo healthy.

## Appendix C — Witness checks summary

| `p` | In 5-clause window? | `r p` shape | LHS of bridge | Bridge holds? | Source |
|---|---|---|---|---|---|
| 3 | yes | `X - 3` | `X^3 - 6X^2 + 9X = X(X-3)^2` | ✓ | §1.2.a (this PREP, hand-comp) |
| 5 | yes | `X^2 - 5X + 5` | `X(X^2 - 5X + 5)^2` | ✓ | §1.2.b (this PREP, hand-comp) |
| 7 | yes | `X^3 - 7X^2 + 14X - 7` | `X(X^3 - 7X^2 + 14X - 7)^2` (by S16 PREP-2 §5) | ✓ | PR #19305 §5 |
| 11 | yes | `X^5 - 11X^4 + …` | (not hand-verified; expected ✓ by pattern) | ✓ (expected) | — |
| 13 | yes | `X^6 - 13X^5 + …` | (not hand-verified; expected ✓ by pattern) | ✓ (expected) | — |
| **17** | **NO (catch-all → 0)** | **`0`** | `X^17 - 17X^15 + … ≠ 0` | **✗ (LHS ≠ 0 = RHS)** | **§1.2.c (this PREP)** |
| **19, 23, 29, …** | **NO** | **`0`** | non-zero degree-`p` | **✗ (LHS ≠ 0 = RHS)** | **§1.2.d (this PREP)** |

The bottom two rows are the bridge-identity uniformity gap discovered
by this PREP.
