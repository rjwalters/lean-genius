# Knowledge Base: e-transcendental-oq-03-oq-01

Feasibility of formalizing the continued-fraction analysis of μ(e) = 2 via
Mathlib's `GenContFract`.

---

## Bottom line

**Partially formalizable today.** Mathlib's `GenContFract` (the namespace
formerly called `GeneralizedContinuedFraction`) already supplies the *general*
convergent-approximation theory for arbitrary reals — but **not** the two
ingredients specific to closing μ(e) = 2:

1. the **convergent lower bound** (the reverse of `abs_sub_convs_le`), and
2. the **specific continued-fraction expansion of e** (Euler 1737,
   `e = [2; 1, 2, 1, 1, 4, 1, 1, 6, …]`).

The parent's remaining axiom `e_not_liouvilleWith_gt_two` rests on *both*.

---

## What Mathlib already provides (verified, in current toolchain v4.26.0)

All in `Mathlib/Algebra/ContinuedFractions/**` and
`Mathlib/NumberTheory/DiophantineApproximation/**`:

| Result | Lemma | Content |
|---|---|---|
| CF algorithm for a real | `GenContFract.of v` | regular CF of any `v : ℝ` |
| Exact error formula | `GenContFract.sub_convs_eq` | `v - convs n = (-1)^n / (Bₙ(frₙ⁻¹Bₙ + Bₙ₋₁))` |
| **Upper** error bound | `GenContFract.abs_sub_convs_le` | `|v - convs n| ≤ 1/(densₙ · densₙ₊₁)` |
| Weaker upper bound | `GenContFract.abs_sub_convergents_le'` | `|v - convs n| ≤ 1/(bₙ · densₙ²)` |
| Denominator monotonicity | `GenContFract.of_den_mono` | `densₙ ≤ densₙ₊₁` |
| Fibonacci growth of dens | `GenContFract.succ_nth_fib_le_of_nth_den` | `fib(n+1) ≤ densₙ` |
| Continuant recurrence | `GenContFract.contsAux_recurrence`, `dens_recurrence` | `Bₙ₊₁ = bₙ₊₁Bₙ + Bₙ₋₁` |
| Convergence | `GenContFract.of_convergence` | `convs n → v` |
| `bₙ ≥ 1` (partial dens) | `GenContFract.of_one_le_get?_partDen` | regular-CF partial denominators ≥ 1 |
| `frₙ⁻¹` vs `bₙ₊₁` | `IntFractPair.succ_nth_stream_b_le_nth_stream_fr_inv`, `nth_stream_fr_lt_one` | `bₙ₊₁ ≤ frₙ⁻¹ < bₙ₊₁ + 1` |
| Legendre best-approx | `Real.exists_rat_eq_convergent` | `|ξ-q| < 1/(2·q.den²) ⟹ q` is a convergent |
| Dirichlet @ exp 2 | `Real.infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational` | irrational ⟹ ∞-many `q` with `|ξ-q|<1/q.den²` |
| Irrational ⟺ ∞ approx | `Real.infinite_rat_abs_sub_lt_one_div_den_sq_iff_irrational` | the iff |

The **lower-bound half of the irrationality measure (μ(e) ≥ 2)** is therefore
*already* fully available: the parent file `ETranscendentalOQ03.lean` proves
`irrational_liouvilleWith_two` outright (no axiom) — this is the constructive
Dirichlet direction, and Mathlib's `infinite_rat_abs_sub_lt_one_div_den_sq_of_irrational`
is exactly the engine.

---

## The two genuine gaps for μ(e) ≤ 2

### Gap 1 — convergent **lower** bound (general, e-independent)

Mathlib exposes only `≤` (`abs_sub_convs_le`). The matching `>` is **not** a
public lemma, although it follows cleanly from the *exact* formula
`sub_convs_eq` that Mathlib already proves internally:

From `sub_convs_eq` (with `frₙ ≠ 0`, i.e. not terminated at `n`):

```
|v - convs n| = 1 / (densₙ · (frₙ⁻¹·densₙ + densₙ₋₁)).
```

Because `frₙ⁻¹ < bₙ₊₁ + 1` (since `0 ≤ fract(frₙ⁻¹) < 1`) and the continuant
recurrence gives `densₙ₊₁ = bₙ₊₁·densₙ + densₙ₋₁`, one gets

```
frₙ⁻¹·densₙ + densₙ₋₁ < (bₙ₊₁+1)·densₙ + densₙ₋₁ = densₙ₊₁ + densₙ,
```

hence the **two-sided bracket**

```
1 / (densₙ · (densₙ₊₁ + densₙ))  <  |v - convs n|  ≤  1 / (densₙ · densₙ₊₁).
```

This is e-independent and is the right reusable Mathlib-style lemma. It is the
direct analogue of `abs_sub_convs_le` and the obvious upstream contribution. A
draft statement + proof sketch is in
`proofs/Proofs/ETranscendentalOQ03OQ01.lean` (see Verification status below).

With this bracket, "partial quotients `aₙ = O(n)`" ⟹ `densₙ₊₁/densₙ` bounded ⟹
`|v - p/q| > c/q²` for convergents ⟹ (via Legendre `exists_rat_eq_convergent`,
which forces every sufficiently good rational to *be* a convergent)
`¬ LiouvilleWith p v` for all `p > 2`. So Gap 1 + Legendre is a complete,
e-independent route to "bounded-growth partial quotients ⟹ irrationality
measure exactly 2."

### Gap 2 — the CF expansion of e (e-specific, deep)

Mathlib has **no** formalization of Euler's `e = [2; 1, 2, 1, 1, 4, 1, 1, 6, …]`,
nor the bound `aₙ = O(n)` on its partial quotients. The classical proofs are
Hermite's integral identity or Cohn's "a short proof of the simple continued
fraction expansion of e" (Amer. Math. Monthly, 2006). This is the genuinely
hard, multi-hundred-line piece and is the real obstruction; it is *not* a thin
wrapper over existing Mathlib.

---

## Concrete formalization plan to discharge `e_not_liouvilleWith_gt_two`

1. **[general, ~40–80 lines]** Prove `convs_dist_lower` (Gap 1) from
   `sub_convs_eq` + `contsAux_recurrence` + `succ_nth_stream_b_le_nth_stream_fr_inv`.
2. **[general, ~80–150 lines]** "geometric denominator growth ⟹ `¬LiouvilleWith p`
   for `p>2`", using step 1 and `Real.exists_rat_eq_convergent`.
3. **[e-specific, DEEP]** Formalize Euler's CF of e and `aₙ = O(n)` (Cohn/Hermite).
4. Combine 2 + 3 to replace the axiom.

Steps 1–2 are tractable now; step 3 is the blocker. So the honest answer to the
child question: **the general convergent machinery is formalizable from Mathlib
today (and steps 1–2 are the right next deliverables); the e-specific expansion
is the remaining deep gap.**

---

## Verification status (IMPORTANT — honesty)

This session had **no working Lean build**: Docker daemon was unresponsive
(`docker info` timed out), no host `elan`/`lake` toolchain was installed, and the
Aristotle prover API returned HTTP 404 (service down). Therefore the draft file
`ETranscendentalOQ03OQ01.lean` is **UNVERIFIED** — its upper-bound proof is a
best-effort attempt against the documented Mathlib API and the lower bound is
left as a structured `sorry` with the proof sketch above. It is **not wired to
the gallery** and must be built/verified before any "verified" claim. The survey
content above (Mathlib lemma inventory + gap analysis) is what this session
stands behind; it is an API/literature survey that needs no build.

---

## Dead ends / cautions

- Do not claim μ(e)=2 is "fully formalized": Gap 2 (e's CF expansion) is open in
  this repo and in Mathlib.
- `abs_sub_convergents_le'` (the `1/(bₙ·densₙ²)` bound) is *weaker* than
  `abs_sub_convs_le`; do not use it where the sharp bound is needed.
- The lower bound is **strict** `<`; in the terminating (rational) case the error
  equals the upper bound `1/(densₙ·densₙ₊₁)`, but for irrational `v` the stream
  never terminates so the bracket is non-degenerate at every `n`.
