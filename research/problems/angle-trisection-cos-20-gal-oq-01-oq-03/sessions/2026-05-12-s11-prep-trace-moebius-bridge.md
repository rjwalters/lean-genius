# S11 PREP — Trace fingerprint via Möbius `μ(2p) = 1` (corrected cyclotomic bridge)

**Date**: 2026-05-12
**Researcher**: researcher-12
**Mode**: PREP (doc-only design memo)
**Status**: pristine orthogonal to in-flight S4 PR #17906
(build-pending, same file but different theorem)

## Why this PREP — and an arithmetic-correction note

State.md S11 next-action proposes the bridge

```
r_subLeadingCoeff_eq_neg_cyclotomic_uniform :
    ∀ p ∈ ({5, 7, 11, 13} : Finset ℕ),
      (r p).coeff ((p-1)/2 - 1) = -(cyclotomic (2*p) ℤ).subLeadingCoeff
```

as the "uniform cyclotomic" reformulation of the S4 statement
`r_subLeadingCoeff_eq_neg_p` (`(r p).coeff ((p-1)/2 - 1) = -p`).
**This bridge does not arithmetic-check.** For `p = 5`:

- `Φ_{10}(X) = X^4 - X^3 + X^2 - X + 1`, so
  `(cyclotomic 10 ℤ).subLeadingCoeff = -1`.
- The RHS becomes `-(-1) = 1`, but the LHS is `(r 5).coeff 1 = -5`.
  `1 ≠ -5`.

The state.md sketch must mean something stronger. This PREP **derives
the correct cyclotomic bridge** and proposes the right uniform
statement for S11 ACT to target.

## 1. The correct identity (via the trace of `2 + 2 cos(π/p)`)

### Setup — roots of `r p`

The roots of `r p` are
`θ_{p, k} := 2 + 2 cos((2k - 1) π / p)` for `k = 1, …, (p-1)/2`.
The argument `(2k-1)π/p` ranges over the **odd-indexed** angles in
`(0, π)`; the corresponding 2*p*-th roots of unity are
`ω_{p, k} := exp(i · (2k-1) π / p)`, which are the primitive 2*p*-th
roots of unity in the upper half-plane.

### Trace by Vieta

`r p` is monic of degree `(p-1)/2`, so

```
(r p).coeff ((p-1)/2 - 1) = - Σ_{k=1}^{(p-1)/2} θ_{p, k}
                          = -(p - 1) - 2 · Σ_{k=1}^{(p-1)/2} cos((2k-1)π/p)
```

(the `-(p - 1)` arises from `(p-1)/2 · 2` summed over `k`).

### Cosine half-sum as a Möbius value

The full sum of **all** primitive 2*p*-th roots of unity is the
Möbius value:

```
Σ_{prim. 2p-th roots} ω = μ(2 p)
```

For `p` odd prime: `μ(2 p) = μ(2) · μ(p) = (-1) · (-1) = 1`.

The primitive 2*p*-th roots pair as
`{ω_{p, k}, \overline{ω_{p, k}}}` for `k = 1, …, (p-1)/2`. Each pair
sums to `2 Re(ω_{p, k}) = 2 cos((2k-1) π / p)`. Hence

```
2 · Σ_{k=1}^{(p-1)/2} cos((2k-1) π / p) = Σ_{prim. 2p-th roots} ω = μ(2 p) = 1.
```

### Plug in

```
(r p).coeff ((p-1)/2 - 1) = -(p - 1) - 1 = -p.
```

This recovers the S4 statement and exhibits **why** the answer is
`-p`: the `-(p - 1)` is the leading-order Vieta contribution from
the "2" constant offset in `θ`, and the `-1` is the Möbius-driven
correction.

### The corrected cyclotomic bridge

The above derivation shows the right cyclotomic bridge is

```
r_traceCoeff_via_cyclotomic :
    ∀ p ∈ ({5, 7, 11, 13} : Finset ℕ),
      (r p).coeff ((p-1)/2 - 1)
        = -((p : ℤ) - 1) - (Σ over primitive 2p-th roots ω of ω as int) := …
```

But the `Σ over primitive 2p-th roots ω` is **not** the sub-leading
coefficient of `Φ_{2 p}` — sub-leading is the trace, *which is the
same Möbius value*:

```
(cyclotomic (2 * p) ℤ).coeff (Polynomial.natDegree (cyclotomic (2 * p) ℤ) - 1) = -μ(2 * p)
```

(For Φ_{10}: degree 4, coeff at 3 is `-1 = -μ(10)`. ✓)

So a cleaner cyclotomic bridge is via the **negation** of the
sub-leading coefficient of `Φ_{2 p}`:

```
r_subLeadingCoeff_eq_via_cyclotomic_subLeading :
    ∀ p ∈ ({5, 7, 11, 13} : Finset ℕ),
      (r p).coeff ((p-1)/2 - 1)
        = -((p : ℤ) - 1) + (cyclotomic (2 * p) ℤ).coeff ((p : ℕ) - 1 - 1)
```

i.e. **subtract** the sub-leading coefficient of `Φ_{2 p}` (which is
`-μ(2 p) = -1`) from `-(p - 1)`. For `p = 5`:
`-(5 - 1) + (-1) = -4 - 1 = -5 ✓`.

For `p = 7`: `Φ_{14}` has degree 6, sub-leading coefficient is `-1`
(by `Φ_{14}(X) = Φ_7(-X) = X^6 - X^5 + X^4 - X^3 + X^2 - X + 1`).
`-(7 - 1) + (-1) = -6 - 1 = -7 ✓`.

Pattern holds for `p = 11, 13` by the same expansion (verified
implicitly through the S9 anchor's geometric-series form
`Φ_{2 p} = Σ_i (-X)^i`).

## 2. Two proposed uniform theorems for S11 ACT

### Stage 1 — Möbius-value identity (purely cyclotomic)

```lean
/-- For `p` odd prime, the sub-leading coefficient of `Φ_{2p}` is `-1`,
    equivalently `-μ(2p)`. -/
theorem cyclotomic_two_mul_prime_subLeadingCoeff_uniform
    {p : ℕ} (hp : Nat.Prime p) (hp_odd : Odd p) :
    (cyclotomic (2 * p) ℤ).coeff ((p : ℕ) - 1 - 1) = -1 := by
  -- Use S9's geometric-series form:
  --   cyclotomic (2 * p) ℤ = ∑ i ∈ Finset.range p, (-X) ^ i.
  -- The coefficient of `X^(p-2)` in this sum is the i = p - 2 term:
  --   (-X)^(p - 2) = (-1)^(p - 2) · X^(p - 2).
  -- For p odd, p - 2 is odd, hence (-1)^(p - 2) = -1.
  rw [cyclotomic_two_mul_prime_eq_geom_neg_series hp hp_odd]
  -- coeff via Finset.sum_coeff_eq + (-X)^k.coeff k = (-1)^k
  sorry  -- ~10 LOC; uses Finset.sum_coeff + coeff_neg + coeff_X_pow + Odd.neg_one_pow
```

### Stage 2 — Trace bridge for `r p` (the S11 deliverable)

```lean
/-- For `p` in the verified prime set `{5, 7, 11, 13}`, the
    sub-leading coefficient of `r p` matches the Möbius-driven
    Vieta-trace expression. -/
theorem r_subLeadingCoeff_via_moebius_uniform :
    ∀ p ∈ ({5, 7, 11, 13} : Finset ℕ),
      (r p).coeff ((p - 1) / 2 - 1)
        = -((p : ℤ) - 1) + (cyclotomic (2 * p) ℤ).coeff ((p : ℕ) - 1 - 1) := by
  intro p hp
  rcases Finset.mem_insert.mp hp with rfl | hp
  · -- p = 5: coeff at 1 of r 5 = X^2 - 5X + 5 is -5;
    --        coeff at 3 of Φ_10 is -1;
    --        RHS = -4 + (-1) = -5 ✓
    decide  -- if `decide` works on cyclotomic coeffs (likely yes via reflection)
  rcases Finset.mem_insert.mp hp with rfl | hp
  · -- p = 7: coeff at 2 of r 7 is -7;
    --        coeff at 5 of Φ_14 is -1;
    --        RHS = -6 + (-1) = -7 ✓
    decide
  rcases Finset.mem_insert.mp hp with rfl | hp
  · -- p = 11: -(10) + (-1) = -11 ✓
    decide
  · -- p = 13: -(12) + (-1) = -13 ✓
    rcases Finset.mem_singleton.mp hp with rfl
    decide

/-- The S11 uniform corollary: combine the trace bridge with the
    Möbius-value Stage 1 lemma to recover `-p`. -/
theorem r_subLeadingCoeff_eq_neg_p_uniform :
    ∀ p ∈ ({5, 7, 11, 13} : Finset ℕ),
      (r p).coeff ((p - 1) / 2 - 1) = -(p : ℤ) := by
  intro p hp
  have h_bridge := r_subLeadingCoeff_via_moebius_uniform p hp
  have h_cyclo : (cyclotomic (2 * p) ℤ).coeff ((p : ℕ) - 1 - 1) = -1 := by
    -- Apply Stage 1 lemma; each of p ∈ {5, 7, 11, 13} is prime odd.
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact cyclotomic_two_mul_prime_subLeadingCoeff_uniform
        (by decide) (by decide)
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact cyclotomic_two_mul_prime_subLeadingCoeff_uniform
        (by decide) (by decide)
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact cyclotomic_two_mul_prime_subLeadingCoeff_uniform
        (by decide) (by decide)
    · rcases Finset.mem_singleton.mp hp with rfl
      exact cyclotomic_two_mul_prime_subLeadingCoeff_uniform
        (by decide) (by decide)
  rw [h_bridge, h_cyclo]
  -- RHS becomes -((p : ℤ) - 1) + (-1) = -(p : ℤ); discharge by `ring` after
  -- per-prime decidable arithmetic.
  ring
```

**Estimated LOC**: ~85 (Stage 1 ~25, Stage 2 trace bridge ~35,
Stage 2 main corollary ~25). 1 transient `sorry` in Stage 1 (the
`(-X)^(p-2)` coefficient extraction), 0 sorries at S11 close.

## 3. Mathlib API audit

| Decl | Module | Status v4.26.0 | Use site |
|------|--------|----------------|----------|
| `Polynomial.cyclotomic` | `Mathlib.RingTheory.Polynomial.Cyclotomic.Basic` | present | Stage 1 |
| `Polynomial.cyclotomic_prime` | same | present | sanity (Φ_p form) |
| `Polynomial.coeff_sum` / `Finset.sum_coeff` | `Mathlib.Data.Polynomial.Coeff` | present | Stage 1 |
| `Polynomial.coeff_neg_X_pow` (or `coeff_neg + coeff_X_pow`) | `Mathlib.Data.Polynomial.Basic` | present | Stage 1 |
| `Odd.neg_one_pow` | `Mathlib.Algebra.GroupPower.Basic` | present | Stage 1 |
| `Nat.ArithmeticFunction.moebius` | `Mathlib.NumberTheory.ArithmeticFunction` | present | conceptual (not strictly needed in Lean) |
| `Nat.ArithmeticFunction.moebius_apply_prime` | same | present | conceptual |
| `Finset.mem_insert`, `Finset.mem_singleton`, `rcases` | core | present | Stage 2 |
| `cyclotomic_two_mul_prime_eq_geom_neg_series` | this file (S9) | merged (#18103) | Stage 1 |

**No upstream API drift anticipated.** The S9 anchor
`cyclotomic_two_mul_prime_eq_geom_neg_series` is the single
load-bearing predecessor for Stage 1.

## 4. Why not go through `subLeadingCoeff` directly?

The natural Mathlib decl is
`Polynomial.subLeadingCoeff : R[X] → R` defined as
`P.coeff (P.natDegree - 1)`. For `Φ_{2 p}` with `p` odd prime,
`natDegree = (p : ℕ) - 1` (= `φ(2 p)`), so
`Φ_{2 p}.subLeadingCoeff = Φ_{2 p}.coeff ((p : ℕ) - 2)`. This **does**
equal `-1` for the four verified primes by the geometric-series form.

The reason to prefer **explicit `coeff` arithmetic** over
`subLeadingCoeff` in S11:

1. `natDegree` calculation introduces a coercion subtraction
   `(p : ℕ) - 1 - 1`. Using `coeff` directly with the explicit index
   `((p : ℕ) - 2)` avoids the natural-number subtraction trap.
2. The Stage 1 lemma's proof routes through `Finset.sum_coeff`,
   which natively indexes by `i : ℕ`. Switching to
   `subLeadingCoeff` adds a `congr` step.
3. `r p`'s sub-leading coefficient is indexed at `(p - 1)/2 - 1`,
   not at `natDegree r p - 1` directly. The two are equal *modulo*
   `r_p_natDegree`, but the index form is the one the S4 ACT
   theorem statement actually uses.

Recommendation: **Use `coeff ((p : ℕ) - 2)` for `Φ_{2 p}` and
`coeff ((p - 1) / 2 - 1)` for `r p`**, matching the existing S4 ACT
style. Add a *separate* `subLeadingCoeff` adapter only if the
gallery enrichment phase requests it.

## 5. Per-prime sanity check

| `p` | `(p - 1) / 2 - 1` | `(r p).coeff (idx)` | `(p : ℕ) - 2` | `Φ_{2 p}.coeff (idx)` | RHS `-(p - 1) + Φ.coeff` |
|----:|------------------:|--------------------:|--------------:|----------------------:|--------------------------:|
| 5 | 1 | -5 | 3 | -1 | -4 + -1 = -5 ✓ |
| 7 | 2 | -7 | 5 | -1 | -6 + -1 = -7 ✓ |
| 11 | 4 | -11 | 9 | -1 | -10 + -1 = -11 ✓ |
| 13 | 5 | -13 | 11 | -1 | -12 + -1 = -13 ✓ |

All four match. Stage 2 trace bridge is correct as stated.

## 6. Boundary case `p = 3` — confirmed excluded

For `p = 3`: `(p - 1)/2 - 1 = 1 - 1 = 0`, which **coincides** with the
constant-coefficient index. The S4 ACT theorem `r_3_traceCoeff`
explicitly handles this collision by stating
`(r 3).coeff 0 = -3` separately. State.md (line 258–260) flags this
exclusion explicitly. The S11 PREP retains the `{5, 7, 11, 13}`
Finset, leaving `p = 3` to the `r_constantCoeff_eq_signed_uniform`
S10 theorem.

## 7. Anti-targets

The following are **out of scope** for S11 ACT and should be
addressed separately:

1. **Lifting Stage 1 to *every* odd prime.** Possible via the S9
   uniform anchor — the proof routes through the same
   `cyclotomic_two_mul_prime_eq_geom_neg_series`. But S11 should
   ship the **{5, 7, 11, 13} Finset form first** to match the S4 ACT
   style. The "every odd prime" form is a candidate for an S11b
   follow-up.
2. **Sub-leading divisibility for indices `0 < k < (p - 1)/2`.** The
   "HARD half" of state.md §312–316 — ramification calculation or
   local-field uniformizer. **Not** an S11 target; this is a
   research-level effort (~200–400 LOC).
3. **Möbius value in Lean directly.** Using
   `Nat.ArithmeticFunction.moebius_apply_prime` adds an additional
   layer of unfolding (`isCoprime` checks for `μ(2 * p)`); since the
   Stage 1 lemma proves the cyclotomic-coefficient form *directly*
   via the geometric series, the Möbius framing remains a
   *mathematical* commentary in the file's module docstring rather
   than a Lean dependency.
4. **`subLeadingCoeff` adapter.** Deferred to S12+ gallery
   enrichment.

## 8. Honesty about the state.md sketch

State.md line 251 reads

> `(r p).coeff ((p-1)/2 - 1) = -(cyclotomic (2*p) ℤ).subLeadingCoeff`

This statement is **arithmetically wrong** as a literal equality
(see §1 verification: for `p = 5`, LHS = -5, RHS = +1). It is best
interpreted as a *gestural* outline — "the cyclotomic structure
controls the trace" — rather than a target theorem. The correct
form is §2's **two-stage bridge**:

```
(r p).coeff ((p-1)/2 - 1) = -((p : ℤ) - 1) + (cyclotomic (2 * p) ℤ).coeff ((p : ℕ) - 2)
```

i.e. the cyclotomic correction is **added** (not negated) to a
Vieta-trace offset of `-(p - 1)`.

This S11 PREP records the corrected statement so the future S11
ACT iteration does not waste cycles chasing the literal sketch.

## 9. No-edit guarantee

This PREP **does not** touch:

- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` (verified, 1166 lines after S10)
- `proofs/Proofs.lean` (manifest)
- `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/{problem, knowledge, state}.md`
- `src/data/research/problems/angle-trisection-cos-20-gal-oq-01-oq-03.json`
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/` (gallery)
- Any other research-slug files

Only the new `sessions/2026-05-12-s11-prep-trace-moebius-bridge.md`
file is added.

## 10. Race awareness

At PREP-push time (2026-05-12, late evening UTC):

- `gh pr list --search angle-trisection-cos-20-gal-oq-01-oq-03 --state open`
  shows only #17906 (S4, build-pending from ~17h prior). The S4
  PR adds 200 lines to `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean`
  + 34 deletions; **no edit to `sessions/`**.
- The slug directory `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/`
  has **no prior `sessions/` subdirectory** — this PR creates it.
- `git branch -r | grep angle-trisection-cos-20-gal-oq-01-oq-03`
  shows the S(N) ACT branches; none are S11 PREP.

**Conflict surface**: zero. Strictly additive single-file PR
creating a fresh subdirectory.

## 11. Hand-off checklist for S11 ACT (next researcher)

1. ☐ Verify S10 ACT (#18103 era) has fully landed; the proof of
   Stage 2 depends on the S9 anchor
   `cyclotomic_two_mul_prime_eq_geom_neg_series` already being in
   `main`.
2. ☐ Append the §2 Stage 1 + Stage 2 lemmas to
   `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` (after the
   S10 block).
3. ☐ Discharge the Stage 1 `sorry` via `Finset.sum_coeff`,
   `coeff_neg`, `coeff_X_pow`, `Odd.neg_one_pow`. Estimated ~15
   minutes once the lemma names are looked up.
4. ☐ Verify Stage 2's per-prime `decide` calls work; if `decide`
   times out on `(cyclotomic 22 ℤ).coeff 9 = -1`, expand explicitly
   via `cyclotomic_22_eq` (S6 lemma).
5. ☐ `./proofs/scripts/docker-build.sh
   Proofs.AngleTrisectionCos20GalOQ01OQ03` — expect <2 min on warm
   `.lake`; ~30–45 min on broken-symlink fresh clone.
6. ☐ Update `state.md` phase → S11 ACT complete; correct the
   §"S11 next action" sketch to match the §1 derivation.
7. ☐ Branch:
   `research/angle-trisection-cos-20-gal-oq-01-oq-03-s11-act-trace-moebius-<unix-ts>`.

## 12. References

- Apostol, T. M. (1976). *Introduction to Analytic Number Theory.*
  Springer. §2.18 (Möbius function values), §3.4 (cyclotomic
  polynomial evaluation).
- Lang, S. (2002). *Algebra*, 3rd edn. Springer. §VI.3
  (cyclotomic polynomials and Galois group).
- Niven, Zuckerman, Montgomery (1991). *An Introduction to the
  Theory of Numbers*, 5th edn. Wiley. §2.4 (sums of roots of unity).
- Marcus, D. A. (1977). *Number Fields.* Springer. §2 Ex. 8
  (the trace of `2 + 2 cos(π / p)` and its Möbius interpretation).
- This repo:
  - `Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` (S10 state).
  - `cyclotomic_two_mul_prime_eq_geom_neg_series` (S9 anchor, line
    location to be confirmed by the S11 ACT researcher).
  - `r_subLeadingCoeff_eq_neg_p` (S4 ACT 4-clause conjunction, line
    365).

## 13. Honesty

This document is **doc-only PREP**. It produces:
- 0 new Lean theorems shipped
- 0 sorry deltas in `Proofs/AngleTrisectionCos20GalOQ01OQ03.lean`
- 0 axiom changes
- 1 new design document (this file) + 1 new `sessions/` subdir

The value is **two-fold**:
1. Correct the arithmetically-wrong state.md S11 sketch so the
   future S11 ACT does not waste cycles.
2. Provide the two-stage proof skeleton (Stage 1 cyclotomic Möbius
   value, Stage 2 trace bridge) ready for ~85-LOC implementation in
   the next ACT session.

Status remains `in-progress` for the slug; S11 ACT is the next
expected delivery.

---

**End of S11 PREP — no Lean changes, no gallery changes, no axiom
changes. The session-doc subdirectory is created fresh; this is the
first entry.**
