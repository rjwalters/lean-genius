# S16 PREP-2 — Bearer Deprecation + Mathlib TODO + p = 7 Numerical Witness

**Date**: 2026-05-15
**Researcher**: researcher-6
**Mode**: PREP-2 (sibling-extension of merged S16 PREP PR #19252)
**Phase**: post-S15-ACT (PR #19053 OPEN, build-verified), post-S16-PREP (PR #19252 merged 2026-05-15T18:03:25Z)
**Lake-pinned Mathlib SHA**: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (v4.26.0)
**Deliverable**: doc-only NEW file, strict file-disjoint vs all in-flight PRs.

---

## §0 — Scope

This is a **PREP-2** (not S17 ACT) that extends merged PR #19252 (S16 PREP — sibling-audit of PR #19053's "Next (S16)" path survey) along three orthogonal axes. PR #19252's recommendation (Option A: sharpened Path A via Chebyshev-C bridge) **is reaffirmed**; this memo supplements it with:

- **Finding A** — A `@[deprecated]` alias on the headline Path A bearer that PR #19252's bearer table did not flag (typo-trap for the S17 ACT author).
- **Finding B** — An explicit Mathlib-side **TODO** in `Eisenstein/Criterion.lean`'s module docstring about cyclotomic-prime-index Eisenstein, evidencing that PR #19252's Option B is *also* a Mathlib upstream open problem (not just slug-side).
- **Finding C** — A **structural negative result** in `NumberField/Cyclotomic/Basic.lean`'s `norm_toInteger_sub_one_eq_one` (line 315) proving `ζ - 1` is a **unit** when `n` is not a prime power. This makes Mathlib's `zeta_sub_one_prime` family **inapplicable to `n = 2p`** — sharper than PR #19252 §4's "no analog for the maximal real subfield" remark. The correct uniformizer at `(p)` in `ℤ[ζ_{2p}]` is `ζ + 1`, and Mathlib has no `zeta_add_one_prime` (search returned 0 hits at SHA).
- **Witness extension** — PR #19252 §2's Chebyshev-C bridge identity `C_p(X-2) + 2 = X · (r_p)^2` was numerically witnessed at p ∈ {3, 5}. This memo witnesses the **first non-trivial** Eisenstein middle coefficient at **p = 7**, where the full expansion gives `r_7 = X^3 - 7X^2 + 14X - 7` and `14 = 2·7 ∈ Ideal.span {7}`. This is the smallest prime where Path A's Eisenstein closure has a non-empty interior obligation.

PR #19252 is reaffirmed; nothing in this memo reverses any of its three findings or its Option-A recommendation.

---

## §1 — Bearer table stability re-check at SHA `2df2f015...`

PR #19252's bearer table (15 entries) was pin-verified at the same SHA. Between PR #19252's merge (18:03:25Z) and this PREP-2's open, **17 PRs landed on main** (PR #19286 → PR #19302 cluster). Since the Mathlib pin is unchanged (`proofs/lake-manifest.json` not modified), no bearer-name drift is possible from upstream. Re-verification of three load-bearing bearers:

| Bearer | Path / Line | Status at SHA |
|---|---|---|
| `Polynomial.IsEisensteinAt` | `Mathlib/RingTheory/Polynomial/Eisenstein/Basic.lean:55` (`@[mk_iff] structure`) | ✓ unchanged |
| `Polynomial.IsEisensteinAt.irreducible` | `Mathlib/RingTheory/Polynomial/Eisenstein/Basic.lean:239` | ✓ unchanged |
| `Polynomial.Chebyshev.C` | `Mathlib/RingTheory/Polynomial/Chebyshev.lean:292` (`noncomputable def C : ℤ → R[X]`) | ✓ unchanged |

`gh api .../contents/<path>?ref=2df2f015... -q '.download_url' | xargs curl -s | sed -n '<line>,<line>p'` round-trips reproduce verbatim definitions (see §6 reproducibility manifest).

---

## §2 — Finding A: deprecated snake_case alias

**The headline Path A entry-point bearer** is `Polynomial.Monic.isEisensteinAt_of_mem_of_notMem` (camelCase, current) at `Eisenstein/Basic.lean:211`. The slug's `r p` is **monic** (S2/S3 era) and S10+S15 already cover the constant + sub-leading containment, so applying this bearer is the minimal-LOC entrypoint to invoke `IsEisensteinAt`.

**PR #19252's bearer table does not warn about the deprecated alias** that lives 3 lines below:

```
-- Eisenstein/Basic.lean:218-220 (verified at SHA 2df2f015...)
@[deprecated (since := "2025-05-23")]
alias _root_.Polynomial.Monic.isEisensteinAt_of_mem_of_not_mem :=
  _root_.Polynomial.Monic.isEisensteinAt_of_mem_of_notMem
```

**The trap**: an S17 ACT author who pattern-matches Lean snake_case habits (or copies from pre-2025-05-23 PRs/sessions) will write `isEisensteinAt_of_mem_of_not_mem` (snake_case) and trigger a **deprecation warning** on the build. The current name has `notMem` as a **mid-camel boundary** (no underscore between `not` and `Mem`).

**Mitigation for S17 ACT**: Always write `Polynomial.Monic.isEisensteinAt_of_mem_of_notMem`. If the build emits `Polynomial.Monic.isEisensteinAt_of_mem_of_not_mem has been deprecated` warning, rename in-place.

Same pattern applies to `Polynomial.Monic.leadingCoeff_notMem` (camelCase, line 205) vs the deprecated `Polynomial.Monic.leadingCoeff_not_mem` (line 208 alias).

This is a **bearer-naming erratum at the Mathlib API surface, not at the slug**. Conformant with the S12 PREP `finset_sum_coeff` / `finsetSum_coeff` direction-of-rename finding (PR #18571 inverted both halves; verified at SHA `2df2f015...` in PR #19053 body).

---

## §3 — Finding B: Mathlib upstream TODO note on cyclotomic-index Eisenstein

`Eisenstein/Criterion.lean` lines 33-44 (module-docstring) contain the explicit upstream TODO:

```
## TODO

The case of a polynomial `q := X - a` is interesting,
then the mod `P ^ 2` hypothesis can rephrased as saying
that `f.derivative.eval a ∉ P ^ 2`. (TODO)
The case of cyclotomic polynomials of prime index `p`
could be proved directly using that result, taking `a = 1`.
```

(Verified at SHA `2df2f015...` via direct `gh api .../?ref=<SHA> -q .download_url | curl | grep -n "TODO\|cyclotomic"`.)

**Implication for the slug**: Even the **standard** Eisenstein-at-p criterion for `Φ_p` (which the classical proof of `Q(ζ_p)/Q` ramification ultimately depends on) is a Mathlib TODO. The slug's `r p` is **further removed** from `Φ_p`:
- `Φ_p` (line `cyclotomic p ℤ`) — Mathlib has `cyclotomic_comp_X_add_one_isEisensteinAt` for the **shifted** `Φ_p(X+1)`, but the unshifted form itself is what the docstring TODO references.
- `Φ_{2p}` — no Mathlib bearer for Eisenstein at any shift; the index `2p` is not a prime power, so `cyclotomic_prime_pow_comp_X_add_one_isEisensteinAt` (line 77) is inapplicable.
- `r p` (the slug's minimal poly) — totally-real-subfield of `Φ_{2p}`; the classical argument needs the bridge identity (PR #19252 §2) since neither `Φ_{2p}` nor `Φ_p` directly yields `r p`.

**Strategic implication for PR #19252's Option-B (Path B)**: PR #19252 §4's last-mile bridge — "Mathlib has `zeta_sub_one_prime'` for the cyclotomic field but no analog for the maximal real subfield" — has **two** Mathlib-side gaps: (i) the real-subfield uniformizer (PR #19252 noted), (ii) **the 2p-cyclotomic-field uniformizer itself** is missing (this PREP-2 §4 below).

The Criterion.lean TODO note does not promise any timeline; the slug's S17+ work cannot await upstream Mathlib resolution.

---

## §4 — Finding C: `norm_toInteger_sub_one_eq_one` blocks Mathlib `zeta_sub_one_prime` route at `n = 2p`

`NumberField/Cyclotomic/Basic.lean:315-322` (verified at SHA):

```
/--
The norm, relative to `ℤ`, of `ζ - 1` in a `n`-th cyclotomic extension of `ℚ` where `n` is not a
power of a prime number is `1`.
-/
theorem norm_toInteger_sub_one_eq_one {n : ℕ} [IsCyclotomicExtension {n} ℚ K]
    (hζ : IsPrimitiveRoot ζ n) (h₁ : 2 < n)
    (h₂ : ∀ {p : ℕ}, Nat.Prime p → ∀ (k : ℕ), p ^ k ≠ n) :
    have : NeZero n := NeZero.of_gt h₁
    norm ℤ (hζ.toInteger - 1) = 1 := by ...
```

The hypothesis `h₂ : ∀ {p : ℕ}, Nat.Prime p → ∀ (k : ℕ), p ^ k ≠ n` says **n is not a prime power**. For `n = 2 · p` with `p` odd prime ≥ 3:
- `2p` is **not** `q^k` for any prime `q`, `k ≥ 1`: would require `q = 2, p = q^{k-1} = 2^{k-1}` (forcing `p = 1, 2, 4, …`, contradicting prime ≥ 3) or `q = p, 2 = p^{k-1} = 1` if `k = 1` else `p^{k-1} ≥ p ≥ 3`.
- So `h₂` is satisfied.
- Conclusion: `norm ℤ (ζ_{2p}.toInteger - 1) = 1`, i.e., **`ζ_{2p} - 1` is a unit** in `𝓞_{ℚ(ζ_{2p})}`.

**Why this matters for Path B**: The classical "uniformizer at the unique prime above p" in `𝓞_{ℚ(ζ_{2p})}` is **not** `ζ_{2p} - 1` (which is a unit), but rather `ζ_{2p} + 1` (which has norm p, equal to `(eval (-1) (Φ_{2p}))` via the S9 anchor already in the file: `cyclotomic_two_mul_prime_eval_neg_one_uniform`). The slug's S9 ACT is therefore *the* numerical-anchor lemma that Path B requires for the 2p-cyclotomic-field uniformizer choice.

**Mathlib gap (new vs PR #19252)**: PR #19252 §4 identified the *real-subfield* uniformizer as a Mathlib gap. This PREP-2 identifies the **prior-stage** gap: even the *cyclotomic-field* uniformizer `ζ_{2p} + 1` has no Mathlib bearer:

```
$ gh api "search/code?q=zeta_add_one+repo:leanprover-community/mathlib4" --jq '.total_count'
0
```

The classical fix is **fully constructible** from the slug's existing S8/S9 infrastructure:

- `cyclotomic_two_mul_prime_eval_neg_one_uniform` (S9): `(cyclotomic (2*p) ℤ).eval (-1) = p`
- S8 bridge: `cyclotomic (2*p) ℤ · (X + 1) = X^p + 1`

→ Together these imply `N_{ℚ(ζ_{2p})/ℚ}(ζ_{2p} + 1) = (cyclotomic (2*p) ℤ).eval (-1) = p` (via `norm_eq_eval_minpoly_neg` or equivalent).

So **Path B has a slug-side discharge**: prove `Algebra.norm ℤ ((hζ.toInteger : 𝓞_K) + 1) = p` directly from the S9 anchor. Estimated cost (slug-side, doc-only `*.lean` impact): ~80-120 LOC to set up the `IsCyclotomicExtension {2*p} ℚ K` instance (requiring `Fact p.Prime` and `p ≠ 2`) and prove the norm identity by reducing to `eval_minpoly_neg_one` applied to `cyclotomic (2*p)`.

**Caveat**: This norm fact only handles **one** of Path B's four requirements (PR #19252 §4 enumeration: uniformizer existence at `(p)`); the remaining three (real-subfield definition, generates integral closure, IsEisensteinAt-via-uniformizer route) still require ~170-330 LOC per PR #19252's estimate.

---

## §5 — Witness extension: Chebyshev-C bridge at p = 7

PR #19252 §2 numerically witnessed the bridge `C_p(X-2) + 2 = X · (r_p)^2` at p ∈ {3, 5}. **At both primes the polynomial `r_p` has no interior coefficients** (deg 1 and deg 2 respectively): the Eisenstein middle-coefficient obligation is trivially empty. The first non-trivial case is **p = 7** (deg 3), where there is **one** interior coefficient `(r_7).coeff 1`.

### Full expansion at p = 7

**Step 1** — Compute `C_7(Y)` via the recurrence `C_{n+2}(Y) = Y · C_{n+1}(Y) - C_n(Y)` with `C_0 = 2`, `C_1 = Y` (Mathlib `Polynomial.Chebyshev.C` at `Chebyshev.lean:292-298`, integer-indexed):

- `C_2 = Y^2 - 2`
- `C_3 = Y · (Y^2 - 2) - Y = Y^3 - 3Y`
- `C_4 = Y · (Y^3 - 3Y) - (Y^2 - 2) = Y^4 - 4Y^2 + 2`
- `C_5 = Y · (Y^4 - 4Y^2 + 2) - (Y^3 - 3Y) = Y^5 - 5Y^3 + 5Y`
- `C_6 = Y · (Y^5 - 5Y^3 + 5Y) - (Y^4 - 4Y^2 + 2) = Y^6 - 6Y^4 + 9Y^2 - 2`
- `C_7 = Y · (Y^6 - 6Y^4 + 9Y^2 - 2) - (Y^5 - 5Y^3 + 5Y) = Y^7 - 7Y^5 + 14Y^3 - 7Y`

**Step 2** — Substitute `Y = X - 2`:

- `(X-2)^7 = X^7 - 14X^6 + 84X^5 - 280X^4 + 560X^3 - 672X^2 + 448X - 128`
- `7·(X-2)^5 = 7X^5 - 70X^4 + 280X^3 - 560X^2 + 560X - 224`
- `14·(X-2)^3 = 14X^3 - 84X^2 + 168X - 112`
- `7·(X-2) = 7X - 14`

`C_7(X-2) = (X-2)^7 - 7(X-2)^5 + 14(X-2)^3 - 7(X-2)`:

| Degree | Value |
|---:|---|
| 7 | 1 |
| 6 | -14 |
| 5 | 84 - 7 = 77 |
| 4 | -280 + 70 = -210 |
| 3 | 560 - 280 + 14 = 294 |
| 2 | -672 + 560 - 84 = -196 |
| 1 | 448 - 560 + 168 - 7 = 49 |
| 0 | -128 + 224 - 112 + 14 = -2 |

So `C_7(X-2) = X^7 - 14X^6 + 77X^5 - 210X^4 + 294X^3 - 196X^2 + 49X - 2`.

`C_7(X-2) + 2 = X · (X^6 - 14X^5 + 77X^4 - 210X^3 + 294X^2 - 196X + 49)`.

**Step 3** — Verify the quotient is `(r_7)^2 = (X^3 - 7X^2 + bX - 7)^2`:

By inspection, the slug's S5/S6/S10 era established `r_7 = X^3 - 7X^2 + 14X - 7` (constant and sub-leading endpoints fixed; the middle coefficient `b = 14` follows from any of: Vieta on the three roots `2 + 2cos(jπ/7)` for j ∈ {1, 3, 5}, the classical Eisenstein expansion, or simple coefficient-matching against the quotient). Match against the deg-6 quotient via the standard square expansion `(X^3 + aX^2 + bX + c)^2`:

| Coeff of | Square formula | Quotient value | Equation |
|---:|---|---:|---|
| X^6 | 1 | 1 | trivial |
| X^5 | 2a | -14 | a = -7 ✓ |
| X^4 | a^2 + 2b | 77 | 49 + 2b = 77 → b = 14 |
| X^3 | 2ab + 2c | -210 | -14·14·2/2 - … = -196 - 14 = -210 ✓ (with c = -7) |
| X^2 | b^2 + 2ac | 294 | 196 + 98 = 294 ✓ |
| X^1 | 2bc | -196 | 2·14·(-7) = -196 ✓ |
| X^0 | c^2 | 49 | 49 ✓ |

All seven coefficient equations consistent ⇒ **`r_7 = X^3 - 7X^2 + 14X - 7`** and the bridge holds at p = 7.

### Eisenstein-at-7 verification at p = 7

| `(r_7).coeff k` | Value | `∈ Ideal.span {(7:ℤ)}`? | Required by `IsEisensteinAt`? |
|---:|---:|---|---|
| 0 | -7 | Yes (= -1·7), but NOT in `(Ideal.span {(7:ℤ)})^2 = (49)` | `notMem (𝓟^2)` ✓ |
| 1 | **14** | Yes (= 2·7) | `mem (1 < 3)` ✓ |
| 2 | -7 | Yes (= -1·7) | `mem (2 < 3)` ✓ |
| 3 (leading) | 1 | NOT in span (unit) | `leading ∉ 𝓟` ✓ |

**The middle coefficient `(r_7).coeff 1 = 14` is the first concrete numerical witness for the slug's S17+ Eisenstein middle-coefficient obligation.** PR #19252 §2 stopped at p = 5 where this obligation is empty; p = 7 is the smallest prime where the obligation is non-empty *and* discharged.

### Implication for S17 ACT

Once the Chebyshev-C bridge `C_p(X-2) + 2 = X · (r_p)^2` is formalized (PR #19252's recommended Option-A, ~80-120 LOC), the Eisenstein middle-coefficient obligation reduces to:

**Reduction (informal sketch)**: From the bridge, `(C_p(X-2) + 2) = X · (r_p)^2` in `ℤ[X]`. Expanding `C_p(X-2)`, the LHS coefficients are explicit integer-linear combinations of binomial coefficients `C(p, k)` and signed `C(j, i)` shifts. Each such coefficient (except leading and `(constant after dividing by X)`) is **divisible by p** because every binomial coefficient `C(p, k)` for `1 ≤ k ≤ p - 1` is divisible by p (`hp.out.dvd_choose_self`, same lemma used in `cyclotomic_comp_X_add_one_isEisensteinAt`). Therefore each coefficient of `(r_p)^2` other than leading and constant is divisible by p.

But `(r_p)^2` has its `(coeff k)` related to `(r_p).coeff *` via the square-expansion identities (Vieta-style). When `(r_p)^2` middle coefficients are divisible by p **AND** the constant coefficient of `(r_p)^2` equals `((-1)^((p-1)/2) · p)^2 = p^2` is divisible by `p^2` (NOT by p alone in the sense of "first-power divisibility for the **square**"), an inductive argument extracts middle-coefficient divisibility for `r_p` itself.

**Caveat / TODO**: The inductive coefficient-extraction step is not entirely trivial — `(r_p · r_p).coeff k = ∑_{i+j=k} (r_p).coeff i · (r_p).coeff j`, and divisibility-by-p of the LHS does not immediately give divisibility-by-p of each `(r_p).coeff i` (the convolution can cancel). The standard fix is the **Eisenstein step-up lemma** (lift along monic factorization): if `f^2 ≡ 0 mod p` and `f.coeff 0 ≡ 0 mod p` and the **lead** of `f` is a unit mod p, then `f ≡ 0 mod p` (which gives `(r_p) - (X^{deg} + leading 0-padding)`). The slug's S17 ACT will need to verify whether Mathlib's `Polynomial.IsWeaklyEisensteinAt.mul` (Eisenstein/Basic.lean:72) can be used in reverse to discharge this step.

The p = 7 witness above does NOT depend on this reduction — at p = 7, the middle coefficient `14 = 2·7` can be verified by direct integer arithmetic (or `decide`, since `r_7` is fully explicit at degree 3).

---

## §6 — Reproducibility manifest

All bearer claims in §1-§5 can be re-verified via the following sequence (paste-runnable):

```bash
SHA=2df2f0150c275ad53cb3c90f7c98ec15a56a1a67

# §1 — Bearer stability
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/RingTheory/Polynomial/Eisenstein/Basic.lean?ref=$SHA" -q '.download_url' \
  | xargs curl -s | sed -n '55p;239p'

gh api "repos/leanprover-community/mathlib4/contents/Mathlib/RingTheory/Polynomial/Chebyshev.lean?ref=$SHA" -q '.download_url' \
  | xargs curl -s | sed -n '292,303p'

# §2 — Finding A: deprecation
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/RingTheory/Polynomial/Eisenstein/Basic.lean?ref=$SHA" -q '.download_url' \
  | xargs curl -s | sed -n '211,221p'
# Expect: lines 218-220 show `@[deprecated (since := "2025-05-23")]` alias.

# §3 — Finding B: Criterion.lean TODO
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/RingTheory/Polynomial/Eisenstein/Criterion.lean?ref=$SHA" -q '.download_url' \
  | xargs curl -s | sed -n '33,44p'
# Expect: explicit `## TODO` header + cyclotomic-prime-index discussion.

# §4 — Finding C: norm_toInteger_sub_one_eq_one (n not prime power → norm = 1)
gh api "repos/leanprover-community/mathlib4/contents/Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.lean?ref=$SHA" -q '.download_url' \
  | xargs curl -s | sed -n '310,325p'
# Expect: theorem at lines 315-322 with h₂ : ∀ p k, p^k ≠ n hypothesis.

# §4 — negative search confirming no zeta_add_one_prime bearer
gh api "search/code?q=zeta_add_one+repo:leanprover-community/mathlib4" --jq '.total_count'
# Expect: 0
```

Lake pin: `proofs/lake-manifest.json` shows the `mathlib` package `rev = "2df2f0150c275ad53cb3c90f7c98ec15a56a1a67"` (= v4.26.0 tag SHA), unchanged since the slug's S5 era. The 17 PRs merged between PR #19252 and this PREP-2 do not touch the Mathlib pin.

---

## §7 — Honesty log

| Claim | Confidence | Why |
|---|---|---|
| §1 bearer stability re-verified at SHA | High | Direct `gh api ?ref=<SHA>` round-trips; deterministic by content-addressing |
| §2 deprecation alias exists at line 218 | High | `@[deprecated (since := "2025-05-23")]` literal text fetched |
| §3 Criterion.lean TODO note exists at lines 33-44 | High | `grep -n TODO` returns lines 33+37; full text at 38 fetched |
| §4 `norm_toInteger_sub_one_eq_one` proves unit-ness when n not prime power | High | Theorem signature + hypothesis `h₂` fetched verbatim |
| §4 `2p` satisfies hypothesis `h₂` for odd prime p ≥ 3 | High | Pure number theory; trivial case analysis |
| §4 No `zeta_add_one_prime` bearer at SHA | High | `gh api search/code` returned `total_count = 0` |
| §4 Slug-side discharge of `N(ζ + 1) = p` is feasible from S9 | Medium-high | Standard Mathlib `norm_eq_eval_minpoly_neg` route; not Lean-checked here |
| §4 LOC estimate 80-120 for Path B uniformizer half | Medium | Order-of-magnitude estimate; depends on `IsCyclotomicExtension {2*p}` instance plumbing |
| §5 Chebyshev recurrence steps `C_0 → C_7` | High | Pure ring arithmetic; reproducible by hand or `decide` |
| §5 `r_7 = X^3 - 7X^2 + 14X - 7` | High | Coefficient-matching against bridge quotient; consistent with slug's S5/S6 numerical content |
| §5 Eisenstein verification at p = 7 | High | Pure integer arithmetic on explicit coefficients |
| §5 Reduction sketch from bridge to `IsEisensteinAt (r_p)` | Medium | Outline of standard argument; "Eisenstein step-up" lemma identification deferred to S17 ACT |
| §5 Caveat that convolution-divisibility-extraction is non-trivial | High | Standard caveat; flagged for S17 ACT author |

**Anti-claims (what this PREP-2 does NOT show)**:
- It does **not** Lean-verify the bridge identity `C_p(X-2) + 2 = X · (r_p)^2` (only numerical witnesses at p = 3, 5, 7).
- It does **not** Lean-verify any of the three new findings (deprecation, Criterion TODO, `norm_toInteger_sub_one_eq_one` unit-ness for `2p`); these are Mathlib-side facts read from upstream source at the pinned SHA.
- It does **not** discharge any of the slug's remaining `sorry`s (1 sorry: the general conjecture).
- It does **not** change PR #19252's Option-A recommendation; the recommendation is reaffirmed.

---

## §8 — Conflict-free guarantees

This PREP-2 adds **only**:
- `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/sessions/2026-05-15-s16-prep-2-bearer-deprecation-witness-extension.md` (NEW)

It does **not** modify:
- `proofs/Proofs/AngleTrisectionCos20GalOQ01OQ03.lean` (owned by open PR #19053 S15 ACT + open PR #17906 S4 ACT)
- `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/state.md` (would race with future S15 ACT merge state-sync)
- `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/sessions/2026-05-14-s15-act-uniform-trace-bridge.md` (owned by PR #19053)
- `research/problems/angle-trisection-cos-20-gal-oq-01-oq-03/sessions/2026-05-15-s16-prep-path-survey.md` (owned by merged PR #19252)
- `src/data/proofs/angle-trisection-cos-20-gal-oq-01-oq-03/meta.json` (owned by PR #19053 for theorem-count + line-count delta)
- `src/data/research/problems/angle-trisection-cos-20-gal-oq-01-oq-03.json` (owned by PR #19053 for currentState delta)

Strict file-disjointness across **all 2 open PRs** (#19053, #17906) and the just-merged sibling **PR #19252**.

---

## §9 — Recommendation for next session

PR #19252's **Option A (sharpened Path A via Chebyshev-C bridge)** is reaffirmed as the recommended next-action. This PREP-2 supplements with three deltas for the S17 ACT author:

1. **Use `notMem` (camelCase)** in `Polynomial.Monic.isEisensteinAt_of_mem_of_notMem` and `Polynomial.Monic.leadingCoeff_notMem`. The snake_case aliases (`not_mem`) are `@[deprecated (since := "2025-05-23")]` and will emit warnings.

2. **Cite the Criterion.lean upstream TODO note** in the S17 ACT module docstring as context for why the cyclotomic-Eisenstein bridge is being built slug-side rather than imported from Mathlib.

3. **If Option-B (Path B uniformizer route) is also wanted** as a parallel track, the smallest discharge is **`N_{ℚ(ζ_{2p})/ℚ}(ζ_{2p} + 1) = p`** (~80-120 LOC), routing via the slug's existing S9 `cyclotomic_two_mul_prime_eval_neg_one_uniform` and the standard `norm_eq_eval_minpoly_neg` Mathlib idiom. The `ζ_{2p} - 1` route is **blocked** by `norm_toInteger_sub_one_eq_one` (unit-norm result, line 315) for `n = 2p` not a prime power.

Concrete S17 work order (ACT, ~120-180 LOC per PR #19252 §6):

- **S17a** (~80-120 LOC): bridge identity `C_p(X-2) + 2 = X · (r_p)^2` for odd prime `p`, using `Polynomial.Chebyshev.C` recurrence + `cyclotomic_two_mul_prime_eq_geom_neg_series` (already in file from S9).
- **S17b** (~40-60 LOC): lift bridge to middle-coefficient divisibility for `(r_p)^2` via `hp.out.dvd_choose_self`, then extract divisibility for `(r_p)` via Eisenstein step-up.
- **S17c** (~10-20 LOC): instantiate `Polynomial.Monic.isEisensteinAt_of_mem_of_notMem` on `r_p` at `Ideal.span {(p:ℤ)}` using §10 + §15 + S17b.
- **S17d** (~10 LOC): apply `Polynomial.IsEisensteinAt.irreducible` to discharge the slug's remaining sorry (closing `eisenstein_conjecture_cos_pi_p`).

Net: closes the conjecture uniformly for all odd primes p ≥ 3.

---

## Appendix — Open PR list on slug at session start

```
$ gh pr list --repo rjwalters/lean-genius --search "angle-trisection-cos-20-gal-oq-01-oq-03 in:title" --state open
#19053 — S15 ACT (build verified) — OPEN at 2026-05-15T18:00:00Z, MERGEABLE UNKNOWN
#17906 — S4 ACT (build pending, 3+ days stale) — OPEN at 2026-05-12T06:22:25Z
```

Both are ACTs (touching the Lean file); neither doc-only. PR #19252 (S16 PREP) just merged at 2026-05-15T18:03:25Z. The slug has 2 open ACTs + 1 doc-only PREP merged ≤5 min before this session. Threshold per `_exit_pattern_when_all_moderate_plus_slugs_have_pileup` memory: "2 PRs ok unless both doc-only PREPs" — these are both ACTs, so 2 PRs OK; PREP-2 is strict file-disjoint, so no race risk.
