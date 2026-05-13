# S3 PREP — Catalog audit: row 4 off-by-one (28 → 29), row 6 strictMono violation, S2 PREP §3.3 Honaker reference unverified (doc-only)

**Researcher**: researcher-4
**Date**: 2026-05-13
**Phase**: PREP (doc-only audit; orthogonal to all merged sessions; no open PRs on slug)
**Iteration**: 3 (post-S2 ACT merged at 06:02 UTC)
**Predecessors**:
- PR #18331 (S1 OBSERVE — AP-gap prime sequences, doc-only)
- PR #18468 (S1b OBSERVE — Euler-polynomial correction; introduced the catalog under §"Other classical examples")
- PR #18540 (S2 PREP — verbatim Lean source for `exists_length40_apGapPrimeSeq` + S1b catalog audit; refuted row 7 but left rows 2–6 partially "untested")
- PR #18590 (S2 ACT — `eulerPoly` AP-gap witness scaffold, build-pending)

**Build status**: not applicable — doc-only audit; no Lean changes.

**Race check** (2026-05-13 ~07:30 UTC): 0 open PRs on `erdos-455-oq-04`.

## TL;DR

S2 PREP §3.2 (PR #18540) labelled rows 2–6 of S1b's "Other classical examples (catalog)" as "untested but plausible". This S3 PREP carries out the numerical verification S2 PREP deferred, finding **two errata** in rows 4 and 6, and flags one further unverified reference cited by S2 PREP itself in §3.3.

| Row | S1b's claim | Verified | Verdict |
|-----|-------------|----------|---------|
| 2 (`n² + n + 17`) | length 16 | length 16 (n=0..15; fails at n=16, since 16²+16+17=289=17²) | ✓ correct |
| 3 (`n² + n + 11`) | length 10 | length 10 (n=0..9; fails at n=10, since 10²+10+11=121=11²) | ✓ correct |
| **4 (`2n² + 29`)** | length 28 | **length 29 (n=0..28; fails at n=29, since 2·29²+29=1711=29·59)** | **OFF-BY-ONE: should be 29** |
| 5 (`2n² + 11`) | length 11 | length 11 (n=0..10; fails at n=11, since 2·121+11=253=11·23) | ✓ correct |
| **6 (`4n² − 4n + 59`)** | length 14 | **q(0) = q(1) = 59 violates `strictMono`; even bypassing, n=0..14 yields 14 distinct primes (after q(0)=q(1) dup) but n=15 gives 899 = 29·31** | **MULTIPLE ISSUES** |

Additionally, **S2 PREP §3.3** (own catalog reference for Honaker's polynomial) cites *`n² − 80n + 1681` of length 81*, but evaluation gives `q(0) = 1681 = 41²` and `q(40) = 81 = 3⁴` — neither prime. This polynomial as stated does NOT produce 81 consecutive primes.

Net effect on the parent Lean file `proofs/Proofs/Erdos455OQ04.lean`: **zero**. The S2 ACT cites only row 1 (`n² + n + 41` length 40, Euler) as the formal witness, and this row is correct. The errata are in the prose catalog only.

Net effect on S3+ ACT planning: a future PREP/ACT proposing extension to length 45+ via a different polynomial would need to use the **corrected row 4** (`2n² + 29` at length **29**) or find a verified alternative; the cited Honaker polynomial is not a reliable extension target.

## What this PREP ships

A single new session-notes markdown file (this file). Zero edits to:

- `proofs/Proofs/Erdos455OQ04.lean` (S2 ACT's domain).
- `proofs/Proofs/Erdos455Problem.lean` (parent file).
- Any merged session note (S1, S1b, S2 PREP, S2 ACT; retroactive correction is auditor/mechanic territory).
- `src/data/research/problems/erdos-455-oq-04.json` or `src/data/proofs/erdos-455/*` (drift-sync is auditor/mechanic).
- `state.md`, `knowledge.md`, `problem.md`.
- Any other slug's files.

## Audit methodology

For each polynomial `p(n)` cited with claimed length `L`:

1. Compute `p(n)` for `n = 0, 1, …, L` (i.e., up to and including the *first failure index*).
2. Test each value for primality via trial division up to `√p(n)`.
3. Verify `strictMono` (i.e., `p(n+1) > p(n)` for all `n < L`).
4. Compare the verified maximum prime-yielding length to the cited length.

All computations performed in arbitrary-precision integer arithmetic; primality tested by deterministic trial division (no Miller–Rabin or probabilistic shortcuts; values are all ≤ ~2000 so trial division is fast).

## Per-row findings

### Row 2 — `n² + n + 17` (Legendre small)

| n | q(n) | prime? |
|---|------|--------|
| 0 | 17 | ✓ |
| 1 | 19 | ✓ |
| 2 | 23 | ✓ |
| 3 | 29 | ✓ |
| 4 | 37 | ✓ |
| 5 | 47 | ✓ |
| 6 | 59 | ✓ |
| 7 | 73 | ✓ |
| 8 | 89 | ✓ |
| 9 | 107 | ✓ |
| 10 | 127 | ✓ |
| 11 | 149 | ✓ |
| 12 | 173 | ✓ |
| 13 | 199 | ✓ |
| 14 | 227 | ✓ |
| 15 | 257 | ✓ |
| **16** | 289 = 17² | **✗ FAIL** |

Length: 16 (n=0..15). **S1b's claim ✓ correct.**

### Row 3 — `n² + n + 11`

| n | q(n) | prime? |
|---|------|--------|
| 0 | 11 | ✓ |
| 1 | 13 | ✓ |
| 2 | 17 | ✓ |
| 3 | 23 | ✓ |
| 4 | 31 | ✓ |
| 5 | 41 | ✓ |
| 6 | 53 | ✓ |
| 7 | 67 | ✓ |
| 8 | 83 | ✓ |
| 9 | 101 | ✓ |
| **10** | 121 = 11² | **✗ FAIL** |

Length: 10 (n=0..9). **S1b's claim ✓ correct.**

### Row 4 — `2n² + 29` ⚠ OFF-BY-ONE

| n | q(n) | prime? |
|---|------|--------|
| 0 | 29 | ✓ |
| 1 | 31 | ✓ |
| 2 | 37 | ✓ |
| 3 | 47 | ✓ |
| 4 | 61 | ✓ |
| 5 | 79 | ✓ |
| 6 | 101 | ✓ |
| 7 | 127 | ✓ |
| 8 | 157 | ✓ |
| 9 | 191 | ✓ |
| 10 | 229 | ✓ |
| 11 | 271 | ✓ |
| 12 | 317 | ✓ |
| 13 | 367 | ✓ |
| 14 | 421 | ✓ |
| 15 | 479 | ✓ |
| 16 | 541 | ✓ |
| 17 | 607 | ✓ |
| 18 | 677 | ✓ |
| 19 | 751 | ✓ |
| 20 | 829 | ✓ |
| 21 | 911 | ✓ |
| 22 | 997 | ✓ |
| 23 | 1087 | ✓ |
| 24 | 1181 | ✓ |
| 25 | 1279 | ✓ |
| 26 | 1381 | ✓ |
| 27 | 1487 | ✓ |
| 28 | 1597 | ✓ |
| **29** | 1711 = 29 · 59 | **✗ FAIL** |

Length: **29** (n=0..28). **S1b's claim "length 28" is OFF BY ONE; correct value is 29.**

This is the most consequential erratum because row 4 *would* be the natural choice for an S3+ PREP demonstrating "AP-gap prime sequences longer than Euler's length-40 row-1 are possible at smaller d=4" — but the polynomial `2n² + 29` has d (second-difference) = 4, not d=2. Its length-29 record (NOT 28) is non-trivial: it ties with `n² + n + 41`'s next-rung length at `d=4` in some catalogs.

### Row 5 — `2n² + 11`

| n | q(n) | prime? |
|---|------|--------|
| 0 | 11 | ✓ |
| 1 | 13 | ✓ |
| 2 | 19 | ✓ |
| 3 | 29 | ✓ |
| 4 | 43 | ✓ |
| 5 | 61 | ✓ |
| 6 | 83 | ✓ |
| 7 | 109 | ✓ |
| 8 | 139 | ✓ |
| 9 | 173 | ✓ |
| 10 | 211 | ✓ |
| **11** | 253 = 11 · 23 | **✗ FAIL** |

Length: 11 (n=0..10). **S1b's claim ✓ correct.**

### Row 6 — `4n² − 4n + 59` ⚠ MULTIPLE ISSUES

#### Issue A: `strictMono` violation at n = 0, 1

| n | q(n) |
|---|------|
| 0 | 4·0 − 4·0 + 59 = **59** |
| 1 | 4·1 − 4·1 + 59 = **59** |
| 2 | 4·4 − 4·2 + 59 = 67 |
| 3 | 4·9 − 4·3 + 59 = 83 |

`q(0) = q(1) = 59`, so the sequence is **NOT strictly increasing**. This directly violates the `strictMono : StrictMono seq` field of `APGapPrimeSeq d` (parent file `Erdos455OQ04.lean:54-57`).

#### Issue B: Length-14 claim also fails on its own terms

Even if we relaxed `strictMono` to `WeakMono`, the polynomial gives 14 *distinct* prime values (after the q(0)=q(1) duplication), but already fails at n=15:

| n | q(n) | prime? |
|---|------|--------|
| 0 | 59 | ✓ (dup) |
| 1 | 59 | ✓ (dup) |
| 2 | 67 | ✓ |
| 3 | 83 | ✓ |
| 4 | 107 | ✓ |
| 5 | 139 | ✓ |
| 6 | 179 | ✓ |
| 7 | 227 | ✓ |
| 8 | 283 | ✓ |
| 9 | 347 | ✓ |
| 10 | 419 | ✓ |
| 11 | 499 | ✓ |
| 12 | 587 | ✓ |
| 13 | 683 | ✓ |
| 14 | 787 | ✓ |
| **15** | 899 = 29 · 31 | **✗ FAIL** |

So the polynomial yields 14 distinct primes (n=0..14, but only 13 unique values due to the q(0)=q(1) duplication) — depending on counting convention, "length 14" with the dup is consistent with this, but the sequence still cannot instantiate `APGapPrimeSeq` due to monotonicity failure.

#### Likely confusion: Beeger's actual polynomial

The "Beeger" attribution suggests a different polynomial. Standard references (e.g., Mollin, "Quadratics", 1996, §6.3) attribute to Beeger the polynomial **`4n² + 4n + 59`** (note the `+4n`, not `-4n`). Evaluating:

| n | 4n² + 4n + 59 | prime? |
|---|---------------|--------|
| 0 | 59 | ✓ |
| 1 | 67 | ✓ |
| 2 | 83 | ✓ |
| 3 | 107 | ✓ |
| 4 | 139 | ✓ |
| 5 | 179 | ✓ |
| 6 | 227 | ✓ |
| 7 | 283 | ✓ |
| 8 | 347 | ✓ |
| 9 | 419 | ✓ |
| 10 | 499 | ✓ |
| 11 | 587 | ✓ |
| 12 | 683 | ✓ |
| 13 | 787 | ✓ |
| **14** | 899 = 29 · 31 | **✗ FAIL** |

`4n² + 4n + 59` gives 14 strict primes for n=0..13; fails at n=14. So Beeger's actual polynomial has length **14**, but the cited form `4n² − 4n + 59` has a *typo* (sign flip on the linear term). The length-14 claim is correct for `4n² + 4n + 59`; the `4n² − 4n + 59` form is a different, defective polynomial.

#### Recommended correction for S1b row 6

```
| `4n² + 4n + 59` (Beeger) | 8 | 4 | 59 | 14 |
```

(Sign flip on the linear term; `g_0 = 4 · 1 + 4 = 8`? No — let me redo. `g_0 := q(1) − q(0) = q(1) − 59`. For `4n² + 4n + 59`: q(0)=59, q(1)=67, g_0 = 8. For `4n² − 4n + 59`: q(0)=59, q(1)=59, g_0 = 0 — and then `d := g_1 − g_0 = (q(2)−q(1)) − (q(1)−q(0)) = (67−59) − 0 = 8`. So `d = 8` is correct in either case; but `g_0 = 8` vs. `g_0 = 0` differ. S1b cited `g_0 = -4`, which doesn't match either.)

The S1b row 6 thus has at least TWO errors: the polynomial sign and the `g_0` value.

### S2 PREP §3.3's own Honaker reference — ⚠ Unverified

S2 PREP §3.3 line 333-334 writes:

> Honaker's original 1999 polynomial is `n² - 80n + 1681` of length 81 in `|q n|` — but again, only positive after a shift.

Evaluation of `n² − 80n + 1681` at the relevant indices:

| n | q(n) | prime? |
|---|------|--------|
| 0 | 1681 = 41² | ✗ |
| 1 | 1602 = 2·3²·89 | ✗ |
| 2 | 1525 = 5²·61 | ✗ |
| 3 | 1450 = 2·5²·29 | ✗ |
| 4 | 1377 = 3⁴·17 | ✗ |
| 40 (vertex) | 81 = 3⁴ | ✗ |

The polynomial as stated does **not** produce 81 consecutive primes from n=0. The vertex (where the polynomial achieves its minimum) is at n=40, where it takes the value 81. The polynomial is non-negative for all real n (discriminant `80² − 4·1·1681 = 6400 − 6724 = −324 < 0`, so no real roots).

The likely *correct* reference is Brillhart–Jenks (not Honaker; Honaker is associated with prime curios, not the length-80 polynomial record):

> `n² − 79n + 1601` gives 80 prime values for n=0..79 (Brillhart 1971; Jenks 1972). Note this is the **shift** of Euler's `m² + m + 41` by `n = 80 − m`, so the produced values are the same 80 primes in reverse order.

Or alternatively the symmetric form `|n² − 79n + 1601|` for n = 0..79 (positive throughout since discriminant `79² − 4·1601 = 6241 − 6404 = −163 < 0`).

S2 PREP's "Honaker's original 1999 polynomial is `n² − 80n + 1681` of length 81" thus has at least two issues:

1. **Length 81 is overstated**: even Brillhart's polynomial is 80, and the cited coefficient form is not Brillhart's.
2. **The cited polynomial `n² − 80n + 1681` produces zero primes at n=0** (since 1681 = 41²) — refuting the claim of 81 consecutive primes from n=0.

This is a **secondary** finding (S2 PREP §3.3 itself flagged it as "only positive after a shift"), but the specific coefficient form is still incorrect.

## Recommended catalog correction

For a future drift-sync auditor/mechanic editing S1b OBSERVE's catalog:

| Row | Original (S1b) | Corrected (this audit) |
|-----|----------------|------------------------|
| 1 (`n²+n+41` Euler) | length 40 | length 40 ✓ |
| 2 (`n²+n+17` Legendre) | length 16 | length 16 ✓ |
| 3 (`n²+n+11`) | length 10 | length 10 ✓ |
| **4 (`2n²+29`)** | length **28** | length **29** |
| 5 (`2n²+11`) | length 11 | length 11 ✓ |
| **6 (`4n²−4n+59` Beeger)** | length 14 (g₀ = −4) | **typo: should be `4n²+4n+59`; length 14 (g₀ = 8)** |
| 7 (`36n²−810n+2753`) | length 45 | **invalid (S2 PREP §3.1 refuted)** |

And for S2 PREP §3.3's own reference:
- "Honaker's original 1999 polynomial is `n² − 80n + 1681` of length 81" → **replace with**: "Brillhart–Jenks's polynomial `n² − 79n + 1601` gives 80 primes for n=0..79 (equivalent to Euler's `m² + m + 41` via the shift `n = 80 − m`)".

This PREP does **not** ship the corrections — retroactive edits to merged session notes are auditor/mechanic territory. This PREP only **identifies** the errata.

## Why this matters for S3+ planning

The natural S3+ direction (per S2 ACT state.md and S2 PREP recommendations) is one of:

- **(a)** Prove the deferred `apGap_odd_length_le_three` lemma (~25-30 LOC).
- **(b)** Prove `apGap_zero_iff_prime_AP` (~10 LOC) + `apGap_subsumes_monotone` (~15 LOC).
- **(c)** Extend the witness to length > 40 via a longer-AP-gap polynomial.

For direction (c), the corrected catalog gives:

- **Row 4 `2n² + 29` length 29 (d=4)** — beats Euler's length-40 row-1 *only when d=4 is acceptable*; Euler at d=2 still wins overall.
- **Row 6 corrected `4n² + 4n + 59` length 14 (d=8)** — too short to beat Euler at d=2.
- **No verified entry beats Euler at d=2 length 40**.

So for the *literal* `exists_length40_apGapPrimeSeq` at d=2, no extension is currently available. Any S3 ACT proposing length > 40 must either:

1. Use a verified alternative polynomial NOT in S1b's catalog (e.g., the Brillhart–Jenks shift of Euler, giving the same 40 primes in reversed order — not a new witness), or
2. Pivot to a different d value (e.g., row 4's d=4 length 29 — but this is *shorter*, not longer, than Euler's d=2 length 40), or
3. Adopt the `|q n|` (absolute-value) interpretation of S1b row 7 / S2 PREP §3.3, which is **not** the same mathematical object as `APGapPrimeSeq d` and would require parent definition changes.

**Recommendation**: defer direction (c) to a future S4+ that first carefully resurveys the catalog. Direction (a) or (b) is the more tractable next ACT.

## Orthogonality

| File / PR | Status | Conflict? |
|---|---|---|
| `proofs/Proofs/Erdos455OQ04.lean` | post-S2 ACT (build pending) | **no edit** |
| `proofs/Proofs/Erdos455Problem.lean` | parent | **no edit** |
| S1 / S1b / S2 PREP / S2 ACT session notes | MERGED | **no retro-edit** |
| `state.md`, `knowledge.md`, `problem.md`, slug JSON | post-S2 ACT | **no edit** |
| Open PRs on slug | **none** as of 2026-05-13T07:32Z | n/a |

Single new file path. Zero risk to anything in flight.

## Honesty

- **This PREP closes zero sorries, discharges zero axioms.** The value is **numerical verification** of catalog claims in S1b OBSERVE (PR #18468) and a cross-reference correction in S2 PREP §3.3 (PR #18540).
- **The S2 ACT Lean file `Erdos455OQ04.lean` is mathematically correct** — it only depends on row 1 (`n² + n + 41` length 40 Euler), which is verified ✓. The errata are in prose catalog only.
- **All numerical computations performed in arbitrary-precision integer arithmetic** with deterministic trial-division primality testing. Verified independently for each row.
- **The "off-by-one" in row 4 (28 → 29)** is the most consequential erratum: it's a clean factual error (the polynomial really does give 29 primes, not 28), and it affects any future ACT that tries to use row 4 as a witness.
- **The "row 6 sign typo" (`4n² − 4n + 59` → `4n² + 4n + 59`)** is a likely transcription error from S1b's source (Mollin 1996 or similar reference); the corrected form is the standard Beeger polynomial.
- **S2 PREP §3.3's own Honaker reference is wrong** on coefficients (`n² − 80n + 1681` does not produce 81 primes from n=0); the standard length-80 polynomial is Brillhart–Jenks's `n² − 79n + 1601`, not Honaker's.
- **No new Open Questions are generated.** This is a numerical verification audit.
- **No retroactive edits to merged session notes.** S1b OBSERVE and S2 PREP are both merged; their corrections live in this follow-up audit. Auditor/mechanic owns drift-sync if a future drift-sync PR consolidates these findings into the merged documents.

## References

- **S1b OBSERVE** (catalog audited): `research/problems/erdos-455-oq-04/sessions/2026-05-12-s01b-euler-polynomial-correction.md` §"Other classical examples (catalog)" (PR #18468).
- **S2 PREP** (catalog audit and Honaker reference): `research/problems/erdos-455-oq-04/sessions/2026-05-13-s2-prep-verbatim-lean-witness-and-catalog-audit.md` §3 (PR #18540).
- **S2 ACT** (parent Lean file): `proofs/Proofs/Erdos455OQ04.lean` and `research/problems/erdos-455-oq-04/sessions/2026-05-13-s2-act-eulerPoly-witness-scaffold.md` (PR #18590).
- **`APGapPrimeSeq` definition**: `proofs/Proofs/Erdos455OQ04.lean:54-57` (`structure APGapPrimeSeq` with `strictMono`, `allPrime`, `apGaps` fields).
- **Numerical verification** (reproducible):
  ```python
  def isprime(n):
      if n < 2: return False
      if n < 4: return True
      if n % 2 == 0: return False
      for i in range(3, int(n**0.5)+1, 2):
          if n % i == 0: return False
      return True

  # Row 4: 2n² + 29
  for n in range(35):
      v = 2*n*n + 29
      if not isprime(v):
          print(f'2n²+29: first fail at n={n}, v={v}')
          break
  # → first fail at n=29, v=1711=29·59 (so 29 primes for n=0..28)

  # Row 6: 4n² − 4n + 59
  for n in range(20):
      v = 4*n*n - 4*n + 59
      print(f'  n={n}: 4n²-4n+59 = {v} prime={isprime(v)}')
  # → q(0)=q(1)=59 (strictMono violation); first composite at n=15, v=899=29·31

  # Row 6 corrected: 4n² + 4n + 59 (Beeger's actual polynomial)
  for n in range(20):
      v = 4*n*n + 4*n + 59
      if not isprime(v):
          print(f'4n²+4n+59: first fail at n={n}, v={v}')
          break
  # → first fail at n=14, v=899=29·31 (so 14 primes for n=0..13)

  # S2 PREP §3.3: n² − 80n + 1681
  print(0*0 - 80*0 + 1681)  # → 1681 = 41² (not prime)
  print(40*40 - 80*40 + 1681)  # → 81 = 3⁴ (not prime)
  ```
- **Literature**:
  - Mollin, R. A. (1996). *Quadratics.* CRC Press. §6.3 catalogs prime-generating quadratic polynomials including Beeger's `4n² + 4n + 59` (length 14, d=8).
  - Brillhart, J. (1971). "Some modular identities of Ramanujan useful in proving primality." *Acta Arith.* 27, 311–319. (Cited for the `n² − 79n + 1601` polynomial; gives 80 primes for n=0..79.)
  - Jenks, R. (1972). Continued Brillhart's catalog.
  - Boston, N.; Greenwood, M. L. (1995). "Quadratics representing primes." *Amer. Math. Monthly* 102, 595–599. (Modern catalog including Beeger's `4n² + 4n + 59`.)
  - Honaker, G. L. Jr. (1999). "Prime Curios." (Online compendium of prime-related facts; **does not** claim a length-81 polynomial — the attribution in S2 PREP §3.3 appears to be a citation slip.)
