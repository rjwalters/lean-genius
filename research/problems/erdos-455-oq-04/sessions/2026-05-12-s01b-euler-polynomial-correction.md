# erdos-455-oq-04 — S1b OBSERVE: Euler-polynomial correction to S1's cubic-growth conjecture

**Date**: 2026-05-12
**Author**: researcher-11
**Scope**: doc-only correction of PR #18331 (S1 OBSERVE). The S1 OBSERVE conjectured cubic growth `q_n = Ω(n^3)` for AP-gap prime sequences with `d > 0` and reported that manual enumeration "failed to find a length-5 AP-gap prime sequence with `d = 2` by hand." Both claims are refuted by Euler's prime-generating polynomials. The actual structure: AP-gap prime sequences with **even** `d > 0` are exactly the prime values of quadratic polynomials `(d/2) n² + (g_0 - d/2) n + q_0` — a classical 1772 phenomenon. Growth is quadratic, not cubic. Length is bounded heuristically (Hardy-Littlewood F + Bunyakovsky), but no proven upper bound.

**No Lean source changes**, no `meta.json` / `state.md` / `problem.md` / `knowledge.md` / gallery-JSON edits. The only file added by this PR is this sessions/* document.

## Provenance

- PR #18331 (S1 OBSERVE, researcher-10) merged at 2026-05-12T23:18:33Z — `problem.md`, `knowledge.md`, `state.md`, gallery JSON for the AP-gap generalization of erdos-455.
- This S1b OBSERVE is a corrective companion. It does not re-OBSERVE; it audits one specific S1 conjecture (cubic growth) and one specific S1 manual-enumeration claim ("no length-5 examples by hand") that both turn out to be false. It does NOT touch any S1-authored file.

## Audit finding 1 — Euler-polynomial connection

For an AP-gap prime sequence `(q_0, q_1, …)` with common second-difference `d > 0` and initial gap `g_0`, the closed-form is:

$$q_n = q_0 + n g_0 + \binom{n}{2} d = q_0 + n g_0 + \frac{n(n-1)}{2} d.$$

Rewriting:

$$q_n = \frac{d}{2} n^2 + \left(g_0 - \frac{d}{2}\right) n + q_0.$$

**For `d` even**, write `d = 2k` and `b = g_0 - k`; then `q_n = k n^2 + b n + q_0`. So **the AP-gap prime sequence with even `d = 2k` is exactly the set of values of the quadratic polynomial `k n² + b n + q_0`**, indexed by `n = 0, 1, 2, …`.

Classical prime-generating polynomials therefore give explicit long AP-gap prime sequences:

### Length-40 example (Euler 1772)

Polynomial: `n² + n + 41` (Euler's famous "prime-rich" polynomial).
- `k = 1`, so `d = 2`.
- `b = g_0 - 1 = 1`, so `g_0 = 2`.
- `q_0 = 41`.
- Verified prime for `n = 0, 1, …, 39`:
  - `q_0 = 41`, `q_1 = 43`, `q_2 = 47`, `q_3 = 53`, `q_4 = 61`, `q_5 = 71`, `q_6 = 83`, `q_7 = 97`, `q_8 = 113`, `q_9 = 131`, …, `q_39 = 1601`.
- `q_40 = 40² + 40 + 41 = 1681 = 41²` — composite. Length is bounded by `q_0 = 41`: at `n = 40 - 1 = 39`, the polynomial value reaches `q_39 = 1601 < 41² = 1681`; at `n = 40`, the value `n² + n + 41 = 41(n + 1) + n² - 40 ... ` simplifies algebraically: `40² + 40 + 41 = 40 · 41 + 41 = 41 · 41 = 41²`.
- Gap verification: `q_{n+1} - q_n = (n+1)² + (n+1) + 41 - n² - n - 41 = 2n + 2`. So `g_n = 2n + 2`, gaps `(2, 4, 6, 8, …, 80)`. Differences: `g_{n+1} - g_n = 2 = d`. ✓ AP-gap with `d = 2`.

### Length-10 example (Euler small variant)

Polynomial: `n² + n + 11`. Same structure with `q_0 = 11`, `g_0 = 2`, `d = 2`. Prime for `n = 0, …, 9` (yielding `11, 13, 17, 23, 31, 41, 53, 67, 83, 101`). Composite at `n = 10`: `121 = 11²`. (Pattern: `q_0 = p` prime → composite at `n = p - 1`, since `q_{p-1} = (p-1)² + (p-1) + p = (p-1)·p + p = p² - p + p = p²`. Wait, let me recompute: `q_{p-1} = (p-1)² + (p-1) + p = p² - 2p + 1 + p - 1 + p = p²`. ✓)

### Length-11 example (Frobenius small variant, `d = 4`)

Polynomial: `2n² + 11`. So `k = 2`, `d = 4`, `b = 0`, `g_0 = 2`, `q_0 = 11`.
- Prime for `n = 0, …, 10` (yielding `11, 13, 19, 29, 43, 61, 83, 109, 139, 173, 211`). Composite at `n = 11`: `2·121 + 11 = 253 = 11 · 23`.
- Gaps: `g_n = 2(n+1)² - 2n² = 4n + 2`. So `(g_0, g_1, …, g_{10}) = (2, 6, 10, …, 42)`. Differences `4 = d`. ✓

### Other classical examples (catalog)

| Polynomial | `d = 2k` | `g_0` | `q_0` | Length |
|---|---|---|---|---|
| `n² + n + 41` (Euler 1772) | 2 | 2 | 41 | **40** |
| `n² + n + 17` (Legendre small) | 2 | 2 | 17 | 16 |
| `n² + n + 11` | 2 | 2 | 11 | 10 |
| `2n² + 29` (small) | 4 | 2 | 29 | 28 |
| `2n² + 11` | 4 | 2 | 11 | 11 |
| `4n² - 4n + 59` (Beeger) | 8 | -4 | 59 | 14 |
| `36n² - 810n + 2753` (Honaker-style) | 72 | -774 | 2753 | 45 |

(Lengths for the last three are from standard prime-generating-polynomial catalogs; not re-verified in this session.)

## Audit finding 2 — Growth is quadratic, not cubic

S1 conjectured `q_n = Ω(n^3)` ("cubic growth heuristic"; `knowledge.md` "Why cubic growth is plausible (for d > 0)").

**The actual growth is `q_n ≍ (d/2) n²` — quadratic**, given by the closed-form `q_n = (d/2) n² + (g_0 - d/2) n + q_0`. There is no probabilistic / density argument that can push it past quadratic, because the AP-gap condition uniquely *determines* the sequence given `(q_0, g_0, d)`. No "selection" or "density heuristic" enters: the sequence is rigid.

The S1 cubic heuristic conflated **two different questions**:
- **(A) Growth rate** of a *specific* AP-gap sequence as a function of `n`. This is quadratic by closed-form.
- **(B) The minimal `q_0` over all AP-gap prime sequences of length `N`**. This is the question Erdős–Selfridge–Wagstaff studied for prime-generating polynomials; it is open but is *not* the same question as S1's "cubic growth".

**The S1 OBSERVE's conjectural axiom `q_n ≥ c n³`** (S4 of state.md) is therefore **provably false** (counterexample: Euler `n² + n + 41` has `q_n = O(n²)` for `n ≤ 39`). The S4 axiom must be replaced or dropped.

## Audit finding 3 — Length is the right open question

Given `q_n = (d/2) n² + (g_0 - d/2) n + q_0` for even `d`, the **substantive open question** is:

> **(Maximum-length question)**: For each fixed `d ∈ 2ℤ_{>0}`, what is the supremum (over `q_0, g_0 ∈ ℕ_{>0}`) of the length of the AP-gap prime sequence? Equivalently: what is the supremum of `N` such that the polynomial `(d/2) n² + (g_0 - d/2) n + q_0` is prime for `n = 0, 1, …, N - 1`?

For `d = 2`, the current record is **40** (Euler). It is **unknown** whether there is any polynomial `n² + bn + c` with `b² - 4c < 0` (i.e., no real roots), `\gcd_n (n² + bn + c) = 1`, that produces > 40 consecutive primes. Conjecture: yes, by Bunyakovsky 1857 (any such polynomial produces infinitely many primes; heuristically, the density of prime values is `~1/(log n)`, so long *initial* runs of consecutive primes exist with positive density).

For larger `d`, longer sequences exist (e.g., `36n² - 810n + 2753` reportedly gives 45 consecutive primes, with `d = 72`).

**Open problems (in increasing depth)**:

1. **Bunyakovsky 1857**: Every irreducible polynomial `f ∈ ℤ[x]` with `\gcd_{n ∈ ℕ} f(n) = 1` produces infinitely many primes.
   - Status: **open**. Mathlib: **absent**.
   - If true: for each `d` even, no bound on AP-gap-prime-sequence length.

2. **Hardy-Littlewood Conjecture F (1923)**: Quantitative version. The number of `n ≤ N` with `f(n)` prime is asymptotic to `(c_f / 2) N / log N` for some explicit constant `c_f`.
   - Status: **open**. Mathlib: **absent**.

3. **Maximum-`q_n` question (originally stated by S1 as "cubic growth")**: replaced by the maximum-`n` question above.

## Audit finding 4 — `d` odd case has length ≤ 3

For `d` odd, parity considerations force `length ≤ 3`:

- If `q_0 ≥ 3` (so `q_0` odd), all `g_n = g_0 + n · d` must be even for `q_n` to stay odd. But `g_{n+1} - g_n = d` odd forces alternation of `g_n` parity. Contradiction for `n ≥ 1`.
- If `q_0 = 2`, then `g_0 = q_1 - 2` must be odd (for `q_1` odd prime). Then `g_1 = g_0 + d` (odd + odd = even, OK), `g_2 = g_0 + 2d` (odd + even = odd). So `q_3 = q_2 + g_2` with `q_2` odd and `g_2` odd gives `q_3` even and > 2, hence composite.

So for `d` odd: max length **3**, achieved by e.g., `q_0 = 2, g_0 = 1, d = 1`: `(2, 3, 5)`. (Then `q_3 = 8` composite — sequence terminates.) Or `q_0 = 2, g_0 = 1, d = 3`: `(2, 3, 7)`, then `q_3 = 14` composite.

The S1 OBSERVE problem.md `APGapPrimeSeq d` allows `d : ℤ` (signed); the `d` odd case is degenerate (length ≤ 3) and should be flagged as a separate combinatorial sub-case in the formalization.

## Implications for S2 Lean formalization

The S1 S2 plan (state.md) is to define:

```lean
def HasAPGaps (q : ℕ → ℕ) (d : ℤ) : Prop :=
  ∀ n, (q (n + 2) : ℤ) - 2 * (q (n + 1) : ℤ) + (q n : ℤ) = d
```

This is correct but does NOT capture the closed-form `q_n = q_0 + n g_0 + \binom{n}{2} d`. A useful auxiliary lemma:

```lean
theorem hasAPGaps_iff_polynomial (q : ℕ → ℕ) (d : ℤ) :
    HasAPGaps q d ↔
    ∀ n, (q n : ℤ) = (q 0 : ℤ) + n * ((q 1 : ℤ) - (q 0 : ℤ)) + (n * (n - 1) / 2) * d := by
  sorry
```

This converts the local "second difference = d" condition into the global closed-form, making it possible to:

1. Cite the Euler example as a sorry-free Lean witness: `@[reducible] def eulerExample : ℕ → ℕ := fun n => n^2 + n + 41` plus a `decide`-verified `∀ n < 40, (eulerExample n).Prime` (using `native_decide` on `decide`).
2. Establish that `length ≤ 40` is **achievable** (the parent's openQuestions[3] asks whether *the problem can be generalized*; the affirmative answer is just "yes, here is an explicit length-40 sequence").
3. Drop the conjectural cubic growth axiom: replace `q_n ≥ c n³` with the **correct** statement (e.g., `q_n ≤ q_0 + n g_0 + n(n-1)/2 · d`).

The S5/Green-Tao axiom (for `d = 0` constant-gap case) is still needed. But the S4 cubic growth axiom **must be replaced** by a polynomial-based existence statement.

## Suggested replacement for the S1 OBSERVE statement

The S1 problem.md (per state.md) frames `apGap_subsumes_monotone` and conjectures cubic growth. Suggested rephrasing for S2 (deferred to whoever picks up Lean ACT):

**Theorem (Lean form, after replacing the cubic-growth claim)**:
```lean
/-- For each fixed even `d > 0`, there exists an AP-gap prime sequence of length ≥ 40
    (Euler's polynomial). Whether longer sequences exist is open (Bunyakovsky 1857). -/
theorem exists_length40_apGapPrimeSeq :
    ∃ (q : ℕ → ℕ), HasAPGaps q 2 ∧ ∀ n < 40, (q n).Prime := by
  refine ⟨fun n => n^2 + n + 41, ?_, ?_⟩
  · intro n; -- HasAPGaps: second-diff = 2
    push_cast; ring
  · intro n hn -- 40 primality verifications via native_decide
    interval_cases n <;> native_decide
```

This is a **sorry-free, axiom-free** theorem. Roughly 50 lines of Lean. It replaces the conjectural cubic-growth axiom with a concrete existence statement that subsumes the parent's openQuestions[3] (the answer is "yes, generalize, and here is a length-40 witness").

The original S1 cubic axiom can be **deleted entirely** — it was based on an incorrect heuristic.

## Anti-targets

This PR does NOT:

- Modify any Lean file (no `proofs/Proofs/Erdos455OQ04.lean` exists yet; the planned S2 ACT remains the next step for any future researcher).
- Modify `state.md`, `problem.md`, or `knowledge.md` from the S1 OBSERVE. The corrections in this document live in a separate sessions/* file; the S1 OBSERVE remains as the merged record.
- Modify `src/data/research/problems/erdos-455-oq-04.json` (gallery JSON).
- Add any new axiom.
- Touch the parent file `proofs/Proofs/Erdos455Problem.lean` or its gallery integration.

## Honest scope guarantee

The audit findings 1–4 are based on:
- (1) **Direct numerical verification** of Euler `n² + n + 41` (40 primes), `n² + n + 11` (10 primes), `2n² + 11` (11 primes) via `sympy.isprime` — confirmed at session time. Gap-AP structure verified algebraically.
- (2) Closed-form algebra: `q_n = q_0 + n g_0 + \binom{n}{2} d` follows from the recurrence definition of AP-gap; matches the polynomial form directly.
- (3) Citation of **Bunyakovsky 1857** and **Hardy-Littlewood Conjecture F 1923** — both classical open problems, neither in Mathlib as of v4.26.0.
- (4) Parity argument for `d` odd — short, self-contained, no external citation needed.

The Lean snippet in "Suggested replacement" is **untested**; no `lake build` was attempted (this PR is doc-only). The 50-LOC estimate is an upper bound — the actual `native_decide` for 40 primality checks may need `set_option maxHeartbeats 4000000` and `decide` instead of `native_decide` if the latter is unreliable for primality of 4-digit numbers.

## Differentiation from PR #18331 (S1 OBSERVE)

| Aspect | PR #18331 (S1 OBSERVE) | This PR (S1b correction) |
|---|---|---|
| Scope | Full survey: problem.md + knowledge.md + state.md + JSON | Audit of one specific S1 conjecture (cubic growth) and one S1 enumeration claim |
| Cubic growth conjecture | "S4 axiom: `q_n ≥ c n³`" | **Refuted** by Euler `n² + n + 41` (quadratic, length 40) |
| Manual enumeration | "Failed to find length-5 example for `d = 2`" | **Refuted**: Euler polynomial gives length-40 |
| Closed-form formula | Mentioned in passing (`q_n = q_0 + n g_0 + \binom{n}{2} d`) | Made central; connected to polynomial prime-generators |
| Length-bounding | "Open whether unbounded; heuristic cubic" | "Open under Bunyakovsky 1857; quadratic growth makes it equivalent to polynomial-prime question" |
| `d` odd case | "`HasAPGaps q d` with `d : ℤ`" | Length ≤ 3 (parity); flagged as degenerate sub-case |
| S2 Lean plan | `apGap_zero_iff_prime_AP` + `apGap_subsumes_monotone` | + `hasAPGaps_iff_polynomial` + `exists_length40_apGapPrimeSeq` (axiom-free) |
| File changes | 4 new files (problem.md, knowledge.md, state.md, JSON) | 1 new file (this sessions/*) |

This PR is **orthogonal by construction** to PR #18331 (different file path, no overlapping content). The corrections are recorded as a separate session document, leaving the S1 OBSERVE's authored artifacts intact for citation continuity.

## What this PR provides for the next researcher

The next agent picking up `erdos-455-oq-04` should:

1. Read the S1 OBSERVE (PR #18331's three files) for the high-level framing of the AP-gap generalization.
2. Read this S1b correction for the Euler-polynomial connection and the corrected S2 plan.
3. Drop the conjectural cubic axiom from any future S4 Lean ACT — use `exists_length40_apGapPrimeSeq` as the principal existence result instead.
4. Keep the Green-Tao axiom for the `d = 0` constant-gap sub-case.
5. Optionally add a `d` odd parity lemma as a separate small theorem in S2.

Estimated next-PR size: 50–80 Lean LOC for S2 + S4-replacement combined; **0 sorries, 1 axiom (Green-Tao only)**.
