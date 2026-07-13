# S2 Session — Mathlib Archive Audit (Duplicate-Detection)

**Date**: 2026-05-12
**Agent**: researcher-11
**Phase**: OBSERVE (audit), complementary to S1 OBSERVE of PR #18220
**Outcome**: Reclassification recommended — see §5

---

## Thesis

The seeker-generated open question

> *Euler converse: every even perfect number is Mersenne-form*

is **already discharged in the gallery** by a verified one-line theorem that
appeals to a Mathlib `Archive` lemma. Both the OQ statement and its
characterization-flavored sibling are exported, with concrete witnesses for
the first four perfect numbers `{6, 28, 496, 8128}`. No new Lean is required
to close OQ-02. Below we trace the duplication line-by-line, audit the
upstream Archive proof's intermediate lemmas, and propose follow-up open
questions that are genuinely fresh.

This audit is intentionally orthogonal to PR #18220's S1 OBSERVE:

| Aspect | PR #18220 (S1) | This audit (S2, doc-only) |
| --- | --- | --- |
| Goal | Sketch a 7-step skeleton for a future `Proofs/SumOfDivisorsOQ02.lean` | Verify that the *same theorem* already exists in main and recommend SKIP / pivot |
| Files | `knowledge.md`, `problem.md`, `state.md`, `*.json` | `sessions/2026-05-12-s2-mathlib-archive-audit.md` only |
| Direction | Forward (build a new scaffold) | Backward (close as duplicate, redirect effort) |
| Honesty caveat | "If structurally identical to the Archive's proof, contribution reduces to documentation/naming." | We confirm this caveat is binding; the Archive proof *is* the skeleton. |

If #18220 lands first, a maintainer can use this audit to decide whether to
follow through with the S2 SCAFFOLD or pivot. Either ordering is safe — the
two PRs touch disjoint files.

---

## 1. Where the OQ is already discharged

### 1.1 Direct one-line discharge — `proofs/Proofs/PerfectNumbers.lean:107-109`

```lean
theorem euler_even_perfect (n : ℕ) (h_even : Even n) (h_perfect : n.Perfect) :
    ∃ k, (mersenne (k + 1)).Prime ∧ n = 2 ^ k * mersenne (k + 1) :=
  Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect h_even h_perfect
```

This **is** OQ-02. Side-by-side:

| OQ-02 (informal) | `euler_even_perfect` (Lean) |
| --- | --- |
| `n` is even | `h_even : Even n` |
| `n` is perfect (`σ(n) = 2n`) | `h_perfect : n.Perfect` |
| ∃ Mersenne prime `M` and exponent `k` with `n = 2^k · M` | `∃ k, (mersenne (k + 1)).Prime ∧ n = 2 ^ k * mersenne (k + 1)` |

The two statements are pointwise the same modulo the standard `Mersenne k = 2^k - 1`
indexing convention. The proof is **definitional** modulo a single appeal to
the Mathlib Archive. There are no sorries.

### 1.2 Biconditional companion — `proofs/Proofs/PerfectNumbers.lean:119-122`

```lean
theorem even_perfect_iff (n : ℕ) :
    (Even n ∧ n.Perfect) ↔
    ∃ k, (mersenne (k + 1)).Prime ∧ n = 2 ^ k * mersenne (k + 1) :=
  Theorems100.Nat.even_and_perfect_iff
```

This is the **full Euclid-Euler theorem** (both directions). OQ-02 is the
forward direction; Euclid's ancient result (300 BCE) is the converse.

### 1.3 Gallery integration — `src/data/proofs/perfect-numbers/meta.json`

The `perfect-numbers` gallery entry already advertises both theorems with
status `"verified"`, badge `"mathlib"`, `"sorries": 0`, and explicit
`mathlibDependencies` entries citing the Archive theorems.
[Tag: `"wiedijk-100"`]

### 1.4 Parent slug status — `src/data/research/problems/sum-of-divisors.json`

The PARENT `sum-of-divisors` is marked `"status": "completed"` with phase
`"COMPLETED"` and a knowledge-markdown body that explicitly says:

> "This problem is marked **SKIPPED** because related content already exists
> in the proof gallery. … The original problem statement was general 'sum
> of divisors properties' without specific goals. Since our
> PerfectNumbers.lean already covers: 1) the σ function behavior, 2) Perfect
> number characterization, 3) Euclid-Euler theorem … there's no clear
> additional target that would justify a separate research track."

OQ-02 is the seeker re-spawning a sub-question that the parent already
disposed of.

---

## 2. Step-by-step trace: PR #18220's skeleton ↔ Archive proof

PR #18220 listed a 7-step algebraic skeleton for the Euler converse. Each
step is **already** an intermediate or named Mathlib lemma. Below we trace
each step to its likely Archive/Mathlib counterpart at Mathlib v4.26.0.

> Caveat: the constant names quoted are observed from the local
> `PerfectNumbers.lean` (lines cited above) plus the established Mathlib
> naming convention for `Theorems100.Nat.*` and `ArithmeticFunction.*`. The
> Archive module `Archive.Wiedijk100Theorems.PerfectNumbers` is imported on
> line 1 of `PerfectNumbers.lean`. A maintainer with build access can
> spot-check the exact internal helper names via `#check` queries.

| # | Skeleton step (PR #18220) | Mathlib / Archive realization |
| --- | --- | --- |
| 1 | `σ(2^k · m) = σ(2^k) · σ(m)` (multiplicativity on coprimes) | `ArithmeticFunction.IsMultiplicative.sigma`, applied with `Nat.Coprime.pow_left_iff` (`gcd(2^k, m) = 1` because `m` is odd) |
| 2 | `σ(2^k) = 2^(k+1) - 1 = M_{k+1}` | `Theorems100.Nat.sigma_two_pow_eq_mersenne_succ` — re-exported as `sigma_two_pow` at `PerfectNumbers.lean:83-84` |
| 3 | `M_{k+1} · σ(m) = 2^(k+1) · m` (perfect-equation expansion) | `Nat.perfect_iff_sum_divisors_eq_two_mul` — re-exported as `perfect_iff_divisor_sum` at `PerfectNumbers.lean:71-73`, plus arithmetic |
| 4 | `M_{k+1} ∣ m` (coprime extraction) | Standard: `Nat.Coprime.dvd_of_dvd_mul_right` applied to `M_{k+1} ∣ 2^(k+1) · m` and `Nat.Coprime M_{k+1} (2^(k+1))` |
| 5 | `m = M_{k+1} · c`, then `σ(m) = 2^(k+1) · c = m + c` | Internal to Archive; algebraic substitution |
| 6 | `c ∣ m`, `σ(m) = m + c` ⇒ `c = 1` ∧ `m` prime (two-divisor uniqueness) | Internal to Archive; uses `Nat.sigma_one_eq_self_iff_prime` or equivalent two-divisor characterization |
| 7 | Conclude `n = 2^k · M_{k+1}` with `M_{k+1}` prime | Returns the existential — `Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect` |

Steps 1, 2, 3, 7 are exposed as gallery theorems. Steps 5 and 6 are *inside*
the Archive proof of step 7 — re-exposing them as separate Lean lemmas would
duplicate the Archive's internal structure, not extend it.

---

## 3. Mathlib v4.26.0 API surface (verifiable in S3 if pursued)

Constants imported or used by `PerfectNumbers.lean`, confirmed by direct
inspection of file 1:202 in main:

```
import Archive.Wiedijk100Theorems.PerfectNumbers
import Mathlib.Tactic

-- Confirmed used (search hits in main):
Nat.perfect_iff_sum_divisors_eq_two_mul        -- line 73
Theorems100.Nat.sigma_two_pow_eq_mersenne_succ -- line 84
Theorems100.Nat.perfect_two_pow_mul_mersenne_of_prime -- line 98
Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect -- line 109 (= OQ-02)
Theorems100.Nat.even_and_perfect_iff           -- line 122
mersenne                                       -- (Mathlib) Mₚ = 2^p - 1
ArithmeticFunction.sigma                       -- σ_k
```

A future S3 audit should `#check` each of these names against the live
Mathlib pin to flag drift before any new file is written.

---

## 4. Numerical sanity (concrete instances)

The Euler converse pins each even perfect number to a unique Mersenne prime
exponent. Witnesses already in `PerfectNumbers.lean`:

| Index | Perfect number `n` | Mersenne exponent `p` | `M_p = 2^p − 1` | Lean theorem |
| --- | --- | --- | --- | --- |
| 1 | 6 | 2 | 3 | `six_is_perfect` (line 132) |
| 2 | 28 | 3 | 7 | `twentyeight_is_perfect` (line 141) |
| 3 | 496 | 5 | 31 | `fourhundredninetysix_is_perfect` (line 150) |
| 4 | 8128 | 7 | 127 | `eightthousandonetwentyeight_is_perfect` (line 159) |

Beyond those, the next four (extending via known GIMPS Mersenne primes; not
in Lean but provable by `native_decide`):

| Index | `n` | `p` | `M_p` |
| --- | --- | --- | --- |
| 5 | 33,550,336 | 13 | 8191 |
| 6 | 8,589,869,056 | 17 | 131071 |
| 7 | 137,438,691,328 | 19 | 524287 |
| 8 | 2,305,843,008,139,952,128 | 31 | 2,147,483,647 |

(`p = 11` is skipped because `2^11 − 1 = 23 · 89` is composite — a useful
counterexample showing the Mersenne primality hypothesis cannot be dropped.)

These eight rows exhaust the explicit known cases formalizable today via
`native_decide`. Any further entries (`p = 61, 89, …`) are unproblematic
arithmetic but yield numbers exceeding standard `UInt64` ranges and would
need `Nat.decide` with care.

---

## 5. Recommendation: close OQ-02 as duplicate

Concretely, we recommend one of:

### Option A — Close immediately
- Change `status` in `.lean/state/candidate-pool.json` from `"available"` to
  `"completed"` (or `"graduated"` if maintainers prefer a softer signal that
  the work is upstream rather than abandoned).
- Add a note: `"Closed as duplicate of PerfectNumbers.lean:107-109 (verified, Wiedijk #70)."`
- Land PR #18220's documentation contributions (knowledge.md / problem.md /
  state.md) as historical context for future similar slugs, but **drop the
  S2 SCAFFOLD plan**.

### Option B — One-shot wrapper file
- If a separate file is desired for pedagogical reasons or per-OQ
  accounting, create `proofs/Proofs/SumOfDivisorsOQ02.lean` as a **~30-line
  wrapper** that simply re-exports `euler_even_perfect` with an
  OQ-specific theorem name and a docstring linking to OQ-02.
- This is honest, low-cost, and avoids the risk of reformalizing the
  Archive's internal lemmas as parallel proof artifacts.
- Reject any S2 plan that would expose Step-5 or Step-6 lemmas as
  standalone declarations — those are Archive-internal and reformalizing
  them is duplicative, not novel.

### Option C — Pivot to a genuinely fresh follow-up
Rather than re-proving the Euler converse, the agent pool can pivot to
adjacent open questions that are NOT covered by `PerfectNumbers.lean` or
the Mathlib Archive. From the parent slug's "Related Open Problems"
section (`sum-of-divisors.json`), four are explicitly fresh:

| Candidate follow-up | Statement | Status | Mathlib state |
| --- | --- | --- | --- |
| Odd perfect existence | Does there exist an odd `n` with `σ(n) = 2n`? | Open since antiquity; lower bounds (`n > 10^1500`) and structural constraints (≥101 prime factors with multiplicity) are known | No Mathlib formalization of the lower-bound theory |
| Aliquot Catalan-Dickson | For all `n`, does the orbit `n ↦ σ(n) − n ↦ …` terminate or enter a cycle? | Open | Mathlib has `Nat.sigma`; aliquot iteration not formalized |
| Abundancy distribution | What is the asymptotic distribution of `σ(n)/n` on the positive integers? | Partially open; Erdős-style density results | `ArithmeticFunction` infrastructure exists |
| Friendly/solitary | Which `n` are friendly (share abundancy with another `n′`)? | Open (e.g. 10 is conjecturally solitary) | None |

Each of these is at least one full slug of genuine research effort and
disjoint from the existing gallery. Of the four, **odd perfect lower
bounds** is the most directly graspable: state the theorem `∀ n, Odd n →
n.Perfect → 10^1500 < n` as an axiom + survey, then chip away by
formalizing the prime-factor-count obstructions (Steuerwald 1937,
Touchard 1953, Servais 1888). That keeps the work mathematically
ambitious while staying genuinely fresh.

---

## 6. Honesty caveats

1. **Mathlib pin drift.** All constant-name references here are against
   the local file as of commit `6457155f73e` and reflect Mathlib v4.26.0
   conventions. If a maintainer pursues Option B or C, the *first* S3
   step should be a `#check` sweep over the names in §3 to catch
   renames before adding code.

2. **Seeker process critique.** This OQ is the second instance this week
   of a seeker-generated sub-OQ duplicating its already-COMPLETED
   parent slug (see researcher-11 PR #18283 for `infinitude-primes-4k3-oq-01`
   ↔ `dirichlets-theorem`). The pattern suggests the seeker's duplicate-
   detection heuristic should consult `src/data/proofs/<parent-slug>/meta.json`
   `status` and `src/data/research/problems/<parent-slug>.json` `phase`
   before emitting fresh sub-OQs. That meta-improvement is out of scope
   for this audit but worth flagging.

3. **Race-safety of this PR.** PR #18220 writes
   `research/problems/sum-of-divisors-oq-02/{knowledge,problem,state}.md`
   and `src/data/research/problems/sum-of-divisors-oq-02.json`. This PR
   writes only `research/problems/sum-of-divisors-oq-02/sessions/2026-05-12-s2-mathlib-archive-audit.md`.
   Disjoint paths; both can land in either order.

4. **No claim of novelty.** This audit re-confirms a duplication that PR
   #18220's own honesty caveat already anticipated. Its value is
   reducing the next-session decision cost (close vs. wrapper vs. pivot)
   to a checklist, and providing concrete pivot candidates.

---

## 7. Session ledger

- **Mode**: REVISIT (duplicate-detection of a seeker-fresh slug with one
  parallel open PR).
- **Files touched** (diff scope): 1 new file in `research/problems/sum-of-divisors-oq-02/sessions/`.
- **Lean changes**: none.
- **Build status**: N/A (doc-only).
- **Sorry delta**: 0 → 0 (parent `PerfectNumbers.lean` is 0-sorry already).
- **Axiom delta**: 0 → 0.
- **Race-check timestamps**:
  - Pre-claim probe: `gh pr list --search "sum-of-divisors-oq-02"` returned PR #18220 only.
  - Mid-session probe: same (no new PR opened during writing).
  - Claim acquired via `claim sum-of-divisors-oq-02` from `$REPO_ROOT`.

### Knowledge propagation seeds (for future agents)

- `Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect` is the
  canonical name for Euler's converse at Mathlib v4.26.0 — no need to
  re-derive.
- A NEW `SumOfDivisorsOQ02.lean` file rebuilding §2 steps 1-7 as named
  lemmas would *reformalize* the Archive's internal proof skeleton
  without strengthening or generalizing anything; the strict cost-benefit
  is negative.
- Genuinely fresh adjacent OQs in the parent's neighborhood: see §5
  Option C table. Odd-perfect lower bounds is the highest-leverage pivot.

### Recommended next action

Close this OQ as `"status": "graduated"` with a `notes` pointer to
`PerfectNumbers.lean:107-109` and `euler_even_perfect`, then have the
seeker re-emit using the parent-status precheck described in §6.2.
