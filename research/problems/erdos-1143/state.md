# Current State: erdos-1143

**Phase**: OBSERVE
**Path**: full
**Since**: 2026-06-02T00:00:00Z (S1 OBSERVE; was placeholder NEW since 2026-01-15)
**Iteration**: 1 (S1 OBSERVE — file inventory + axiom analysis + forward roadmap, doc-only)

## S1 OBSERVE (researcher-1, 2026-06-02, this PR) — file inventory + 2-axiom analysis + roadmap

**Outcome**: progress — the slug's `state.md` was a 28-line placeholder
("Begin problem exploration"); the actual Lean file
`proofs/Proofs/Erdos1143Problem.lean` is a sophisticated 299-LOC file with
**11 theorems + 3 definitions + 2 axioms + 0 sorries**, fully consistent
with `meta.json` (`status: axiomatized`, `badge: axiom` — correct per
CLAUDE.md policy for Erdős open conjectures). S1 absorbs this drift and
proposes a forward roadmap.

### §1 Mathematical content

Erdős Problem #1143 (https://erdosproblems.com/1143): for primes
`p₁ < p₂ < ··· < pᵤ` and `k ≥ 1`, define `F_k(p₁,...,pᵤ)` as the
**minimum** number of integers in any interval of `k` consecutive
integers divisible by at least one `pᵢ`. Estimate `F_k`, particularly
when `k = αpᵤ` for constant `α > 2`.

By inclusion-exclusion, the expected proportion of integers divisible
by at least one of `p₁,...,pᵤ` is the **expected density**
`density := 1 - ∏ᵢ (1 - 1/pᵢ)`. For `k = αpᵤ` with `α > 2`, the
interval is long enough that multiple complete periods of each prime
fit inside, so `F_k ≈ k · density`. The Erdős–Selfridge exact bound
holds for `2 < α < 3` (paper not located per file header); `α > 3` is
substantially open.

Related: Erdős Problem #970 (Jacobsthal's function).

### §2 Existing Lean file inventory (`proofs/Proofs/Erdos1143Problem.lean`)

299 LOC, `namespace Erdos1143`, `import Mathlib`, `open Finset BigOperators`.

**3 definitions** (lines 39, 44, 49):

| Symbol | Type | Line | Role |
|---|---|---|---|
| `coveredInInterval` | `Finset ℕ → ℕ → ℕ → Finset ℕ` | 39 | filter Ico over divisibility by any `p ∈ primes` |
| `coveringFunction` | `Finset ℕ → ℕ → ℕ` (noncomputable) | 44 | `⨅ a, (coveredInInterval primes a k).card` |
| `expectedDensity` | `Finset ℕ → ℝ` (noncomputable) | 49 | `1 - ∏_{p ∈ primes} (1 - 1/p)` |

**11 theorems** (lines 57, 69, 126, 156 private, 165, 188, 208, 218, 236, 253, 259):

| Symbol | Line | Statement (informal) | Body |
|---|---|---|---|
| `covering_le_k` | 57 | `coveringFunction primes k ≤ k` | trivial (filter ≤ whole interval) |
| `single_prime_lower` | 69 | `coveringFunction {p} k ≥ k/p` (for `Prime p`, `k ≥ 1`) | inject `Finset.range (k/p)` into multiples via `i ↦ (⌈a/p⌉ + i) * p`, ~55 LOC including `Function.Injective` discharge + lo/hi bound calcs |
| `single_prime_upper` | 126 | `coveringFunction {p} k ≤ k/p + 1` | inject divisor `(n ↦ n/p)` into `range (k/p + 1)`, ~25 LOC |
| `prod_one_sub_inv_pos` | 156 (private) | `0 < ∏ (1 - 1/p)` for nonempty primes | `Finset.prod_pos` + per-prime `(p ≥ 2) → (0 < 1 - 1/p)` |
| `expectedDensity_pos` | 165 | `0 < expectedDensity primes` (nonempty primes) | split product as `f(p₀) * ∏(rest)`, bound rest ≤ 1, deduce product < 1 |
| `expectedDensity_lt_one` | 188 | `expectedDensity primes < 1` (nonempty primes) | `linarith [prod_one_sub_inv_pos]` |
| `erdos_selfridge_exact` | 208 | `2 < α < 3 → ∃ exact_val : ℕ, F_k = exact_val` | **trivially true** — the comment notes "mathematical content is the *formula* for `exact_val`, not its existence" |
| `covering_lower_bound` | 218 | `k * (density - 1) ≤ F_k` | trivially true since `density < 1 ⟹ LHS ≤ 0 ≤ F_k` |
| `alpha_gt_3_open` | 236 | for `α > 3`, `k * (density - 1) ≤ F_k ≤ k * density + |primes|` | combines `covering_lower_bound` + `covering_upper_bound` axiom |
| `density_two_three` | 253 | `expectedDensity {2,3} = 2/3` | `norm_num` |
| `density_two_three_five` | 259 | `expectedDensity {2,3,5} = ...` | `norm_num` |

**2 axioms** (lines 196, 230, both correctly Erdős-axiomatized per CLAUDE.md):

#### Axiom A1: `covering_asymptotic` (line 196)

```lean
axiom covering_asymptotic (primes : Finset ℕ)
    (hprime : ∀ p ∈ primes, Nat.Prime p) :
    ∃ C : ℝ, C > 0 ∧ ∀ k : ℕ, k ≥ 1 →
    |(coveringFunction primes k : ℝ) - k * expectedDensity primes| ≤ C
```

The asymptotic "main term" claim: `F_k = k · density + O(1)` with the
implicit constant depending only on the primes (not on `k`). This is
the **strong form** of the Erdős–Selfridge estimate. Not directly proven
from `covering_upper_bound` because A2 only gives one-sided control;
need a matching lower bound (other than the trivial `k * (density - 1)`).

#### Axiom A2: `covering_upper_bound` (line 230)

```lean
axiom covering_upper_bound (primes : Finset ℕ)
    (hprime : ∀ p ∈ primes, Nat.Prime p)
    (hne : primes.Nonempty) (k : ℕ) :
    (coveringFunction primes k : ℝ) ≤ k * expectedDensity primes + primes.card
```

The "periodicity averaging" claim: the infimum of `covered(a, k)` over
`a ∈ ℕ` is at most the average over one period `P = ∏ primes`, with
correction term bounded by `|primes|` from inclusion-exclusion residual.
**Tractable** via:

1. Take `P := ∏ p ∈ primes, p` (period).
2. Show `(1/P) * ∑_{a ∈ Finset.range P} (covered primes a k).card =
   k · density + ε(primes, k)` where `|ε| ≤ |primes|` from
   inclusion-exclusion boundary terms.
3. The infimum is ≤ average, so the bound follows.

### §3 The 3 ACT lanes (deferred to S2+)

#### Lane A: Discharge `covering_upper_bound` (A2) via periodicity averaging

**Strategy**: ~80-120 LOC. The key Mathlib bearers (to spot-check at
Mathlib pin `2df2f0150c…` in S2):

- `Finset.sum_Ico_consecutive` for the periodicity decomposition.
- `Nat.Prime.coprime_iff_not_dvd` for the coprimality chain underlying
  the inclusion-exclusion error term.
- `Nat.totient_prime` (∏ primes = P, totient(P) = ∏(p-1)) for relating
  the average `∑ covered/P` to `k · (1 - ∏(1 - 1/p)) = k · density`.
- `Finset.inf'_le` + standard ciInf bounds.

**Caveat**: the error term `≤ |primes|` is loose; the tight constant
is `∏ (1 - 1/p) ≤ 1` ≪ `|primes|`. Loose form keeps the proof
simpler.

#### Lane B: Discharge `covering_asymptotic` (A1) from A2 + matching lower bound

**Strategy**: after Lane A, derive A1 by combining A2's upper bound
`F_k ≤ k · density + |primes|` with a matching lower bound
`F_k ≥ k · density - |primes|` (analogous periodicity averaging on the
*supremum* of the *complement* count). Set `C := |primes|`.

**LOC**: ~60-80 LOC on top of Lane A.

#### Lane C: Tighten `erdos_selfridge_exact` (currently a tautology) to a real Erdős–Selfridge formula

**Blocker**: Erdős–Selfridge paper not located. Per the file header:
"Erdős and Selfridge found the exact bound for 2 < α < 3 (paper not
located)". S2+ needs literature search (likely Erdős & Selfridge 1968
"On a combinatorial problem of Schur"; Va99 = Vasilenko 1999
*Number Theory Lectures*, Problem 1.8 cited in the file header).

**Risk**: the "exact bound" may not have a tractable closed form
expressible in Lean — could be a recurrence or piecewise formula
indexed on residue patterns. **Defer** to a literature-confirmed S3+
iteration.

### §4 Recommended S2 picker path

**S2 ACT**: Lane A (`covering_upper_bound` discharge). Highest-value /
lowest-risk: tightens the file from `axiomCount: 2` to
`axiomCount: 1` (still `axiomatized`, since A1 remains open). Lane B
(`covering_asymptotic` discharge) follows naturally as **S3**.
Lane C is **S4+ (literature-blocked)**.

**Forward outlook**:

| Iteration | Target | LOC | Risk |
|---|---|---|---|
| S2 ACT | Lane A: discharge `covering_upper_bound` via periodicity averaging | ~80-120 | medium (Mathlib bearer survey needed) |
| S3 ACT | Lane B: discharge `covering_asymptotic` from Lane A | ~60-80 | low (incremental on S2) |
| S4+ | Lane C: literature search + Erdős–Selfridge `2 < α < 3` formula | unknown | high (literature-blocked) |
| S5+ | OQ-spinoff: Jacobsthal connection (Erdős #970) | n/a (new slug) | exploratory |

### §5 What S1 OBSERVE did **not** do (explicit)

1. **No Lean file edits.** Slug remains at 299 LOC / 11 thm / 3 defs /
   2 axioms / 0 sorries / `axiomatized`. Lane A discharge deferred to S2.
2. **No `meta.json` edits.** Counts already accurate.
3. **No `knowledge.md` creation.** Will be drafted in S2 ACT.
4. **No bearer SHA-pin verification.** Deferred to S2 PREP / ACT cycle
   when the Lane A Mathlib bearer list is finalized.
5. **No JSON tracker update.** State `currentState.phase: NEW` may not
   exist in the research JSON for this slug (Erdős slug, never claimed
   before); S2 will create/update the JSON.
6. **No Docker BUILD-VERIFY.** Sibling container `lean-build-57602`
   (image `9026c55995f4`, `lean4-arm64:v4.26.0`) up 5+ hours; build
   deferred per [[project-researcher-1-2026-06-02-s13-act-clt-gaussian-in-own-doa]].

### §6 References

- File: `proofs/Proofs/Erdos1143Problem.lean` (299 LOC, 11 thm + 3 defs + 2 axioms).
- meta.json: `src/data/proofs/erdos-1143/meta.json` (`status: axiomatized`, `badge: axiom`, counts match exactly).
- Source: https://erdosproblems.com/1143 (per file header).
- Related: Erdős Problem #970 (Jacobsthal's function).
- Citations: Erdős & Selfridge for `2 < α < 3` (paper not located);
  Vasilenko 1999 Number Theory Lectures, Problem 1.8 (per file header).
- Mathlib pin: `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (unchanged
  since 2026-05-13, 21 days).
