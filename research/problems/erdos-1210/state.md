# Current State

**Phase**: ACT (S5 COMPLETE — unblocked; harmonic baseline proved + clobbered S3 axiom restored, Docker-verified on Lean v4.31.0)
**Since**: 2026-07-24 (researcher-3)
**Iteration**: 5

## S5 ACT + regression repair (researcher-3, 2026-07-24)

**Two deliverables in one iteration:**

1. **Stale-PR clobber discovered and repaired.** The S3 rewrite (#22965,
   merged 2026-06-13: `primeReciprocalSum` + corrected [Er80] O(1) axiom) was
   **accidentally reverted on 2026-06-30** when the stale sibling PR #22935
   (branched 06-12, before S3 merged) landed its older refutation-only version
   of the file. Until today `main` had NO corrected-form axiom, and meta.json
   read `verified`/`mathlib`/0 axioms — out of sync with this state file's
   S3/S4 description. Restored **append-only** (annotation anchors for the
   first 244 lines preserved modulo a +2 import / header shift, sections
   re-anchored in meta.json): `primeReciprocalSum`, nonneg/pos, `axiom
   erdos_1210` (corrected O(1) form), `primeReciprocalSum_five`,
   `naive_statement_fails_at_five`, `corrected_statement_consistent_at_five`.
   (Dropped only the trivial restatement `erdos_1210_uniform_bound`.)
   NOTE: S4's STATE-SYNC claim that the registry was moved to iter-4/BLOCKED
   was also not on main — the registry sat at iteration 2. Both synced now.

2. **S5 regime-(1) baseline shipped** (the planned build-gated ACT; Docker
   restored): `sum_reciprocal_le_harmonic` — for ANY `A ⊆ [1,n)`,
   `∑_{a∈A} 1/(n-a) ≤ H_{n-1}` via the injective reindex `a ↦ n-a` into
   `Icc 1 (n-1)` (`Finset.sum_image` + `Nat.cast_sub`), then
   `erdos_1210_trivial_upper_bound`: `≤ 1 + log(n-1)` via Mathlib's
   `harmonic_le_one_add_log`. Axiom-free; coprimality displayed but unused
   (documented honestly — that's where the `log → log log` gap lives).

**File**: 244 → 392 lines, 14 → 21 theorems, 4 → 5 defs, 0 → 1 axiom
(the open conjecture), 0 sorries. **meta.json**: status `verified` →
`axiomatized`, badge `mathlib` → `axiom`, axiomCount 1, `assumptions`
populated, sections re-anchored + 2 new sections.

**Remaining blocker (unchanged)**: the conjectured `log log n` RHS asymptotic
needs Mertens' second theorem, absent from Mathlib — long-horizon.

---

# Prior State (2026-06-13, superseded)

**Phase**: BLOCKED (next ACT is build-gated; conjecture is Mathlib-gap-blocked)
**Since**: 2026-06-13T15:00:00Z
**Iteration**: 4

> STATE-SYNC (2026-06-14, researcher-6): the registry
> `src/data/research/problems/erdos-1210.json` trailed this file — its
> `currentState` still read iteration 3 / phase AXIOMATIZED / status active
> with a stale `nextAction` ("do S4", already done), and `leanFiles[]` read
> 179 LOC / 11 thm / 3 def while the file is 230 / 14 / 4. Brought in line
> (iter 4 / BLOCKED, blockers populated, nextAction advanced to the S5
> unconditional-log-n deliverable, counts corrected against gallery
> meta.json + grep) and marked the pool entry blocked. No Lean changes.

## Current Focus

S4 surveyed the achievable-bounds landscape (see knowledge.md Session 4) and
concluded the slug is blocked during the verification blackout. The statement
and formalization on `main` are sound and fully in sync; what remains is
build-gated. See "Blockers" and "Next Action" below.

## Prior Focus (S3)

S3 RESOLVED the S2 blocker. Recovered the correct Erdős statement directly from
erdosproblems.com/1210 (via curl; WebFetch was 403-blocked). The earlier
"unsoundness" was a transcription error, not a flaw in Erdős's conjecture.

## What the source actually says

> Let A ⊆ [1,n) be a set of integers such that (a,b)=1 for all distinct
> a,b ∈ A. Is it true that ∑_{a∈A} 1/(n-a) ≤ ∑_{p<n} 1/p + O(1)?

Two corrections vs. the original Lean transcription:
1. **RHS is ∑_{p<n} 1/p** (prime reciprocals, the Mertens sum ~ log log n),
   NOT ∑_{p<n} 1/(n-p).
2. **There is a +O(1) additive term** — the inequality is asymptotic up to an
   absolute constant, not exact.

The S2 counterexample (n=5, A={4}: LHS=1 > 5/6) does NOT refute the real
conjecture; the 1/6 gap is absorbed by the O(1) constant.

Erdős's own note ([Er80]): he "did not state [this] quite correctly" in
[Er77c]. The [Er80] reformulation concerns primes in an interval: if
n < q₁ < ⋯ < q_k ≤ m are the primes in (n,m], then
∑ 1/(qᵢ-n) < ∑_{p<m-n} 1/p + O(1). See also #460, #950.

## Action taken (S3)

Rewrote `proofs/Proofs/Erdos1210Problem.lean` (Docker-verified, 3058 jobs):
- New def `primeReciprocalSum n = ∑_{p<n} 1/p` (corrected RHS).
- Replaced the unsound exact axiom with the honest O(1) form:
  `axiom erdos_1210 : ∃ C, ∀ n ≥ 3, ∀ pairwise-coprime A ⊆ [1,n),
   ∑ 1/(n-a) ≤ primeReciprocalSum n + C`.
- Kept all verified structural lemmas (primes_coprime, primesBelow_*,
  pairwiseCoprime_at_most_one_even, primeReciprocalSum_nonneg/pos).
- Reframed the n=5 case: `naive_statement_fails_at_five` (the C=0 version is
  false) + `corrected_statement_consistent_at_five` (any C ≥ 1/6 works), proving
  the O(1) term is essential.
- Updated gallery `meta.json` to the corrected statement and counts
  (14 theorems, 4 defs, 1 axiom, 230 lines).

## S4 survey outcome (the two difficulty regimes)

1. **Trivial `log n` baseline (elementary, build-gated).** For any `A ⊆ [1,n)`
   the values `{n−a : a∈A}` are distinct integers in `[1,n−1]`, so
   `∑_{a∈A} 1/(n−a) ≤ H_{n−1} ~ log n` (an injective-image reindex + harmonic
   bound; uses no coprimality). This is the right next ACT deliverable — a
   verified unconditional upper bound instantiating the `C`-free shape with
   `f(n) = H_{n−1}`. Honest partial progress, but NOT the conjecture
   (`log n ≫ log log n`).
2. **The conjecture's `log log n` is Mathlib-gap-blocked.** Closing the
   `log n → log log n` gap is where the coprimality (≤1 element per prime) does
   the work, via a sieve/Mertens comparison. Base Mathlib v4.26.0 lacks Mertens'
   second theorem (`∑_{p<n} 1/p = log log n + O(1)`) — so even *stating* the RHS
   asymptotic requires upstream analytic number theory. Long-horizon.

## Blockers

- **Verification blackout (2026-06-13).** Docker `docker ps` hangs (no build
  route) and the Aristotle backend 404s. The regime-(1) ACT is an
  injective-image reindex — exactly the kind of step that fails silently without
  a compiler, so it must not be blind-shipped (per S4 recommendation).
- **Mathlib gap.** The full `log log n` conjecture needs Mertens' second theorem,
  absent from base Mathlib v4.26.0; a substantial upstream contribution.

The statement itself has no open blocker: `main` is sound and fully in sync
(meta.json ↔ .lean: 14 theorems, 4 defs, 1 axiom, 230 lines; status
`axiomatized`, badge `axiom` — correct for an open conjecture).

## Next Action (when build infra returns)

S5 ACT — ship the regime-(1) trivial `H_{n−1}` unconditional bound (elementary,
no new axioms, Mathlib-reachable). Do NOT attempt the `log log n` conjecture
directly until Mertens' second theorem is available in Mathlib.

## Attempt Counts

- Total attempts: 4
- Approaches tried: 4 (S1 formalization/axiomatization; S2 falsification of the
  mis-transcribed statement; S3 source recovery + corrected re-axiomatization;
  S4 achievable-bounds survey → BLOCKED on build infra + Mathlib gap)
