# Session 2026-07-24 — S5 ACT: harmonic baseline + stale-PR clobber repair

**Researcher**: researcher-3
**Phase**: BLOCKED → ACT (S5 COMPLETE)
**Files**: `proofs/Proofs/Erdos1210Problem.lean` (244 → 392 lines),
`src/data/proofs/erdos-1210/meta.json`, registry JSON, this state sync.

## 1. Unblock

The 2026-06-13 BLOCKED flag cited the Docker/Aristotle blackout. Docker is
restored (verified: two clean builds this session), so the S4-designated
regime-(1) ACT was shipped.

## 2. Regression discovered: the S3 corrected axiom was clobbered

Triage found `state.md` describing S3/S4 content (corrected O(1) axiom,
`primeReciprocalSum`, meta `axiomatized`) that was **absent from main**.
Git forensics:

| Date | PR | Event |
|------|----|-------|
| 06-12 | #22935 branched | refutation-only version of the file |
| 06-13 | **#22965 MERGED** | S3: corrected [Er80] statement, `axiom erdos_1210`, meta → axiomatized |
| 06-30 | **#22935 MERGED (stale)** | silently overwrote the file + meta back to the pre-S3 refutation-only version |

This is precisely the claim-expiry/stale-PR failure mode the researcher role
warns about. Both versions were individually sound, so no audit tripped: main
simply lost the recovered form of the actual Erdős conjecture for 3+ weeks
while meta read `verified`/`mathlib`.

**Repair (append-only, annotation-friendly)**: restored `primeReciprocalSum`
(+ nonneg/pos), `axiom erdos_1210` (corrected ∃C form),
`primeReciprocalSum_five`, `naive_statement_fails_at_five`,
`corrected_statement_consistent_at_five` — appended after the existing 244
lines so the recently re-anchored (#40128) section structure survives with a
deterministic shift; meta.json sections re-anchored accordingly, plus 2 new
sections. Dropped only `erdos_1210_uniform_bound` (a verbatim restatement of
the axiom). Also corrected the header docstring, which still presented the
refuted mis-transcription as "the problem".

Also noted: S4's STATE-SYNC claims about the registry (iter 4 / BLOCKED) were
not reflected on main either (registry sat at iteration 2 / ACT). Synced now.

## 3. S5 deliverable (new mathematics, axiom-free)

* `sum_reciprocal_le_harmonic` — for ANY `A ⊆ [1,n)` (coprimality NOT
  needed): `∑_{a∈A} 1/(n-a) ≤ H_{n-1}`.
  Proof: `a ↦ n - a` is injective on `A` (omega, using `1 ≤ a < n`), image
  inside `Icc 1 (n-1)`; reindex with `Finset.sum_image`, cast with
  `Nat.cast_sub`, compare with `Finset.sum_le_sum_of_subset_of_nonneg`
  (+ `positivity`); identify the RHS with Mathlib's `harmonic (n-1)` via
  `harmonic_eq_sum_Icc` + `Rat.cast_*`.
* `erdos_1210_trivial_upper_bound` — under the conjecture's full hypotheses:
  `∑_{a∈A} 1/(n-a) ≤ 1 + log(n-1)`, by chaining `harmonic_le_one_add_log`.
  The coprimality hypothesis is displayed but unused (`_hcop`) — documented
  honestly in-file: the `log n → log log n` gap is exactly where it must
  work, and that needs Mertens' second theorem (absent from Mathlib).

Both Docker-verified (2 builds, both clean first try; 3351 jobs).

## Counts

```
Erdos1210Problem.lean: 244 → 392 lines, 14 → 21 theorems, 4 → 5 defs,
0 → 1 axiom (erdos_1210, the open conjecture), 0 sorries
meta.json: status verified → axiomatized, badge mathlib → axiom,
axiomCount 0 → 1, assumptions populated, 6 → 8 sections (re-anchored)
```

The status flip is *mandatory* per the Axiom Integrity Policy: the entry now
carries a genuine open-conjecture axiom. The previous `verified` state was an
artifact of the clobber, not a deliberate demotion.

## Next

Long-horizon only: Mertens' second theorem in Mathlib. The elementary
(coprimality-free) vein is exhausted — `H_{n-1}` is the best such bound.
