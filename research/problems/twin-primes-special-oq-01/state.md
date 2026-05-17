# Research State: twin-primes-special-oq-01

## Current State
**Phase**: COMPLETED (axiomatized)
**Path**: full
**Since**: 2026-05-16
**Iteration**: 3

## Current Focus

S3 STATE-SYNC (2026-05-17 researcher-12): correct the lineCount convention
that S2 (2026-05-16) reversed. S2 changed `leanFiles[0].lineCount` 151→150
to match a then-stale `meta.json`; canonical is the other way around per
`enrich-research.ts` (`content.split('\n').length`, not `wc -l`). This S3
fixes both `meta.json` (150→151 in `meta.lineCount` and `leanFile.lineCount`)
and `research/.../JSON` (`leanFiles[0].lineCount` 150→151). Pool also
re-flipped `available` → `completed`.

**Disk reality**: `proofs/Proofs/TwinPrimesSpecialOQ01.lean` exists (151 LOC
per `split('\n').length`, 150 newlines, ends with trailing `\n`; 25
theorems via `decide` + conditional consequences, 0 standalone axioms,
0 sorries, inherits `twin_prime_conjecture` from parent `TwinPrimes.lean`).
Gallery entry `src/data/proofs/twin-primes-special-oq-01/{meta.json,annotations.json,index.ts}`
exists with `status: "axiomatized"`, `badge: "axiom"`.

## Active Approach

Completed. The S1 port plan was executed mechanically as documented:

- Mirrored `proofs/Proofs/SophieGermainOQ01.lean` structure
- 4 equivalent formulations of `TwinPrimeConjecture`
- 25 verified twin prime pairs via `decide` (19 new beyond parent's 6)
- 3 conditional consequences under TPC axiom: primes ≡ 5 (mod 6) infinite, no-finite-cover, no-max
- No additional standalone axioms (inherits parent's `twin_prime_conjecture`)

## Blockers

None mathematical. **Standing host INFRA RED** (disk 2.5 Gi, Docker hung, `proofs/.lake` self-symlink) applies only to *optional follow-up iterations*, not to anything required by this slug — the slug is COMPLETED.

## Next Action

Slug is COMPLETED axiomatized. Optional follow-up iterations:

1. **Maynard-Tao bounded-gaps axiom**: add `axiom bounded_gaps_246 : ∀ N, ∃ p > N, ∃ k ≤ 246, IsPrimePair p k` as a strengthened companion result (unconditional, by Zhang/Maynard/Polymath8). Would add ~30-50 LOC and 0 new mathematical assumptions.
2. **Strong converse alternatives**: cross-reference to `bounded-prime-gaps-*` family for the post-Zhang state-of-the-art.
3. **Annotation enrichment**: hand off to `/lean-research` enricher agent (separate pipeline) for richer gallery prose.

None of these are scheduled. The slug stands as-is.

## History

- 2026-04-23: Problem created (gallery-gap, seeker batch #11863)
- 2026-04-27 (S1): Survey complete; port plan documented; no code change (no build access)
- 2026-05-02 (out-of-band): PR #14871 implemented the port plan — Lean file 150 newlines (151 LOC split) + gallery entry created
- 2026-05-16 (S2): STATE-SYNC catchup — state.md/JSON aligned with then-stale gallery; **leanFiles[0].lineCount erroneously rolled 151→150** to match a wc-l-style meta.json
- 2026-05-17 (S3): STATE-SYNC re-reconciliation — restore canonical `split('\n').length` convention: meta.json 150→151, registry leanFiles[0].lineCount 150→151, pool re-flipped `available` → `completed`

## Attempt Count

- Total attempts: 3
- Current approach attempts: 1 (port-from-SG-OQ-01 strategy)
- Approaches tried: 1
