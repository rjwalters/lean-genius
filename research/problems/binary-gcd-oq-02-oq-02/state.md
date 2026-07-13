# Current State

**Phase**: COMPLETED
**Since**: 2026-05-12T12:20:43Z
**Iteration**: 2

## Current Focus

Slug is **COMPLETED**. Lean realization of Lehmer GCD for `ℤ` shipped in
S1 (PR #18083, merged 2026-05-12T12:00 UTC) and the corresponding
gallery entry shipped in S2 (PR #18095, merged 2026-05-12T12:20 UTC).
Build verified end-to-end (S1 PR title carried "build verified"); zero
sorries, zero axioms.

This STATE-SYNC consolidates the canonical-vs-flat-path divergence
inherited from the S1 SCAFFOLD: the original session log was written to
the misplaced flat directory `research/binary-gcd-oq-02-oq-02/` (no
`problems/` segment) while the canonical
`research/problems/binary-gcd-oq-02-oq-02/state.md` remained at the
seeker-init stub. JSON tracker
(`src/data/research/problems/binary-gcd-oq-02-oq-02.json`) correctly
reflects `phase: COMPLETED` / `status: completed` since 2026-05-12.

Pattern documented in memory as the "canonical vs flat
`research/problems/<slug>/`" trap. The misplaced flat directory at
`research/binary-gcd-oq-02-oq-02/` (no `problems/` prefix) contains the
S1-era session content — preserved for archival but not aggregated into
gallery listings.

## Deliverables (S1 + S2)

### S1 (PR #18083, researcher-10, 2026-05-12) — Lehmer GCD on `ℤ`

* `proofs/Proofs/BinaryGcdOQ02OQ02.lean` (~155 LOC, 0 sorries, 0 axioms)
* Header definition: `def lehmerGcdInt (a b : ℤ) : ℕ := lehmerGcd a.natAbs b.natAbs`
* Headline correctness:
  `theorem lehmerGcdInt_eq_intGcd : lehmerGcdInt a b = Int.gcd a b`
* Supporting properties (mechanical, all ≤ 5 LOC each):
  - sign invariance: `lehmerGcdInt (-a) b = lehmerGcdInt a b`
  - commutativity: `lehmerGcdInt a b = lehmerGcdInt b a`
  - self-application: `lehmerGcdInt a a = a.natAbs`
  - zero cases: `lehmerGcdInt 0 b = b.natAbs`, `lehmerGcdInt a 0 = a.natAbs`
  - universal property via `Int.gcd_dvd_left`/`right` composition
  - agreement on natural absolute values
* Proof strategy: reduce ℤ to ℕ via `natAbs`, invoke the existing ℕ
  correctness theorem (`LehmerGcdOQ01.lehmerGcd_correct`), and inherit
  `Int.gcd`-correctness mechanically since `Int.gcd` is itself defined
  as `natAbs.gcd natAbs`. This is the **Lehmer analogue** of
  `BinaryGcdOQ02.binaryGcdInt`; the file is a thin sibling.
* Build verified clean on origin/main; PR title carried "build verified".

### S2 (PR #18095, researcher-?, 2026-05-12) — Gallery entry

* `src/data/proofs/binary-gcd-oq-02-oq-02/meta.json` — sibling of
  `binary-gcd-oq-02` gallery entry (same proof shape, same theorem
  inventory).
* annotations.json, index.ts as per standard gallery scaffold.
* `status: verified` / `badge: original` (or equivalent) since 0
  sorries, 0 axioms.

## Active Approach

None — slug is at terminal COMPLETED status. No active work threads.

## Blockers

None.

## Next Action

* **No further research-scope work expected.** The Lehmer-GCD-on-ℤ
  theorem is established and gallery-integrated.
* **Optional sibling extensions** (out of `oq-02-oq-02` scope, would
  require a new slug):
  - Prove `lehmerGcdInt a b = BinaryGcdOQ02.binaryGcdInt a b`
    transitively via `Int.gcd` (would require breaking the current "no
    cyclic imports" tree by importing both `BinaryGcdOQ02` and
    `BinaryGcdOQ03OQ01` in a new sibling file).
  - Extend to `GaussianInt` / `ℤ[i]`.
* **Optional gallery enrichment** (mechanic/enricher scope): cross-link
  to `binary-gcd-oq-02` and `binary-gcd-oq-02-oq-01` (binary GCD via
  testBit/shiftRight) for the gallery's GCD-algorithm family thread.

## Attempt Counts

- Total attempts: 2
- Current approach attempts: 0 (terminal)
- Approaches tried: 1 (natAbs reduction; succeeded)

## References

* `proofs/Proofs/BinaryGcdOQ02OQ02.lean` — implementation
* `src/data/proofs/binary-gcd-oq-02-oq-02/` — gallery entry
* `research/binary-gcd-oq-02-oq-02/` (misplaced flat) — S1 session log
  (preserved for archival; not aggregated into gallery listings)
* PR #18083 — S1 SCAFFOLD (researcher-10, build verified)
* PR #18095 — S2 gallery (verified Lehmer GCD on ℤ entry)
