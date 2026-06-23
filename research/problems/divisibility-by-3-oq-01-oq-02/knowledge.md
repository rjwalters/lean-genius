# Knowledge Base: divisibility-by-3-oq-01-oq-02

Extend truncation coverage beyond 19 (23, 29, 31, 37, 41, 43).

---

## Problem Understanding

The parent entry `divisibility-truncation-general` (file
`proofs/Proofs/DivisibilityTruncationGeneral.lean`) proves two **parametric**
osculator theorems that subsume every base-10 truncation divisibility test:

- `truncation_pos d c n` : for `d` coprime to 10 with positive osculator `c`
  (`d ∣ 10c − 1`), `d ∣ n ↔ d ∣ (n/10 + c·(n%10))`.
- `truncation_neg d c n` : for `d` coprime to 10 with negative osculator `c`
  (`d ∣ 10c + 1`), `d ∣ n ↔ d ∣ (n/10 − c·(n%10))`.

The osculator `c` is just `10⁻¹ mod d` (positive case) or `d − 10⁻¹` (negative
case); it always exists because `gcd(d, 10) = 1`. So "extending coverage" to a new
prime is purely a matter of supplying its osculator constant — **no new machinery**.

---

## Insights

- The OQ list is 23, 29, 31, 37, 41, 43. Of these, **23, 29, 31, 37 were already
  present** in `DivisibilityTruncationGeneral.lean` (`twentythree_dvd_trunc`, …,
  `thirtyseven_dvd_trunc`). Only **41 and 43 were genuinely missing.**
- Osculators computed and added:
  - **41**: negative osculator `c = 4`, since `10·4 + 1 = 41 = 41·1`
    → `41 ∣ n ↔ 41 ∣ (n/10 − 4·(n%10))`  (`fortyone_dvd_trunc`).
  - **43**: positive osculator `c = 13`, since `10·13 − 1 = 129 = 43·3`
    → `43 ∣ n ↔ 43 ∣ (n/10 + 13·(n%10))`  (`fortythree_dvd_trunc`).
- Added a bundling theorem `extended_truncation_coverage` collecting all six
  primes (23–43) as the explicit answer to this OQ.
- Coprimality discharged by `by decide` and the osculator witness by `⟨k, by norm_num⟩`,
  exactly mirroring the four existing 23/29/31/37 instances — so the new code is
  structurally identical to already-merged, building code.

## Dead Ends

- None. This OQ is fully tractable: it is an instantiation of an existing general
  theorem, not new mathematics.

---

## Session Log

### Session 2026-06-13 (S1) — ORIENT → ACT

**Mode**: FRESH
**Outcome**: progress (proof code written; build-unverified — Docker daemon down)

**What I did**
- Surveyed the parent truncation framework; found 23/29/31/37 already covered.
- Computed osculators for the two missing primes (41 neg c=4, 43 pos c=13) and
  added `fortyone_dvd_trunc`, `fortythree_dvd_trunc`, two osculator-table examples,
  and an `extended_truncation_coverage` bundling theorem.

**Files modified**
- `proofs/Proofs/DivisibilityTruncationGeneral.lean`

**Build status**
- NOT verified locally: Docker daemon is down (verification blackout 2026-06-13).
  The additions are textually identical in structure to the adjacent merged
  23/29/31/37 instances, so confidence is high, but the deployer's Docker build
  must confirm before this OQ is marked `completed`.

**Next steps**
- After Docker is restored: `./proofs/scripts/docker-build.sh Proofs.DivisibilityTruncationGeneral`.
  If green, flip candidate status available → completed and (optionally) generate a
  follow-up OQ on whether `c` can be produced uniformly via a decidable osculator function.
