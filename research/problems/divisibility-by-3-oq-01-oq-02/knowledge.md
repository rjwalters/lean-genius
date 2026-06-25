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

### Session 2026-06-25 (S2) — VERIFY (math) + follow-up scoped

**Mode**: REVISIT (S1 work already merged via PR #23115)
**Outcome**: no new code (verification blackout); independent math check + ready-to-formalize follow-up

**What I did**
- Confirmed S1's additions are present and merged on `main`
  (`fortyone_dvd_trunc`, `fortythree_dvd_trunc`, `extended_truncation_coverage`;
  file is 284 lines, 18 theorems, **0 axioms, 0 sorries**).
- **Independently re-checked the two new osculators by hand:**
  - 41 (negative): `10·4 + 1 = 41 = 41·1` ✓ → `41 ∣ n ↔ 41 ∣ (n/10 − 4·(n%10))`.
  - 43 (positive): `10·13 − 1 = 129 = 43·3` ✓ → `43 ∣ n ↔ 43 ∣ (n/10 + 13·(n%10))`.
  Both are correct; the new theorems are structurally identical to the merged
  23/29/31/37 instances. The OQ ("extend coverage to 23,29,31,37,41,43") is
  **mathematically solved**; only the canonical Docker build remains to bless it.

**Build status**
- Still NOT verifiable locally this session: Docker daemon down, no local Mathlib
  oleans, host disk at 99% (≈13Gi free — fetching the olean cache is unsafe), and
  the Aristotle MCP endpoint returned `Resource not found` (service unavailable).
  Deliberately did **not** append unverified Lean to the already-merged working
  file: a single typo would fail the whole-project build and could jeopardize S1's
  merged content with no way to check. Left for the deployer's Docker build.

**Follow-up worked out (ready to formalize next session, needs no new machinery):**
*Osculator duality* — the positive and negative truncation rules are NOT independent.
If `c` is a positive osculator for `d` (`d ∣ 10c − 1`), then `d − c` is a negative
osculator (`d ∣ 10(d−c) + 1`), and conversely. Proof is pure `dvd` arithmetic:
`10(d−c) + 1 = 10d − (10c − 1)`, and `d ∣ 10d` with `d ∣ (10c − 1)` give the result
via `dvd_sub`. Consequence: `truncation_neg` is derivable from `truncation_pos`
(and vice versa), so the framework needs only one general theorem. Candidate
statements (verify once a build path returns):
```lean
theorem neg_osculator_of_pos (d : ℕ) (c : ℤ) (hc : (d:ℤ) ∣ 10*c - 1) :
    (d:ℤ) ∣ 10*((d:ℤ) - c) + 1 := by
  have hkey : (10:ℤ)*((d:ℤ) - c) + 1 = 10*(d:ℤ) - (10*c - 1) := by ring
  rw [hkey]; exact Int.dvd_sub (dvd_mul_left (d:ℤ) 10) hc
theorem pos_osculator_of_neg (d : ℕ) (c : ℤ) (hc : (d:ℤ) ∣ 10*c + 1) :
    (d:ℤ) ∣ 10*((d:ℤ) - c) - 1 := by
  have hkey : (10:ℤ)*((d:ℤ) - c) - 1 = 10*(d:ℤ) - (10*c + 1) := by ring
  rw [hkey]; exact Int.dvd_sub (dvd_mul_left (d:ℤ) 10) hc
```
This is theory-level (a structural duality between the two rule forms), not a
shallow per-prime extension, so it is a legitimate follow-up rather than a cosmetic
variant. Adding *more primes* (47, 49, …) is explicitly NOT worth doing — pure
repetition of the existing pattern.

**Next steps (unchanged + refined)**
- When any build path returns (Docker up, or Aristotle MCP reachable, or local
  cache safe to fetch): build the merged file to bless this OQ, then add the two
  duality theorems above and re-verify.
