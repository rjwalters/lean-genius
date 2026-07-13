# Knowledge Base: divisibility-by-3-oq-01-oq-02

Extend truncation coverage beyond 19 (23, 29, 31, 37, 41, 43).

---

## Problem Understanding

**OQ:** "Extend truncation coverage beyond 19 (23, 29, 31, 37, 41, 43)."

Two complementary framings of the same instantiation problem were developed:

**Framing A — via `DivisibilityTruncationGeneralOQ01` (this entry's file).**
This is a follow-up to `DivisibilityTruncationGeneralOQ01.lean`, which proved
the **Unified Osculator Theorem** and instantiated it for the primes
d = 7, 11, 13, 17, 19. The general theorem already covers every divisor
coprime to 10, so extending coverage to the next primes is pure
instantiation — no new mathematics.

The general results (in namespace `UnifiedOsculator`):
- `unified_osculator d c n (hcop : IsCoprime d 10) (hc : d ∣ 10c - 1)`
  gives `d ∣ n ↔ d ∣ (n/10 + c·(n%10))`  (positive osculator).
- `neg_osculator_from_unified d c n hcop (hc : d ∣ 10c + 1)`
  gives `d ∣ n ↔ d ∣ (n/10 − c·(n%10))`  (negative osculator).

**Framing B — via the parent `DivisibilityTruncationGeneral`.**
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

For each new prime, pick whichever osculator (positive `10c−1` or negative
`10c+1`) gives the smaller constant c. Hand-verified osculator table:

| d  | osculator | c  | identity              |
|----|-----------|----|-----------------------|
| 23 | positive  | 7  | 10·7  − 1 = 69  = 23·3 |
| 29 | positive  | 3  | 10·3  − 1 = 29  = 29·1 |
| 31 | negative  | 3  | 10·3  + 1 = 31  = 31·1 |
| 37 | negative  | 11 | 10·11 + 1 = 111 = 37·3 |
| 41 | negative  | 4  | 10·4  + 1 = 41  = 41·1 |
| 43 | positive  | 13 | 10·13 − 1 = 129 = 43·3 |

Each theorem is a one-line application of the OQ01 general theorems, with the
divisibility witness `⟨k, by norm_num⟩` (k = (10c∓1)/d) and coprimality
`by decide` (same instance OQ01 used for 7..19).

Worked check: 23 ∣ 161 (=23·7). Rule: 161 → 16 + 7·1 = 23, and 23 ∣ 23. ✓

Notes from the Framing-B (parent-file) line of work:
- The OQ list is 23, 29, 31, 37, 41, 43. Of these, **23, 29, 31, 37 were already
  present** in `DivisibilityTruncationGeneral.lean` (`twentythree_dvd_trunc`, …,
  `thirtyseven_dvd_trunc`). Only **41 and 43 were genuinely missing.**
- Osculators added there:
  - **41**: negative osculator `c = 4`, since `10·4 + 1 = 41 = 41·1`
    → `41 ∣ n ↔ 41 ∣ (n/10 − 4·(n%10))`  (`fortyone_dvd_trunc`).
  - **43**: positive osculator `c = 13`, since `10·13 − 1 = 129 = 43·3`
    → `43 ∣ n ↔ 43 ∣ (n/10 + 13·(n%10))`  (`fortythree_dvd_trunc`).
- A bundling theorem `extended_truncation_coverage` collected all six primes
  (23–43) as the explicit answer to this OQ.

---

## Dead Ends

None. The problem is fully tractable by instantiation; there is no missing
Mathlib infrastructure.

---

## Sessions

### Session 2026-06-13 (S1) — ORIENT/ACT (Framing A: OQ01OQ02 new file)

**Mode:** FRESH
**Outcome:** progress (proof drafted; build UNVERIFIED — Docker daemon down)

- Identified that `DivisibilityTruncationGeneralOQ01.unified_osculator` /
  `neg_osculator_from_unified` already subsume all divisors coprime to 10,
  so the OQ reduces to choosing osculator constants for 23,29,31,37,41,43.
- Computed and hand-verified the osculator table above.
- Wrote `proofs/Proofs/DivisibilityTruncationGeneralOQ01OQ02.lean` with six
  instantiation theorems (`twentythree_unified` … `fortythree_unified`),
  six numeric sanity `example`s, and one worked `native_decide` example.
  Registered it in `proofs/Proofs.lean`.
- Could NOT run `lake build` to confirm: Docker daemon is down (build
  blackout, 2026-06-13). The proof mirrors the five OQ01 instances
  (d=7,11,13,17,19) line-for-line, so confidence is high but unverified.

**Next steps:** once Docker is restored, run
`./proofs/scripts/docker-build.sh Proofs.DivisibilityTruncationGeneralOQ01OQ02`
and, if green, promote the candidate `available → completed`.

### Session 2026-06-13 (S1') — ORIENT → ACT (Framing B: parent-file edits)

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
