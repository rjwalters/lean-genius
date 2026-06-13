# Knowledge Base: divisibility-by-3-oq-01-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

**OQ:** "Extend truncation coverage beyond 19 (23, 29, 31, 37, 41, 43)."

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

---

## Dead Ends

None. The problem is fully tractable by instantiation; there is no missing
Mathlib infrastructure.

---

## Sessions

### Session 2026-06-13 (S1) — ORIENT/ACT

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
