# Knowledge Base: divisibility-truncation-general-oq-01-oq-01

Open question from the parent gallery entry `divisibility-truncation-general-oq-01`
(Unified Osculator Theorem):

> Can this be extended to divisors that share factors with 10 by combining with
> the last-k-digits framework?

---

## Problem Understanding

The Unified Osculator Theorem proves, for `d` coprime to 10 with osculator `c`
(i.e. `d | 10c - 1`):

    d | n  ↔  d | (n/10 + c·(n%10)).

The coprimality hypothesis is essential: for divisors sharing a factor with 10
(6, 12, 14, 15, 35, ...) there is no osculator, because 10 is not invertible
mod `d`. The classical remedy for the 2- and 5-parts is the **last-k-digits
rule** (4 | n iff 4 | last two digits, 8 | n iff 8 | last three, etc.), already
in the gallery as fixed cases in `DivisibilityRules.lean`.

---

## Resolution (Session 1, 2026-06-15, FRESH → ACT)

**Answer: YES.** Every divisor factors as `d = s · m` with `s = 2^a · 5^b`
(shares all factors with 10) and `m` coprime to 10, and `gcd(s, m) = 1`
automatically. The two frameworks compose via the Chinese Remainder Theorem:

    d | n  ↔  (s | n % 10^k)  ∧  (m | n/10 + c·(n%10)),    s | 10^k,  m | 10c-1.

The left conjunct is the last-k-digits rule; the right is the osculator rule.

### What was built (`proofs/Proofs/DivisibilityTruncationGeneralOQ01OQ01.lean`)

- `dvd_iff_dvd_last_k (s k n) (hs : s ∣ 10^k) : s ∣ n ↔ s ∣ n % 10^k`
  — the last-k-digits rule in **general** form (generalises the gallery's fixed
  4/8/25/125 cases to any divisor of a power of ten). Proof: `Nat.div_add_mod` +
  `Nat.dvd_sub'` / `dvd_add`.
- `combined_divisibility (s m c k n) (hs hcop_sm hmcop hc) :
   s*m ∣ n ↔ (s ∣ n%10^k ∧ (m:ℤ) ∣ (↑(n/10) + c*↑(n%10)))`
  — the main theorem. Proof: rewrite via `DivisibilityRules.coprime_mul_dvd_iff`
  (CRT split), then `and_congr (dvd_iff_dvd_last_k …) (bridge.trans
  (UnifiedOsculator.unified_osculator …))`, where `bridge` is the ℕ→ℤ cast of
  divisibility by `exact_mod_cast`.
- Concrete corollaries: `six_combined` (2·3), `twelve_combined` (4·3, last-two-
  digits part), `fourteen_combined` (2·7, **new**), `thirtyfive_combined`
  (5·7, **new**). Side conditions discharged by `norm_num` and
  `norm_num [Int.isCoprime_iff_gcd_eq_one]`.
- `native_decide` sanity checks (6|144, 14|154, 35|245, 12|1452 + non-divisors).

0 sorries, 0 axioms. Reuses the parent `unified_osculator` and the existing
`coprime_mul_dvd_iff` — no new Mathlib infrastructure needed.

### Verification certificate

`verify_combined_divisibility.py` checks the iff over `n ∈ [0, 200000)` for 9
divisors (6, 12, 14, 15, 35, 18, 28, plus the boundary cases `s=1` pure
osculator d=21 and `m=1` pure last-k-digits d=50). All side conditions and all
equivalences PASS with zero mismatches, confirming the chosen osculators `c` and
digit counts `k` in the Lean corollaries.

### Key insights

- `gcd(s, m) = 1` is automatic once `s = 2^a 5^b` and `m` coprime to 10, so the
  CRT split needs no extra hypothesis beyond `Nat.Coprime s m` (always provable
  numerically per case).
- `k` must be `≥ max(a, b)`; for the 2-part of 12 (= 4) this forces the
  last-*two*-digits rule.
- This subsumes the gallery's ad-hoc composite rules (6, 12, 15, 18, 30), which
  previously only reduced `d | n` to `d₁ | n ∧ d₂ | n` without exposing the
  explicit last-k-digits + osculator computation.

---

## Status

ACT — proof written, 0 sorries / 0 axioms, build-pending (Docker outage at
session time; CI is ground truth). Python certificate PASS. Gallery entry
(`src/data/proofs/divisibility-truncation-general-oq-01-oq-01/`) created.

## Next Steps

- Confirm the Lean file builds in CI (registered in `Proofs.lean`).
- Possible follow-up: minimality of digit operations per divisor, or iterating
  the osculator on the coprime part to bound steps by `log d`.
