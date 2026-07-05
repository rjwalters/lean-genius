# Knowledge Base: derangements-convergence-oq-04-oq-03

Divisibility & congruence for (generalized r-)derangement numbers.

---

## Problem Understanding

Parent `derangements-convergence-oq-04` proved two SEPARATE facts about
`D(n) = numDerangements n`:

- `(n − 1) ∣ D(n)`  (from the additive recurrence `D(n) = (n−1)(D(n−2)+D(n−1))`)
- `D(n) ≡ (−1)^n (mod n)`  (from the multiplicative recurrence `D(n+1) = (n+1)D(n) − (−1)^n`)

**Note — the child problem statement is internally inconsistent.** It writes both
`(n−1) ∣ D(n)` and `D(n) ≡ (−1)^n (mod n−1)`. But `(n−1) ∣ D(n)` means
`D(n) ≡ 0 (mod n−1)`, so the second would force `(−1)^n ≡ 0 (mod n−1)`, false for
`n > 2`. The correct companion modulus is `n`, not `n−1`.

---

## Insights

### Session 2026-07-04 (Session 2, researcher-14) — FRESH → ACT

**Outcome:** progress (new theorem derived + Lean-drafted, UNVERIFIED under build blackout).

**Main mathematical content.** Because `gcd(n, n−1) = 1`, the two parent facts are
not independent — the Chinese Remainder Theorem fuses them into a single **sharp**
congruence modulo `n(n−1)`:

> **D(n) ≡ (−1)^(n+1)·(n − 1)  (mod n(n−1)).**

This determines `D(n)` modulo `n(n−1)` exactly and is strictly stronger than either
parent fact. Numerically verified for `2 ≤ n ≤ 9`:

| n | D(n) | D(n) mod n(n−1) | (−1)^(n+1)(n−1) mod n(n−1) |
|---|------|-----------------|-----------------------------|
| 4 | 9    | 9               | 9                           |
| 5 | 44   | 4               | 4                           |
| 6 | 265  | 25              | 25                          |
| 7 | 1854 | 6               | 6                           |
| 8 | 14833| 49              | 49                          |
| 9 |133496| 8               | 8                           |

**Structural theorem (`crt_combine`).** The fusion is *combinatorics-free*. It is a
property of the recurrence **shape**, not of derangements:

> If `(n−1) ∣ a` and `n ∣ (a − u)`, then `n(n−1) ∣ (a + u·(n−1))`.

Proof needs no coprimality hypothesis: write `a = (n−1)k`; then `n ∣ (a − u)`
forces `n ∣ (k + u)` (since `(n−1)k ≡ −k mod n`), and multiplying back by `(n−1)`
gives the claim. Holds for every `n`, including degenerate `n = 0, 1`.

**Consequence for the r-derangement ask.** Any r-derangement family `D_r(n)` whose
counting sequence inherits BOTH a `(n−1)`-factor (or `(n+r−1)`-factor) additive
recurrence AND a `±1`-corrected multiplicative recurrence automatically satisfies
the same fused congruence — one only needs the two divisibilities, then `crt_combine`
does the rest. The combinatorial definition is irrelevant to the arithmetic
conclusion.

**Lean (UNVERIFIED draft):** `lean/DerangementsConvergenceOQ04OQ03.lean`
- `crt_combine` — the CRT engine (full proof)
- `sub_one_dvd` — `(n:ℤ−1) ∣ D(n)` over ℤ for all n (self-contained)
- `dvd_numDerangements_sub_sign` — `n ∣ (D(n) − (−1)^n)`
- `numDerangements_combined_dvd` / `numDerangements_combined_congr` — the sharp result
- value sanity checks `D(4)=9, D(5)=44, D(6)=265`

**Why UNVERIFIED:** Docker Lean build image blob corrupted (containerd meta.db EIO),
Aristotle MCP returns 404. File placed under `research/.../lean/` (not globbed by the
lakefile) so it cannot break the gallery build. Promote to `proofs/Proofs/` after a
clean build.

---

## Dead Ends

- Literal combinatorial r-derangements: Mathlib has no definition of permutations
  avoiding a prescribed cycle structure / no cycles of length ≤ r, nor their
  recurrence. Building it (EGF/species) is >500 lines and was not attempted under
  the build blackout. `crt_combine` deliberately routes around this.

---

## Next Steps

1. Machine-check `DerangementsConvergenceOQ04OQ03.lean` once Docker is restored; if
   clean, promote into `proofs/Proofs/` and add a verified gallery entry.
2. Define r-derangements by their recurrence, prove the `(n+r−1)`-factor + sign
   facts, then instantiate `crt_combine` for the literal r-derangement congruence.
3. Determine whether `n(n−1)` is the exact modulus (period) of `D(n)` or whether
   more structure holds mod `n(n−1)(n−2)`.
