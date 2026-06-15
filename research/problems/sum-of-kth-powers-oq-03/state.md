# Research State: sum-of-kth-powers-oq-03

## Current State
**Phase**: ORIENT
**Path**: full
**Since**: 2026-06-14T20:00:16-07:00
**Iteration**: 4

## Current Focus
OQ resolved on paper (odd-number partition of cubes). Formalizable core pinned to existing
Mathlib lemmas with a milestone split. M1 spec **re-verified exactly in ℕ semantics** (S2,
researcher-4): L1/L2/L3/Main all hold for n,i ≤ 40, and the `i=0` block under ℕ-truncated `i-1`
is empty (=0³), so `Main` over `range (n+1)` needs no `i=0` special case — no hidden off-by-one.
**S3 (researcher-1):** that verification is now **durable + reproducible** — committed as
`verify_m1.py` (sympy symbolic + brute force n=0..60, exits non-zero on mismatch) — and the M1
spec sharpened to a **ℕ-subtraction-free reindex** (block `i∈range n` ↦ cube `(i+1)³` on
`[T i, T(i+1))`, no `i-1`, no `i≥1` side condition).
**S4 (researcher-5):** closed the last documented hazard — the `/2` division-clearing in L2′.
`verify_m1.py` now certifies the **division-free** ring identities (multiply through by 4 using
`2·T k = k(k+1)`): `((i-1)i)² + 4i³ = (i(i+1))²` and the reindex form
`(i(i+1))² + 4(i+1)³ = ((i+1)(i+2))²`, plus that the ℕ-division is **exact**
(`2·(k(k+1)//2)=k(k+1)`, `k(k+1)` even = `Nat.even_mul_succ_self`). The Lean ring steps can now
avoid `/2` entirely. Spec fully de-hazarded; ready to ACT (transcription only) once backends return.

## Active Approach
Telescoping odd-partition: i³ = T_i² − T_{i−1}², then `Finset.sum_Ico_consecutive` tiles the
odd-position ranges and `sum_odds (m) = m²` closes it to T_n² = (∑ i)². See knowledge.md
"Formalizable core" (L1–L3 + Main, M1 milestone).

## Attempt Count
- Total attempts: 0 (no build possible — backend blackout)
- Current approach attempts: 0
- Approaches tried: 0

## Blockers
- Verification blackout: Docker down (`docker info` timeout) AND Aristotle "Resource not found".
  No Lean can be built/checked this session. M1 is spec-complete and Docker-gated only.

## Next Action
When Docker returns: create `proofs/Proofs/SumOfKthPowersOQ03.lean`, type M1 using the
**ℕ-sub-free reindex** in knowledge.md ("ℕ-subtraction-free reindex"): L1 `sum_odds`, L2′
`block_eq_cube` (`∑ Ico (T i) (T (i+1)) (2j+1) = (i+1)³` via `Finset.sum_Ico_consecutive` +
the **division-free** ring identity `(i(i+1))²+4(i+1)³=((i+1)(i+2))²`, clearing `/2` by
`2*T k = k*(k+1)` with `Nat.even_mul_succ_self`), L3′ tiling, Main′,
then index-shift to the parent's RHS shape. Build via
`./proofs/scripts/docker-build.sh Proofs.SumOfKthPowersOQ03`; cross-check arithmetic against
`verify_m1.py` if any ring step misbehaves. Then add the gallery entry under
`src/data/proofs/sum-of-kth-powers-oq-03/`.
