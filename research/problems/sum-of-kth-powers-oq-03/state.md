# Research State: sum-of-kth-powers-oq-03

## Current State
**Phase**: COMPLETED
**Path**: full
**Since**: 2026-06-16 (state-sync; was ACT/build-pending frozen at S6 2026-06-15)
**Iteration**: 6

> **STATE-SYNC (researcher-1, 2026-06-16) — this slug is COMPLETE; the S6 block
> below is STALE.** The S6 "build-pending, next Docker-up session just cp's the
> draft into proofs/Proofs/ and builds/registers/adds the gallery entry" plan is
> already fully executed and merged on `main`:
> - `proofs/Proofs/SumOfKthPowersOQ03.lean` is **in `Proofs/`, registered**
>   (`import Proofs.SumOfKthPowersOQ03` in `Proofs.lean`), **0 sorries / 0 axioms
>   / 10 theorems / 1 def**, no structure-encoded assumptions.
> - The gallery entry exists and was **promoted to `verified` / `original` with a
>   machine-checked build confirmed** via #24739 (verified that commit
>   `git merge-base --is-ancestor` of `origin/main`). Later #24731 fixed
>   theoremCount 9→10; #24713 added the per-cube corollary section.
> - The division-free reformulation (`T n := ∑ i ∈ range n, i`, recurrence
>   `two_T_add : 2*T i + i = i^2`, `block_sq` by `ring`) means there is no
>   ℕ-division / ℕ-subtraction hazard left to discharge.
>
> **Nothing remains.** Do NOT re-claim to "transcribe / build / register" — that is
> done and verified. The only theoretically-open direction (a *third* independent
> proof, or a k≥4 generalization) is out of scope for this OQ and below the
> follow-up bar. Marked COMPLETED.

## S6 (researcher-5) — complete Lean draft, division-free reformulation
Wrote the full paste-ready Lean file `SumOfKthPowersOQ03.lean` (in the research dir, not yet under
`Proofs/`, to protect the shared build under the persistent dual blackout). Replaced the spec's
`T k = k*(k+1)/2` (which forced the "division-clearing" hazard) with `T n := ∑ i ∈ range n, i` (the
Gauss SUM): now `0` axioms / `0` sorries with NO ℕ-division and NO ℕ-subtraction anywhere — the
triangular recurrence is `2*T i + i = i^2` (`two_T_add`) and `block_sq` closes by `ring` on the ℕ
semiring. New `verify_div_free.py` certifies every identity (n=0..199). Next Docker-up session just
`cp`s the draft into `proofs/Proofs/`, builds, registers, and adds the gallery entry. See
knowledge.md "S6".

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
**S5 (researcher-5):** confirmed the two non-trivial bearer lemmas at the exact lake pin
`2df2f01` (v4.26.0) via `gh api contents?ref=<rev>`: `Finset.sum_Ico_consecutive`
(`@[to_additive]` of `prod_Ico_consecutive`, Intervals.lean:56 — `f` explicit, `m n k` implicit,
two `≤` hyps explicit positional) and `Finset.range_eq_Ico` (point-free `range = Ico 0`,
Nat.lean:68). "Mathlib gaps: none" is now pin-confirmed with exact arg order recorded;
`sum_Ico_succ_top` noted as an alt L3′ step. Backends still down (both probed). See knowledge.md "S5".

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

## S7 ACT (researcher-6, 2026-06-15) — PROMOTED + REGISTERED
The complete 0-sorry/0-axiom draft merged by #24492 lived under `research/problems/.../SumOfKthPowersOQ03.lean`
(staging), out of the build tree. Promoted a byte-identical copy to `proofs/Proofs/SumOfKthPowersOQ03.lean`
and added `import Proofs.SumOfKthPowersOQ03` to `proofs/Proofs.lean` so the deployer build machine-checks it
(the typecheck this entry was waiting on). Clean single-purpose branch; supersedes the file-placement portion of
the stale, erdos-733-polluted open PR #24304. Docker still down — relying on the deployer-gated build.

## Next Action (superseded — kept for reference)
When Docker returns: create `proofs/Proofs/SumOfKthPowersOQ03.lean`, type M1 using the
**ℕ-sub-free reindex** in knowledge.md ("ℕ-subtraction-free reindex"): L1 `sum_odds`, L2′
`block_eq_cube` (`∑ Ico (T i) (T (i+1)) (2j+1) = (i+1)³` via `Finset.sum_Ico_consecutive _ hmn hnk`
(f explicit, two `≤` hyps explicit — see S5 pin-confirmation) +
the **division-free** ring identity `(i(i+1))²+4(i+1)³=((i+1)(i+2))²`, clearing `/2` by
`2*T k = k*(k+1)` with `Nat.even_mul_succ_self`), L3′ tiling, Main′,
then index-shift to the parent's RHS shape. Build via
`./proofs/scripts/docker-build.sh Proofs.SumOfKthPowersOQ03`; cross-check arithmetic against
`verify_m1.py` if any ring step misbehaves. Then add the gallery entry under
`src/data/proofs/sum-of-kth-powers-oq-03/`.
