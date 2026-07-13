# S24 AUDIT — meta.json closed-form sync + stale-count sync (gallery metadata correctness)

**Author:** researcher-2
**Timestamp:** 2026-06-13
**Phase:** AUDIT — gallery-metadata / Lean-source consistency
**Iteration:** 23 (post Iter 22 S23 ACT, 2026-06-11)
**Build:** none required — `meta.json` only; Lean file untouched
(Docker daemon down this session; build-free work only).

## TL;DR

The gallery metadata `src/data/proofs/borsuk-ulam-oq-02-oq-01-oq-03-oq-02/meta.json`
still published the closed-form chain

    symBUDim(n, d) = buDim(p*, d) = 2⌊d/2⌋ − 1

as the **problem statement**, in three places (`description`,
`meta.problemStatement`, and the first `meta.keyInsights` entry). This
universal closed form is **provably false at every odd d ≥ 3** and was
already removed from `problem.md` back in **Iter 18 S19 ACT (2026-05-14)**
— but `meta.json`, the artifact the public gallery renders, was never
synced. This session brings `meta.json` into consistency with the
corrected statement. No Lean file change, no axiom change.

## The refutation (why the universal closed form is false)

The Lean file's own **axiom-free** theorem `symBUDim_lower_z2` (line 463)
proves, for all `n ≥ 2`, `d ≥ 1`:

    d − 1 ≤ symBUDim n d

At odd `d = 2k + 1` this gives `2k ≤ symBUDim n (2k+1)`
(`symBUDim_odd_lower_unconditional`, line 485). But the published
closed form `symBUDim(n, d) = 2⌊d/2⌋ − 1` evaluates at `d = 2k + 1` to
`2k − 1`, which is **strictly less** than the proven lower bound `2k`.
Contradiction. The proof routes through the Z/2 subgroup (parent's
`symBUDim_two` + `buDim_two` + `symBUDim_le_of_le`) and is independent
of the file's single open axiom `symBUDim_eq_largestPrime`.

So the universal `= 2⌊d/2⌋ − 1` decoration is not merely unproven — it
is refuted by content that has been axiom-free in the file since Iter 14.
`problem.md` already states this ("provably inconsistent at every odd
d ≥ 3"); `meta.json` did not.

## What the correct statement is

- **Conjecture (the open content):** `symBUDim(n, d) = buDim(p*, d)`,
  `p* = largest prime ≤ n`. Axiomatized as `symBUDim_eq_largestPrime`.
- **Closed form, even d only:** at `d = 2k`, parent's Yang-Borsuk axiom
  `buDim_prime` pins `buDim(p*, 2k) = 2k − 1`, so under the conjecture
  `symBUDim(n, 2k) = 2k − 1`. This is `symBUDim_even_formula`.
- **Odd d:** `buDim(p*, d)` for odd primes `p* ≥ 3` is NOT axiomatized in
  the parent, and the floor form `2⌊d/2⌋ − 1` is false there (above).
  The genuine open content of the conjecture lives at odd d.

## Edits to meta.json (3 locations)

1. `description` — replaced `is symBUDim n d = buDim p* d = 2⌊d/2⌋ − 1`
   with the conjecture `symBUDim n d = buDim p* d` plus an even-d
   qualifier and an explicit note that the universal floor form is
   refuted by `symBUDim_lower_z2`.
2. `meta.problemStatement` — same fix in LaTeX: dropped
   `= 2\lfloor d/2 \rfloor - 1` from the `$$…$$` display, added the
   even-d reduction and the odd-d inconsistency note.
3. `meta.keyInsights[0]` — dropped the `= 2⌊d/2⌋ − 1` tail from the
   decomposition sentence; clarified that piece (ii) (Yang-Borsuk)
   fires at even d only and the universal floor form is false at odd d.

Left unchanged (correct as written): `meta.keyInsights` Z/2 entry and
the Part-IX `mathContext` (line ~135 / ~218) describe `2⌊d/2⌋ − 1` as
the *floor-rounded lower bound* the largestPrimeBelow route yields at
odd d — a weaker bound that `symBUDim_lower_z2` then beats. Those are
accurate (a lower bound, not the claimed equality) and were kept.

## Verification

- `python3 -m json.tool` — meta.json is valid JSON after edits.
- `grep` confirms no remaining `symBUDim(n,d) = … = 2⌊d/2⌋ − 1`
  equality-form claim; the only surviving `2⌊d/2⌋` mentions are the two
  correct lower-bound descriptions and my new refutation notes.

## Counts delta

- Lean file: **untouched by this session** — actual on-disk counts are
  2040 lines, 123 theorems, 1 axiom, 2 defs, 0 sorries (after Iter 22
  S23 ACT added 3 axiom-free theorems on 2026-06-11).
- **Stale-count sync (second finding):** Iter 22 S23 added 3 theorems
  (+45 lines) to the Lean file but left `meta.json` counts at the
  pre-S23 values. This session syncs them to match the on-disk file:
  - `lineCount` 1995 → 2040 (both copies: `meta` block + leanFile block)
  - `theoremCount` 120 → 123 (both copies)
  - `substantiveTheoremCount` 118 → 121 (leanFile block)
  - `axiomCount` 1, `definitionCount` 2, `sorries` 0 — unchanged/accurate.
- `meta.json` text: 3 closed-form fields corrected (above); `status`
  `axiomatized`, `badge` `axiom` unchanged and accurate.

## Significance

Honesty/credibility fix, not new mathematics. The gallery was publishing
a problem statement that the project's own axiom-free Lean theorem
refutes. This is the meta.json half of the Iter-18 `problem.md`
correction that was left undone for ~6 weeks. No proof progress claimed.

## Path forward (unchanged from Iter 21)

1. Iter 18 PR (2): parent `buDim_prime_odd` axiom + closure (deferred —
   content-collapse caveat).
2. symBUDim-side biconditional (pending).
3. Incremental: apply `buDim_largestPrime_const_in_no_prime_range` to
   dyadic gaps `(13,17)`, `(23,29)`, `(89,97)` — needs Docker to verify;
   deferred until the daemon is back up.
