# Knowledge: erdos-1026-oq-05 (k-monotonic decompositions / Hanani lower bound)

`proofs/Proofs/Erdos1026OQ05.lean` (self-contained, `import Mathlib`) already proves,
axiom-free, the Mirsky/Dilworth lower bound `n ≤ numParts · max(LIS, LDS)` for any
monotonic decomposition, its division form, and `singletonDecomposition` existence.

## Session 2026-07-08 (researcher-2) — minMonotonicParts invariant + bracket (0 axioms)

Added the **actual extremal invariant** OQ-05 asks about (the file previously only bounded
a *given* decomposition, never defined the minimum):
- `minMonotonicParts seq := sInf {p | ∃ D, D.numParts = p}` — the covering number (Hanani).
- `minMonotonicParts_le : minMonotonicParts seq ≤ n` (singleton witness, `Nat.sInf_le`).
- `minMonotonicParts_ge : n / max(LIS,LDS) ≤ minMonotonicParts seq` (`le_csInf` + the
  per-decomposition `monotonicDecomposition_numParts_ge`).
- `minMonotonicParts_bracket` : `[n/max(LIS,LDS), n]`.

### ✅ BUILD STATUS: VERIFIED (resolved 2026-07-08 researcher-2 follow-up)
The `minMonotonicParts` additions of #35758 now compile green under Docker
(`Proofs.Erdos1026OQ05`, exit 0, "Completed successfully!") — the earlier UNVERIFIED
status was purely the SIGBUS storm, not a math problem. Confirmed 0 axioms, 0 sorries.

## Session 2026-07-08 (researcher-2, follow-up) — verify build + covering-number positivity

- Obtained the green build that #35758 could not (fleet had calmed).
- Added `numParts_pos_of_pos` (any decomposition of a nonempty seq has `numParts > 0`,
  since `D.covering ⟨0,hn⟩` yields an `i : Fin numParts`) and `minMonotonicParts_pos`
  (`0 < minMonotonicParts seq` for `0 < n`, via `Nat.sInf_mem` on the nonempty achievable
  set + `numParts_pos_of_pos`). This sharpens the lower bracket: the division bound
  `n / max(LIS,LDS)` degenerates to 0 when the longest monotone run dominates n, but
  positivity always holds — you cannot cover a nonempty sequence with zero monotone pieces.
- Counts synced 216→237 / 12→14 (definitionCount unchanged at 10). Note main's meta was
  stale w.r.t. #35758 prose (no `minMonotonicParts` section); added a `covering-number`
  section covering both #35758 and this session.

### Gotcha already fixed
Term-mode `Nat.sInf_le ⟨…⟩` / `le_csInf ⟨…⟩` fails with "Invalid `⟨…⟩` notation: expected
type could not be determined" because `minMonotonicParts` is a plain def wrapping `sInf`
and the anon-constructor arg elaborates before the metavars are pinned. Fix: `unfold
minMonotonicParts` then `apply Nat.sInf_le` / `apply le_csInf` (conclusion unifies first),
supplying the membership/nonempty witness as a separate `exact ⟨…⟩` goal. This deterministic
error was observed and fixed; only the SIGBUS-clean rebuild remains.

## Session 2026-07-09 (researcher-8) — Erdős–Szekeres extremal staircase (bracket is TIGHT)

New companion `Proofs/Erdos1026OQ05Extremal.lean` (320 lines, 14 thm/lemma, 2 def, **0 axioms,
0 sorries**). Prior work only *bounded* the covering number and never exhibited a sequence
that *forces* many pieces. This session supplies the missing **extremal witness**.

The classic staircase on `n = k²` points, `value(i) = k·(i/k) − (i%k)` (blocks of length `k`,
increasing across blocks, strictly decreasing within each block):
- `staircase_LIS : LIS = k`  (block map `i ↦ i/k` is injective on any increasing run ⇒ `≤ k`;
  the `remainder-0` column `j ↦ k·j` is an increasing run of length `k` ⇒ `≥ k`).
- `staircase_LDS : LDS = k`  (column map `i ↦ i%k` injective on any decreasing run ⇒ `≤ k`;
  the first block `j ↦ j` is a decreasing run of length `k` ⇒ `≥ k`).
- `staircase_injective` (value distinct — needed for the `min(LIS,LDS)` upper bound).
- **`minMonotonicParts_staircase : minMonotonicParts (staircase k) = k`** — the general bracket
  `[n/max(LIS,LDS), min(LIS,LDS)]` COLLAPSES: `k = k²/k ≤ mMP ≤ min(k,k) = k`. Reuses the two
  existing bracket theorems (`minMonotonicParts_ge`, `minMonotonicParts_le_min_LIS_LDS`).
- `minMonotonicParts_staircase_eq_sqrt` and `exists_sqrt_monotone_parts_needed`: for every
  `n = k²` there is a sequence whose covering number is exactly `√n`.

**Significance:** shows the two-sided bracket is TIGHT and that `Θ(√n)` monotone pieces are
sometimes NECESSARY (lower-bound extremal side). Does NOT prove the hard universal Hanani
*upper* bound (√n pieces always suffice for EVERY sequence) — still open.

### Proof recipe (reusable)
Three cancellation lemmas keep everything linear: same-block ⇒ value decreases (block term
`k·(·/k)` cancels), diff-block ⇒ value increases (the `≥ k` block gap dominates the `< k`
remainder penalty — the one `nlinarith` spot), same-column ⇒ value increases (compare the
block terms directly, no quotient comparison). `Nat.div_add_mod` + `omega` after `rw [hblk]`
/`rw [hcol]` (align the shared block/remainder atom first, else omega can't relate `k*q₁`,
`k*q₂`). Upper bounds via `Fintype.card_le_of_injective` of a block/column map into `Fin k`;
`csSup_le` with the empty-subsequence nonempty witness `Subsequence.mk Fin.elim0 (fun a => a.elim0)`.

### ⚠️ BUILD STATUS: UNVERIFIED (2026-07-09)
Elaboration is CLEAN — dependency `Erdos1026OQ05IncreasingIdentity` builds green, then the
Extremal file crashes at olean-WRITE with exit 135 (SIGBUS) / 139 (SIGSEGV), 430ms–1.4s, **zero
Lean type-error diagnostics** across 6 attempts (mem 24–32 GB). Classic fleet memory-pressure
storm, not a math error. Deployer should re-attempt a green build before merge.

### Still open
The matching `O(√n)` **upper** bound (few monotone pieces always suffice — the hard
constructive Hanani direction) is stated in the file docstring, not axiomatized.
