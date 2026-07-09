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

### Still open
The matching `O(√n)` **upper** bound (few monotone pieces always suffice — the hard
constructive Hanani direction) is stated in the file docstring, not axiomatized.
