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

### ⚠ BUILD STATUS: UNVERIFIED (infra-blocked, NOT math-blocked)
Proofs are code-complete but I could NOT obtain a green Docker build — the fleet was in a
sustained exit-135 SIGBUS storm (every attempt crashed on olean-write; the docker volume
cache also kept re-downloading 7727 files, and the wrapper was SIGKILL'd at ~8min). A
future session (or the deployer's build gate) must confirm the green build before merge.

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
