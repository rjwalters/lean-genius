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

## Session 2026-07-09 (researcher-1) — canonical sharp-threshold ES form (VERIFIED) + saturation note

**Saturation assessment.** All 5 OQ-05 files (main OQ05 18 thm, IncreasingIdentity 26,
KMonotonic 10, ErdosSzekeres, plus OQ02) are VERIFIED, 0 axioms, 0 sorries. The tractable
theory is complete: Mirsky lower bound, minMonotonicParts bracket + positivity, exact
minIncreasingParts=LDS identity, product bound n≤LIS·LDS, pigeonhole form, k-monotone
sandwich + k=1 endpoint. The ONLY remaining direction is the hard constructive O(√n)
Hanani UPPER bound (few monotone pieces always suffice) — genuinely open, not session-sized,
not Aristotle-shaped. Deliberately did NOT pad with trivial reindexed corollaries.

**One genuine gap filled (Erdos1026OQ05ErdosSzekeres.lean, 5→6 thm).** The file stated the
theorem only in the loose strict form `r·s<n ⟹ r<LIS ∨ s<LDS`; added the canonical textbook
statement with the SHARP Erdős–Szekeres number:
- `erdos_szekeres_threshold`: `(r-1)*(s-1) < n → r ≤ LIS seq ∨ s ≤ LDS seq`. Derived from
  the strict form at `(r-1, s-1)`; `omega` converts each `·-1 < ·` to `· ≤ ·` (valid for
  all r,s:ℕ incl. degenerate 0). Honestly a restatement at the canonical threshold, not new
  counting content — included for gallery recognizability (the famous (r-1)(s-1)+1 constant).

**Build.** VERIFIED `Built Proofs.Erdos1026OQ05ErdosSzekeres (3.8s)` at LEAN_MEMORY_LIMIT=8192.
Hit a shared-cache corruption first (`Mathlib/.../Acyclic.ir invalid header` from fleet race)
→ fixed with `docker-build.sh --repair-cache` (force cache re-download) → then the usual
SIGBUS-135 at olean-write on busy fleet, cleared in a quiet window. meta ES additionalFiles
synced 139→166 / 5→6.

## Session 2026-07-09 (researcher-7) — antitone-in-k (covering number non-increasing in the run budget)

Added the last clean elementary structural fact to `Erdos1026OQ05KMonotonic.lean` (282→348 lines,
+2 thm / +1 def): the full **antitone law** the file's own docstring only asserted informally.

- `IsKMonotonic.mono` (padding lemma): a `k`-monotone piece is `k'`-monotone whenever `1 ≤ k ≤ k'`,
  by clamping the run index `Fin k' → Fin k` via `j ↦ min j (k-1)` (repeats the last run in the
  surplus slots — **no empty runs needed**, since the covering condition only requires *some* run
  to hit each index). This is the reverse direction of the existing `IsKMonotonic.isMonotonic_of_one`.
- `KMonotonicDecomposition.mono`: lifts the padding to whole decompositions (parts padded, disjoint
  + covering data unchanged) — same shape as `monotonicToKMonotonic` / `kMonotonicToMonotonic_one`.
- `minKMonotonicParts_antitone`: `1 ≤ k ≤ k' ⟹ minKMonotonicParts k' seq ≤ minKMonotonicParts k seq`.
  Padding the optimal `k`-decomposition gives a `k'`-decomposition of the same size, so its part
  count bounds the `k'`-infimum (`Nat.sInf_le`). Combined with the k=1 identity this **subsumes**
  `minKMonotonicParts_le_minMonotonicParts` (previously the only monotonicity fact, at k=1 only).

**Significance:** completes the "non-increasing in k, pinned at the monotone covering number" picture.
Genuinely new (not a reindexed corollary): the general `k ≤ k'` comparison did not exist before.

### Gotcha (dependent-Sigma reindexing — the fiddly part flagged in prior notes)
The covering witness needs `b : Fin (runs j).1` placed where `Fin (runs (clamp J)).1` is expected.
`simp only [hfj]` REFUSES the rewrite (changes the bound variable `b`'s type → dependent motive,
reported as "unused simp arg"). Fix: **`rw [hfj]`** — `rw` abstracts `clamp J` into a motive
`fun x => ∃ b : Fin (runs x).1, …` that is type-correct for all `x : Fin k`, so the dependent
rewrite goes through. Use `set f := (clamp) with hf` so `f J` is an atomic rewrite target; prove
`f ⟨j.val,_⟩ = j` by `Fin.ext; simp only [hf, Fin.val_mk]; omega` (omega picks up `j.isLt` + `0<k`).

### ⚠️ BUILD STATUS: UNVERIFIED (2026-07-09, same fleet storm as Extremal above)
Elaboration is **CLEAN** — after the `rw` fix, ~6 consecutive builds show **zero** Lean type-error
diagnostics; the file crashes at olean-WRITE with exit 135 (SIGBUS), 2–5 s, across mem 16–30 GB, plus
intermittent transient dep-cache corruptions on the `import Mathlib` line (`FintypeCat.olean` /
`KullbackLeibler/Basic.ir` / different file each run = fleet race, not this file). The pre-edit build
of the unchanged file was green `[7744/7744] (4.4s)`, confirming toolchain is sound. Each of the 3 new
decls is a structural near-clone of an already-verified decl in the same file. Deployer should
re-attempt a green build in a quiet window (try `--repair-cache` + `LEAN_MEMORY_LIMIT=8192`).
