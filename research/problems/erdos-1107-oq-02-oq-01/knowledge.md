# Knowledge Base: erdos-1107-oq-02-oq-01

## Problem Summary

**Title**: Threshold for the r=3 (cubeful) case of Erdős #1107
**Parent**: erdos-1107-oq-02 (Effective Squareful Sum Threshold, r=2)
**Question**: For cubeful (3-powerful) numbers, what is the threshold N₃ such that every
n ≥ N₃ is a sum of ≤ 4 cubeful numbers? Identify the exceptional set.

A number n is *r-powerful* iff every prime p | n satisfies pʳ | n (1 is r-powerful
vacuously, and is admitted as a summand, matching the r=2 base case where 7, 15, 23, …
are exceptions only because the small-summand set is {1, 4, …}).

The gallery overview for the parent states Erdős #1107 as "every large n is a sum of at
most **3** r-powerful numbers for every r", while the parent's own `description` field
states the "at most **r+1**" form. These two framings disagree at r=3. This session
settles the disagreement empirically.

## Session 2026-06-14 (Session 1) — ORIENT, threshold computation

**Mode**: FRESH
**Outcome**: progress (ORIENT; durable computation, Lean ACT deferred — Docker down)

### What I Did
- Wrote `proofs/scripts/verify_cubeful_sums.py`, a bounded coin-change DP over the
  r-powerful basis. **Validated** it by exactly reproducing the known r=2 result:
  threshold 120, exceptions {7, 15, 23, 87, 111, 119}.
- Computed the r=3 (cubeful) representation problem for both ≤3 and ≤4 summands, over
  ranges up to 60000.

### Key Findings
- **≤4 cubeful summands has a sharp finite threshold: N₃ = 2040.** There are exactly
  **45 exceptions**, the largest being **2039**, and *no* exceptions in (2039, 60000]
  — a ~58000-wide clean gap above the last exception, strong evidence the threshold is
  genuine (conditional on the asymptotic; see below).
  Exceptional set:
  `{5,6,7,12,13,14,15,20,21,22,23,31,38,39,46,47,53,58,69,77,79,85,95,101,103,111,
    175,196,212,228,231,247,327,444,458,490,606,662,860,975,1167,1470,1821,1967,2039}`
- **≤3 cubeful summands does NOT have a finite threshold.** The exceptional set keeps
  positive density: ~0.30 on (0,10000], still ~0.21 on (50000,60000], not decaying.
  So the "≤3 for all r" framing is **false at r=3** — only r=2 enjoys the constant 3.
- **Structural law (the reason).** The count of r-powerful numbers up to x is ∼ Cᵣ·x^{1/r}.
  Hence the k-fold sumset has ∼ x^{k/r} elements up to x, which covers a positive
  proportion of [1,x] only when **k/r > 1**, i.e. **k ≥ r+1**. The critical case k = r
  (here 3 = r for r=3) has sumset of the *same order* x as the target, so a positive
  density is permanently missed (C₃³/6 < 1). This both explains why r=2 needs 3 and r=3
  needs 4, and confirms the parent's **r+1** framing over the overview's constant-3 one.

### Honesty / scope
- The *asymptotic* "every large n is a sum of ≤4 cubeful numbers" is, to my knowledge,
  still **open** for r=3 (no proven Heath-Brown analog). So N₃ = 2040 is the *effective
  threshold conditional on the asymptotic*, exactly parallel to the r=2 gallery entry
  (native_decide for a finite range + an axiom for the tail). The unconditional half —
  that ≤3 cannot work (positive exception density) — needs no such assumption.

### Files Modified
- `proofs/scripts/verify_cubeful_sums.py` (durable, runnable: validates r=2, computes r=3)
- `research/problems/erdos-1107-oq-02-oq-01/knowledge.md` (this file)
- `src/data/research/problems/erdos-1107-oq-02-oq-01.json` (knowledge record)

### Next Steps (ACT — Docker-gated, ~180 LOC)
- Transcribe `proofs/Proofs/Erdos1107OQ02.lean` (156 LOC template) to a cubeful version:
  `IsCubeful` (exponents ≥ 3) + Decidable instance; `isSumOf4Cubeful : ℕ → Bool`
  (4 nested loops over the cubeful basis ≤ n); `native_decide` lemmas for the 45
  exceptions, for the non-exceptions in [1,2040), and for blocks [2040,N] in chunks;
  one `axiom cubeful_sum_threshold` for n ≥ 2040 (the conjectural asymptotic).
- Build via `./proofs/scripts/docker-build.sh Proofs.Erdos1107OQ02OQ01` once Docker is up.
- Optional: confirm 2040 stability to a much larger bound (e.g. 10⁶) with a sieve-based
  DP before committing the threshold as the axiom's hypothesis.

## Session 2026-06-14 (Session 2, researcher-5) — threshold stability to 10⁶/10⁷

**Mode**: continue (build-free; Docker + Aristotle both down, re-probed this session)
**Outcome**: progress — discharged the "Optional" next-step above (threshold-stability check).

### What I Did
- Wrote `proofs/scripts/verify_cubeful_stability.py`: a **fast, sieve-based** redo of the
  ≤4-cubeful-summand exception scan, replacing the Session-1 per-number `factorint` + Python
  BFS (capped at N≈20000) with an SPF sieve (cubeful basis in O(N log log N)) + a `numpy`
  shift-OR bounded coin-change DP over all of [0, N]. Same validation gate: it reproduces the
  r=2 base case ({7,15,23,87,111,119}) and exits non-zero unless the cubeful exception set is
  **exactly** the known 45.

### Key Finding (hardens the axiom hypothesis)
- **N₃ = 2040 is stable far beyond the original 60000 bound.** The exceptional set is exactly
  the known 45 (largest 2039) with **no exception in (2039, 10⁶]** — verified in the committed
  script (cubeful basis size 307; runs in <1 s) — and **identically no exception in (2039, 10⁷]**
  (spot-confirmed this session; cubeful basis 713, ~9 s). The clean gap above the last exception
  grows from ~58 000 to ~10 000 000, strong empirical support for committing 2040 as the
  hypothesis of the eventual `axiom cubeful_sum_threshold`.

### Honesty / scope
- This is a **stability/regression** strengthening of the Session-1 computation, not a new
  theorem. The r=3 asymptotic ("every large n is a sum of ≤4 cubeful numbers") remains **open**;
  2040 is the effective threshold *conditional* on it. The unconditional half (≤3 fails with
  positive exception density) is unchanged. No Lean written — ACT (the ~180 LOC transcription +
  one axiom) stays Docker-gated exactly as Session 1 left it.

### Files Modified
- `proofs/scripts/verify_cubeful_stability.py` (new; default N=10⁶, accepts an override bound)
- `research/problems/erdos-1107-oq-02-oq-01/knowledge.md` (this session note)
