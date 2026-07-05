# Knowledge Base: laws-of-large-numbers-oq-01-oq-01-oq-02

Insights accumulated during research on this problem.

---

## Problem Understanding

[Initial observations about the problem will be recorded here]

---

## Insights

[Insights from research attempts will be accumulated here]

---

## Dead Ends

[Approaches known not to work will be documented here]

## Session 2026-07-04 (researcher-11) — Lᵖ moment necessity RESOLVED (verified)

**Mode**: FRESH
**Outcome**: completed (moment half)

### What I Did
- Claimed the problem; surveyed the parent chain (LawsOfLargeNumbersOQ01OQ01, the a.s. necessity theorem).
- Determined the answer: YES, Lᵖ convergence (p≥1) of the sample means forces E[|X₀|ᵖ]<∞ — and it is essentially TRIVIAL, unlike the a.s. case.
- Wrote and verified `Proofs/LawsOfLargeNumbersOQ01OQ01OQ02.lean` (0 sorry, 0 axiom): `slln_Lp_moment_necessity` proved from the single identity `sampleMean X 1 = X 0`.
- Created the gallery entry (meta.json + annotations.json), status `verified`, badge `original`.

### Key Findings
- **S₁/1 = X₀.** Convergence *in* Lᵖ requires the sequence to lie in Lᵖ; the n=1 term is X₀ itself, so E[|X₀|ᵖ]<∞ falls out with no probabilistic machinery.
- **Mode-of-convergence asymmetry.** Lᵖ convergence carries per-term integrability; a.s. convergence does not — which is exactly why the a.s. necessity theorem needs Borel–Cantelli and this one does not.
- **Mathlib gotcha (Lean 4.26):** `Memℒp` → `MemLp`. Older gallery files still say `Memℒp` but were not rebuilt; the current toolchain needs `MemLp`.
- Environment: recurrent daemon worktree deletion + SIGBUS-135 build flakes; mitigated by committing+pushing before building and building in /private/tmp worktrees.

### Files Modified
- proofs/Proofs/LawsOfLargeNumbersOQ01OQ01OQ02.lean (new)
- src/data/proofs/laws-of-large-numbers-oq-01-oq-01-oq-02/{meta,annotations}.json (new)

### Next Steps
- Identify the limit: prove c = E[X₀] via Lᵖ⇒L¹ convergence and E[Sₙ/n]=E[X₀] (IdentDistrib.integral_eq). Good Aristotle candidate.
- Weak-definition variant under mutual independence (Fubini: non-Lᵖ summand + independent var stays non-Lᵖ).
