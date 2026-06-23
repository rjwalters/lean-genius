# Erdős #748: The Cameron-Erdős Conjecture on Sum-Free Sets

**Problem**: Is f(n) = 2^{(1+o(1))n/2} where f(n) counts sum-free subsets of {1,...,n}?
**Status**: SOLVED (Green 2004, Sapozhenko 2003); formalized in Lean with 0 sorries (3 axioms remain for deep results).
**File**: `proofs/Proofs/Erdos748Problem.lean`

---

## Session 2026-04-14 (Session 1) — Prove cameron_erdos_proved via log sandwich

**Mode**: FRESH
**Outcome**: progress (1 sorry eliminated: 1→0)

### What I Did
- Claimed erdos-748 (knowledge score 0, EMPTY tier)
- Read `Erdos748Problem.lean` — 1 sorry in `cameron_erdos_proved`, 3 remaining axioms
- Designed log sandwich proof: squeeze log₂(f(n)) between ⌊n/2⌋ and log₂(C)+⌊n/2⌋
- Applied complete proof to worktree file; proof compiles

### Key Findings
- **Log sandwich strategy**: Lower: f(n) ≥ 2^⌊n/2⌋ → log₂(f n) ≥ ⌊n/2⌋. For n ≥ 1/ε: (1-ε)·n/2 ≤ n/2-1/2 ≤ ⌊n/2⌋ ≤ log₂(f n). Upper: f(n) ≤ C·2^⌊n/2⌋ → log₂(f n) ≤ log₂(C)+⌊n/2⌋. Let K = max(0, log₂(C)). For n ≥ 2K/ε: K ≤ ε·n/2, so log₂(f n) ≤ (1+ε)·n/2.
- **Key Lean tools**: `exists_nat_gt` for choosing large N, `Real.log_le_log` for monotonicity, `Real.log_pow` for log of power, `Real.log_mul` for log of product, `Nat.cast_nonneg` for ↑(n/2)≥0.
- **The ⌊n/2⌋ bridge**: Need `n/2 - 1/2 ≤ ↑(n/2:ℕ) ≤ n/2` to connect nat floor division with real division. This follows from `n = (n/2)*2 + n%2` and `n%2 ≤ 1`.
- **Remaining 3 axioms**: `trivial_lower_bound` (f(n) ≥ 2^{n/2}), `green_upper_bound` (f(n) ≤ C·2^{n/2}), `precise_asymptotic` (f(n)~c_n·2^{n/2}) — all require deep combinatorial machinery (Green's container method or Sapozhenko's approach), not formalizable short-term.
- **Aristotle**: Not needed — proof was developed manually.
- **Import added**: `Mathlib.Analysis.SpecialFunctions.Log.Basic` for `Real.log` lemmas.

### Files Modified
- `proofs/Proofs/Erdos748Problem.lean`: added log import, proved `cameron_erdos_proved` (sorry→proof)
- `src/data/proofs/erdos-748/meta.json`: sorries 1→0, lineCount updated
- `research/problems/erdos-748/knowledge.md`: this file

### Next Steps
- The 3 axioms are deep results requiring Green's container method or Sapozhenko's graph theory — not formalizable without substantial new Mathlib infrastructure (>1000 lines each).
- `trivial_lower_bound` is most approachable: requires showing that powerset of upper half has 2^{n/2} elements that are all sum-free.
- Status remains `axiomatized` (not `verified`) due to the 3 axioms.
