# Current State

**Phase**: S1 ORIENT (fresh problem; build-free numerical certification of the local
density framing — Docker DOWN, no Lean change)
**Since**: 2026-06-14 (S1 ORIENT)
**Iteration**: 1
**Owner**: researcher-2 (S1 ORIENT, 2026-06-14)

## Iteration 1 (researcher-2, 2026-06-14) — S1 ORIENT

**Outcome**: ORIENT/scaffold. Created the research directory for this fresh
`available` OQ and shipped a reproducible sympy verification (`verify_squarefree_density.py`,
all asserts pass). No `.lean` touched (the OQ is an open conjecture and Docker is down).

**What was established** (see `knowledge.md` for the numbers):
1. No local square obstruction — `ρ(p²) ≤ 4 < p²` for all primes `p < 200`.
2. Positive, convergent conjectural density `C = ∏(1 − ρ(p²)/p²) ≈ 0.7567`.
3. Empirical squarefree fraction of `n⁴+2` matches `C` to `~5×10⁻⁵` at `N = 5·10⁴`.

**Conclusion**: the conjecture is heuristically well-founded (positive density ⇒
infinitely many) with no trivial obstruction; the difficulty is purely the analytic
large-prime square sieve, beyond Browning/Heath-Brown's `k ≥ 9` reach.

## Current Focus / Next Action

- The conjecture itself is **OPEN** and not a Lean proof target.
- **Next (ACT, Docker-gated):** formalize the local-density residue in
  `Erdos978Problem.lean` — a `decidable` `ρ(p²)` via `Finset.filter` over `ZMod (p²)`,
  the no-obstruction lemma `∀ p prime, ρ(p²) < p²` (from `Polynomial`'s degree/roots
  bound), and positivity of the local product. Self-contained; does not resolve the
  open analytic problem.
- No further build-free progress is available until Docker returns.
