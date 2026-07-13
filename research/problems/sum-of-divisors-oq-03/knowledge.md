# Knowledge: sum-of-divisors-oq-03 — Robin's inequality + RH equivalence

## Session 1 (researcher-2, 2026-06-27): OBSERVE → SURVEY/ACT

### Established Facts

- **Robin's theorem (1984)**: RH ⟺ `σ(n) < e^γ·n·ln(ln n)` for all `n ≥ 5041`. Formalized as the
  axiom `robin_iff_riemannHypothesis` (the gallery-requested RH bridge).
- **The candidate framing is WRONG on two counts** (both now documented):
  1. Robin's inequality is FALSE on `n ≤ 5040` — it fails on a finite exceptional set whose largest
     element is `5040 = 7!`. (Under RH, exactly 27 numbers: 1,2,3,4,5,6,8,9,10,12,16,18,20,24,30,36,
     48,60,72,84,120,180,240,360,720,840,2520,5040.) So there is no true "∀ n ≤ 5040" statement.
  2. `native_decide` cannot decide it: `e^γ`, `ln(ln n)` are transcendental ⇒ not `Decidable`.
- **Mathlib γ bounds are only `1/2 < γ < 2/3`** ⇒ `e^γ ∈ (1.6487, 1.9477)`. Too loose for the
  boundary: at n=5040, `σ(n)/n ≈ 3.838` vs `e^γ·ln(ln 5040) ≈ 3.82`; loose enclosure → `(3.54,4.18)`,
  undecided.

### What was delivered — `proofs/Proofs/SumOfDivisorsOQ03.lean` (namespace `SumOfDivisorsRobin`)
Verified structure (0 axioms) + requested RH axiom (1 axiom). 1 def, 4 theorems, 1 axiom, 0 sorries.
- `RobinInequality n` — precise predicate via `Real.eulerMascheroniConstant`, `ArithmeticFunction.sigma 1`.
- `exp_eulerMascheroni_lower`/`_upper` — `e^{1/2} < e^γ < e^{2/3}` (sharpest from Mathlib's γ bounds).
- `log_log_pos` (n≥3), `robin_rhs_pos` (n≥3) — well-posedness of the comparison.
- `robin_iff_riemannHypothesis` — AXIOM: Robin's theorem. Status: **axiomatized** (axiomCount=1).
Registered in Proofs.lean.

### Promising Leads / blocker for the computational claim
The only route to "verify Robin on a finite head & prove 5040 exceptional" is a MUCH tighter `e^γ`
enclosure (~`1.781 < e^γ < 1.782`). Mathlib lacks this; producing more terms of `eulerMascheroniSeq`
/`eulerMascheroniSeq'` to tighten `eulerMascheroniConstant` bounds is the self-contained prerequisite
sub-project. Until then OQ-03's computational half is BLOCKED.

### Failed Approaches
- `native_decide` on the comparison — impossible (transcendental, non-Decidable). Don't retry.

### Verification status: UNVERIFIED
Both channels down (Docker containerd `meta.db` I/O error + `docker images` empty; Aristotle MCP 404).
All Mathlib lemma names verified present by grepping the pinned package.
