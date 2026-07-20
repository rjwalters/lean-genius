# erdos-1003-wip-01 — Consecutive equal totients φ(n)=φ(n+1)

## State
OPEN. Erdős asks whether {n : φ(n)=φ(n+1)} is infinite (and the stronger
∀k≥1, {n : φ(n)=…=φ(n+k)} infinite). Parent Erdos1003Problem.lean was a
def-only stub: ConsecutiveEqualTotients, erdos_1003_conjecture,
ConsecutiveKEqualTotients, erdos_1003_strong_conjecture, countConsecutiveEqual,
carmichael_totient_conjecture — 0 theorems (small cases only as native_decide examples).

## Session 2026-07-20 (researcher-1)
Route: **foundational API + de-native_decide** on the def-only stub.

Added 16 axiom-free, kernel-checked theorems (host-verified Lean v4.31.0,
`#print axioms` = propext/Classical.choice/Quot.sound only — NO Lean.ofReduceBool):

- Converted 8 native_decide examples (memberships 1/3/15/104; totients 15/16/104/105)
  to kernel-`decide` theorems → file no longer depends on Lean.ofReduceBool.
- mem_consecutiveEqualTotients (membership characterisation).
- consecutiveKEqualTotients_zero (= univ), _one (= base set),
  _antitone (nested in k), _subset_base (k≥1 ⊆ base).
- countConsecutiveEqual_mono (monotone in N), _le (≤ N+1).
- strong_conjecture_imp_conjecture.

## Blocked / not attempted
- Infinitude (erdos_1003_conjecture) and the strong conjecture: OPEN, no known
  unconditional Lean-formalizable proof. Route "prove infinitude directly" BLOCKED
  (reopen bar: materially new mechanism / Mathlib infrastructure).
- EPS sparsity upper bound and FLP lower bound: analytic number theory beyond Mathlib.
