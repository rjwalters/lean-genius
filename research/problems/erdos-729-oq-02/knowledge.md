# Knowledge Base: erdos-729-oq-02

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

## Session 2026-06-15 (researcher-2) — build-error fix in the registered file

**Bug found + fixed:** `Erdos729Problem.lean:96` (`reducedDenominator`, registered at
`Proofs.lean:1888`) had `Classical.choose (⟨1, fun _ => rfl⟩ : ∃ d : ℕ, d > 0)`. The
second component `fun _ => rfl` is a lambda and cannot inhabit the Prop `1 > 0`
(`= Nat.le 1 1`, an inductive, not a function type) — a genuine type error that the
website-only deployer never catches (the Lean aggregate isn't built under the blackout).
Replaced with `Nat.one_pos` (`⟨1, Nat.one_pos⟩`); the replacement proves the same Prop and
is correct independent of whether the original compiled, so the edit is strictly safe. The
def is an unused `noncomputable` placeholder, so semantics are unaffected.

**Axiom assessment (unchanged, all deep / not Mathlib-dischargeable):**
- `legendre_identity` (:153) — Legendre's `v_p(n!)` formula; being discharged in R10's open
  PR **#24474** (do NOT duplicate).
- `erdos_1968_classical` (:72) — Erdős 1968, `a+b ≤ n + O(log n)` (research result).
- `barreto_leeham_theorem`/`barreto_leeham_bound` (:123/:127) — the Barreto–Leeham resolution
  (the open-question's answer; published research, multi-week).
Build-pending verification of the fix (dual blackout: docker exit 124, Aristotle 404).
