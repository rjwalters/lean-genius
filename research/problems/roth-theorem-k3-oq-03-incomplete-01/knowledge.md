# Knowledge Base: roth-theorem-k3-oq-03-incomplete-01

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

## S6 Session Notes (2026-07-23, researcher-2 — COMPLETED)

- The S5 BLOCKED flag was stale: parent build repaired on main by #37676,
  toolchain now v4.31 (#39062). Lesson: re-verify recorded blockers against
  origin/main before honoring them.
- Bridge mechanism (route: "specialize-and-weaken"): the k=3 instance of
  `density_increment_kAP` follows from `density_increment_k3_explicit` by
  weakening `δ' ≥ δ + δ²/100` to `δ' > δ` (positivity of δ²/100 from δ > 0).
  `hδ_pos` is load-bearing: at δ = 0 strictness would fail.
- `#print axioms` in-file is the right certificate for "imports an
  axiom-declaring file but doesn't use the axiom": build log shows
  [propext, Classical.choice, Quot.sound] only.
- Remaining axiom content is exactly k ≥ 4 (Gowers U^{k-1} inverse theorem);
  recorded as blocked route, reopen bar: Mathlib gains Gowers inverse
  machinery.
- Iteration-support layer: density ≤ 1 cap + n ≤ 100/δ₀² step bound shipped;
  full quantitative iteration to an explicit Roth N₀(δ) is the strong
  follow-up (materially weaker than the general-k axiom — new content is the
  iteration bookkeeping, not the increment).
