# Knowledge Base: e-transcendental-oq-02-oq-06

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

---

## Session 2026-07-08 (Researcher-8) — Frequency-mismatch criterion

**Mode**: FRESH | **Outcome**: progress (VERIFIED, 0 sorry, 0 new axiom)

### What I did
Generalized the existing *absence* obstruction (`not_normal_of_eventually_missing_ktuple/_digit`,
which handles matching-frequency `0`) to arbitrary frequency anomalies. Added to
`proofs/Proofs/ETranscendentalOQ02.lean` (PART IV.7):

- `not_normal_of_match_freq_tendsto_ne` — if a k-tuple's matching frequency
  converges to `L ≠ b^(-k)`, then not normal. One line via `tendsto_nhds_unique`
  against the definitional limit `hn k s`.
- `not_normal_of_match_freq_eventually_le` / `_eventually_ge` — if the matching
  frequency is *eventually* `≤ c < b^(-k)` (resp. `≥ c > b^(-k)`), then not
  normal. Uses `le_of_tendsto` / `ge_of_tendsto`; **no convergence of the
  frequency is assumed** — strictly stronger than the tendsto form. Captures
  under- and over-representation.
- `not_normal_of_digit_freq_tendsto_ne` — single digit with density `≠ 1/b`
  forbids normality (k=1). Bridged `b^(-(1:ℤ)) = b⁻¹` via `Nat.cast_one` +
  `zpow_neg_one`; collapsed the `∀ i : Fin 1` predicate with `Fin.forall_fin_one`.

### Key findings
- The absence case was the extreme (`L = 0`) instance; the general anomaly needs
  nothing beyond uniqueness of limits (`tendsto_nhds_unique`) or one-sided limit
  comparison (`le_of_tendsto` / `ge_of_tendsto`). The eventual-bound forms are the
  real content: they conclude non-normality from a *single* frequency inequality
  holding eventually, without the frequency converging.
- The necessary-condition theory for normality is now complete: irrational ⇐
  normal, disjunctive ⇐ normal, and full frequency-mismatch ⇐ ¬normal.

### Status
Core axiom `e_absolutely_normal` remains **genuinely open** (no base is proved
normal for e as of 2026) — not eliminable. This session strengthens the sharp
boundary, not the open core.

### Files modified
- `proofs/Proofs/ETranscendentalOQ02.lean` (+4 theorems, PART IV.7)
- `src/data/proofs/e-transcendental-oq-02/meta.json` (lineCount 1021→1114, theoremCount 61→65)
- `src/data/research/problems/e-transcendental-oq-02-oq-06.json` (knowledge)
