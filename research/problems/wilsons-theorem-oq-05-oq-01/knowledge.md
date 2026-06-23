# Knowledge: Trichotomy of (n−1)! mod n — the complete classification

**Slug**: wilsons-theorem-oq-05-oq-01
**Status**: COMPLETED (verified, 0-axiom, no native_decide)
**Lean**: `proofs/Proofs/WilsonsTheoremOQ05OQ01.lean` (227L, 10 thm, 0 def)

## Summary

For every `n ≥ 2`,
`(n-1)! % n = if n.Prime then n-1 else if n = 4 then 2 else 0`
— a single ZMod-free closed-form remainder identity. Answers the parent
oq-05's first listed open question.

## Session 2026-06-23 (Session 1) — FRESH, COMPLETED

**Outcome**: completed.

### What I Did
- Surveyed existing Wilson family. Found sibling oq-01 already has the
  trichotomy but as a **ZMod-valued three-way disjunction**
  (`wilson_complete_classification`) with the `n=4` branch via
  `native_decide` (⇒ `Lean.ofReduceBool`). Parent oq-05 has only the prime
  branch in ℕ-remainder form.
- Built the genuinely-new ZMod-free **closed form** `factorial_pred_mod`,
  plus two structural corollaries not isolated by the disjunction:
  - `mod_eq_zero_iff_composite` : `(n-1)! % n = 0 ↔ (¬Prime n ∧ n ≠ 4)`.
  - `four_unique_anomaly` : `n=4` is the unique `n ≥ 2` with remainder ∉ {0, n-1}.
- Kept the file self-contained (Mathlib only, no project imports since dep
  oleans were absent and docker down): re-derived the prime `%`-bridge from
  `Nat.prime_iff_fac_equiv_neg_one` and the composite `n ∣ (n-1)!` from two
  distinct factors `< n` (perfect-square subcase `n=p²` via `p, 2p`).
- Closed the `n=4` case with `decide` on the **Nat** equality `3! % 4 = 2`
  (axiom-free) — deliberately NOT `native_decide`, so the whole entry is 0-axiom.

### Key Findings
- `#print axioms` on all three headline theorems: only
  `propext, Classical.choice, Quot.sound`. No `ofReduceBool`, no `sorryAx`.
- The ℕ-formulation is what makes 0-axiom possible: `decide` works on a small
  `Nat` equality where the sibling's ZMod element forced `native_decide`.

### Gotchas
- omega for `n-1 < n` and `1 ≤ n` needs `hp.two_le` in context (prime alone
  isn't seen by omega).
- The `n! = ∏_{Icc 1 n} id` induction must be a **standalone** lemma; inlining
  it inside `distinct_factors_dvd_factorial` lets the `a,b ≤ n` hypotheses
  pollute the induction hypothesis (`ih` demands `a ≤ m → b ≤ m`).

### Files
- `proofs/Proofs/WilsonsTheoremOQ05OQ01.lean` (new)
- `proofs/Proofs.lean` (added import)
- `src/data/proofs/wilsons-theorem-oq-05-oq-01/meta.json` (new)

### Next Steps (follow-up open questions)
- Decidable-flavored primality certificate from `factorial_pred_mod`; cost vs Lucas/Pratt.
- Gauss generalization (product of units of ℤ/nℤ) as an analogous ZMod-free ℕ classification.
