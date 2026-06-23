# Knowledge Base: stirling-formula-oq-01-incomplete-01

Insights accumulated during research on this problem.

---

## Problem Understanding

The originally-stated goal — formalize the first correction term in Stirling's
series, `n!/(√(2πn)(n/e)^n) = 1 + 1/(12n) + O(1/n²)` — is **already achieved
upstream** in `proofs/Proofs/StirlingExpansion.lean`:

| Theorem | Location | Status |
|---------|----------|--------|
| `stirling_first_correction` | StirlingExpansion.lean:574 | Proved, 0 sorries |
| `stirling_two_term_expansion` | StirlingExpansion.lean:810 | Proved, 0 sorries |
| `error_bound_from_correction` | StirlingExpansion.lean:851 | Proved, 0 sorries |

A targeted scan of the main file finds 0 `sorry` tokens and 0 `axiom`
declarations. The two sorries the original problem statement referenced (at
lines 94 / 106 of an older revision) were closed in earlier sessions.

## Local Evidence

- `state.md` was still in `OBSERVE` with zero attempts before this session.
- `src/data/research/problems/stirling-formula-oq-01-incomplete-01.json`
  explicitly recommends: "Resolve whether this incomplete slug should be
  retired or linked to the completed stirling-formula-oq-01 record. If
  continuing mathematically, target the next-order correction term."

## This Session (2026-06-05, researcher-1)

Followed the "target the next-order correction" branch. Added
`stirlingPartial_three` to StirlingExpansion.lean (just after
`stirlingPartial_two`):

```
theorem stirlingPartial_three (n : ℕ) (hn : n ≠ 0) :
    stirlingPartial 3 n = 1 + 1 / (12 * (n : ℝ)) + 1 / (288 * (n : ℝ) ^ 2)
```

Proof pattern mirrors `stirlingPartial_two`: `simp` unfolds the three-term
`Finset.range 3` sum against the explicit `stirlingCoeff_{zero,one,two}`
identities, then `ring` closes. This is a small algebraic identity, not a
bound — it merely names the second-order target on the left-hand side of
the still-open inequality.

## Insights

- `stirlingCoeff_two = 1/288` is already defined; what was missing was the
  partial-sum identity that names the second-order truncation. Without it,
  any future `stirling_second_correction` statement would have to inline the
  expression.
- The full second-order correction theorem
  `|stirlingSeq n / √π - stirlingPartial 3 n| ≤ C / n^3` remains genuinely
  open. The current proof of `stirling_first_correction` uses cubic and
  quartic log bounds (`log_one_plus_le_cubic`, `log_one_plus_ge_quartic`,
  `log_one_plus_le_quintic` already exist) — pushing to `C/n^3` would
  require sharper, higher-order log expansions and a parallel
  telescoping argument over the Stirling step formula.
- The Aristotle companion `StirlingExpansionAristotle.lean` declares
  `stirling_first_correction` and `stirling_two_term_expansion` as sorries
  in the same `namespace StirlingExpansion`. This appears to overlap the
  proved versions in the main file; left untouched this session to avoid
  any namespace-collision risk without a fresh build to verify.

## Dead Ends

- None new this session.

## Next Steps

1. Prove `stirling_second_correction` (the open `C/n^3` bound) — likely
   needs a sharper log expansion plus a refined telescoping argument.
2. Audit the `StirlingExpansionAristotle.lean` namespace overlap with the
   main file; either delete the redundant sorries or rename to a separate
   companion namespace.
3. If neither (1) nor (2) is undertaken, this slug should be retired in
   favour of `stirling-formula-oq-01` (the verified parent).
