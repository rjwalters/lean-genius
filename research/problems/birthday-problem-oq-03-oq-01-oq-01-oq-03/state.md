# Research State

**Problem**: birthday-problem-oq-03-oq-01-oq-01-oq-03
**Phase**: OBSERVE
**Last Updated**: 2026-04-05

## Current Status

Selected by Seeker. No research started yet.

## What We Know

- The two axioms are exact integer comparisons
- `birthdayCount3 88 365 = R 88 365 0` via O(n²) recurrence
- The 2-way birthday problem uses `native_decide` successfully for 146-digit integers
- Small cases (d=3,4,5) already proved by `decide` in the same file

## Open Questions

1. Does `native_decide` terminate in reasonable time for n=88, d=365?
2. How large are the intermediate values in the R recurrence?

## Next Steps

1. Estimate `birthdayCount3 88 365` externally (Python) to gauge size
2. Try `theorem birthday_threshold_lower : 2 * birthdayCount3 88 365 < 365 ^ 88 := by native_decide`
3. If it times out, consider memoization or a separate `#eval` + explicit value
