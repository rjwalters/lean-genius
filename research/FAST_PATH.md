# Fast Path Protocol

When a problem appears straightforward, use this abbreviated OODA loop instead of the full process.

## When to Use Fast Path

Use fast path when **ALL** of these are true:
- [ ] Problem has a well-known solution approach
- [ ] Direct Mathlib theorem exists or is likely
- [ ] Similar problem already solved in gallery
- [ ] Single obvious approach (no need to compare)
- [ ] Estimated time < 2 hours

If ANY checkbox is false → Use full OODA loop

## Fast Path Execution

### 1. QUICK-OBSERVE (5-10 min)
```
□ Grep codebase for existing proofs/axioms
□ Check related gallery proofs
□ One Mathlib search for key theorem
□ Document findings in state.md (brief)
```

Skip: Full literature survey, extensive web search

### 2. SKIP ORIENT/DECIDE
Go directly to ACT if:
- You found a directly applicable theorem
- There's only one viable approach
- The approach is obvious from OBSERVE

**Document why**: Add one line to state.md:
```
Fast path: Direct application of [theorem], skipping ORIENT/DECIDE
```

### 3. QUICK-ACT (30-60 min)
```
□ Write proof attempt
□ Iterate until compiles
□ Max 3 attempts before escalating to full loop
```

If 3 attempts fail → Escalate to full OODA with ORIENT phase

### 4. QUICK-VERIFY (5-10 min)
```
□ Build succeeds
□ Quick review of proof (no obvious gaps)
□ Spot-check 1-2 edge cases mentally
```

Skip: Formal adversarial attacks, extensive edge case testing

### 5. QUICK-LEARN (10 min) ← DON'T SKIP THIS
Even fast successes capture knowledge:
```
□ Fill out success-recap.md (not full post-mortem)
□ Add any tactic patterns to knowledge base
□ Update registry
```

## Fast Path → Full Loop Escalation

Escalate immediately if:
- Proof fails 3 times
- Unexpected type errors
- Theorem doesn't apply as expected
- Discover problem is more complex than thought

When escalating:
1. Document what was tried in hypothesis.md
2. Reset phase to ORIENT
3. Do full divergent ideation
4. Don't assume first approach was correct

## Comparison

| Phase | Full Loop | Fast Path |
|-------|-----------|-----------|
| OBSERVE | 30-60 min | 5-10 min |
| ORIENT | 30-60 min | SKIP |
| DECIDE | 15-30 min | SKIP |
| ACT | 1-4 hours | 30-60 min |
| VERIFY | 30-60 min | 5-10 min |
| LEARN | 30-60 min | 10 min |
| **Total** | **3-7 hours** | **50-90 min** |

## Example: cube-root-2-irrational

This problem was correctly handled as Fast Path:
- Well-known result
- `irrational_nrt_of_notint_nrt` found immediately
- Similar to sqrt2 proof
- Succeeded on first approach

What was missing: QUICK-LEARN step. Should have written success-recap.md.
