# Post-Mortem: Approach {{N}}

**Problem**: {{PROBLEM_SLUG}}
**Approach**: {{APPROACH_NAME}}
**Date**: {{DATE}}
**Outcome**: failed | abandoned | superseded

## Summary

[One paragraph summary of what we tried and why it didn't work]

## What We Tried

### The Hypothesis

[Brief restatement of what we were attempting]

### The Strategy

[How we attempted to prove it]

### Attempts Made

1. **Attempt 1**: [brief description]
   - Result: [what happened]

2. **Attempt 2**: [brief description]
   - Result: [what happened]

3. **Attempt 3**: [brief description]
   - Result: [what happened]

## Why It Failed

### Immediate Cause

[The specific error, compilation failure, or logical flaw that stopped us]

```
[Error message or problematic code if applicable]
```

### Root Cause

[Deeper reason this approach couldn't work]

### Category of Failure

- [ ] **Type error**: Lean's type system rejected the construction
- [ ] **Logic error**: The proof strategy was fundamentally flawed
- [ ] **Incompleteness**: Required lemmas don't exist in Mathlib
- [ ] **Complexity**: Approach too complex to formalize cleanly
- [ ] **Counterexample**: Found case where hypothesis fails
- [ ] **Resource limit**: Ran out of time/attempts before success
- [ ] **Other**: [describe]

## Insights Gained

### About the Problem

1. [What we learned about the problem structure]
2. [What we learned about necessary conditions]
3. [What we learned about the difficulty]

### About the Technique

1. [What we learned about this proof technique]
2. [When it works / when it doesn't]
3. [How to apply it better next time]

### About Lean/Mathlib

1. [Any Mathlib gaps we discovered]
2. [Type-theoretic obstacles encountered]
3. [Useful tactics or patterns found]

## Implications for Future Work

### Approaches Now Ruled Out

- [Approach X because of reason Y]
- [Approach Z because it shares same flaw]

### Approaches Suggested

- [New direction A suggested by this failure]
- [Variation B that might avoid the issue]

### Things to Defer

- [Idea C: interesting but requires [prerequisite]]
- [Idea D: might work but not priority]

## Artifacts

### Code Preserved

```
approaches/approach-{{N}}/attempts/
├── attempt-001.lean  # [brief description]
├── attempt-002.lean  # [brief description]
└── attempt-003.lean  # [brief description]
```

### Key Code Snippets

```lean
-- The furthest we got before hitting the wall
theorem partial_result : ... := by
  ...
  -- Stuck here because: [reason]
  sorry
```

## Lessons for Knowledge Base

**Key insight to record**:

> [One-sentence insight that should be remembered for future research on this problem]

**Tags**: [technique], [failure-mode], [mathlib-gap], etc.

## Time Spent

- Research/orientation: [X hours]
- Coding attempts: [Y hours]
- Debugging: [Z hours]
- Documentation: [W hours]
- **Total**: [T hours]

## Final Assessment

**Was this attempt worthwhile?** Yes | Partially | No

**Justification**: [Why the time spent was or wasn't valuable]

**Confidence this direction is exhausted**: Low | Medium | High
